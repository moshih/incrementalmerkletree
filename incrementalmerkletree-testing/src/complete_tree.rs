//! Sample implementation of the Tree interface.
use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io;
use std::io::{Read, Write};
use crate::Tree;
use incrementalmerkletree::{Hashable, Level, Marking, Position, Retention};
use serde::{Serialize, Deserialize};
use bincode;

const MAX_COMPLETE_SIZE_ERROR: &str = "Positions of a `CompleteTree` must fit into the platform word size, because larger complete trees are not representable.";

pub(crate) fn root<H: Hashable + Clone>(leaves: &[H], depth: u8) -> H {
    let empty_leaf = H::empty_leaf();
    let mut leaves = leaves
        .iter()
        .chain(std::iter::repeat(&empty_leaf))
        .take(1 << depth)
        .cloned()
        .collect::<Vec<H>>();

    //leaves are always at level zero, so we start there.
    let mut level = Level::from(0);
    while leaves.len() != 1 {
        leaves = leaves
            .iter()
            .enumerate()
            .filter(|(i, _)| (i % 2) == 0)
            .map(|(_, a)| a)
            .zip(
                leaves
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| (i % 2) == 1)
                    .map(|(_, b)| b),
            )
            .map(|(a, b)| H::combine(level, a, b))
            .collect();
        level = level + 1;
    }

    leaves[0].clone()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Checkpoint {
    /// The number of leaves in the tree when the checkpoint was created.
    leaves_len: usize,
    /// A set of the positions that have been marked during the period that this
    /// checkpoint is the current checkpoint.
    marked: BTreeSet<Position>,
    /// When a mark is forgotten, we add it to the checkpoint's forgotten set but
    /// don't immediately remove it from the `marked` set; that removal occurs when
    /// the checkpoint is eventually dropped.
    forgotten: BTreeSet<Position>,
}

impl Checkpoint {
    fn at_length(leaves_len: usize) -> Self {
        Checkpoint {
            leaves_len,
            marked: BTreeSet::new(),
            forgotten: BTreeSet::new(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CompleteTree<H, C: Ord, const DEPTH: u8>
{
    leaves: Vec<Option<H>>,
    marks: BTreeSet<Position>,
    checkpoints: BTreeMap<C, Checkpoint>,
    max_checkpoints: usize,
}

impl<H: Hashable, C: Clone + Ord + core::fmt::Debug, const DEPTH: u8> CompleteTree<H, C, DEPTH> {
    /// Creates a new, empty binary tree
    pub fn new(max_checkpoints: usize) -> Self {
        Self {
            leaves: vec![],
            marks: BTreeSet::new(),
            checkpoints: BTreeMap::new(),
            max_checkpoints,
        }
    }

    /// Appends a new value to the tree at the next available slot.
    ///
    /// Returns true if successful and false if the tree is full or, for values with `Checkpoint`
    /// retention, if a checkpoint id would be introduced that is less than or equal to the current
    /// maximum checkpoint id.
    fn append(&mut self, value: H, retention: Retention<C>) -> Result<(), AppendError<C>> {
        fn append<H, C>(
            leaves: &mut Vec<Option<H>>,
            value: H,
            depth: u8,
        ) -> Result<(), AppendError<C>> {
            if leaves.len() < (1 << depth) {
                leaves.push(Some(value));
                Ok(())
            } else {
                Err(AppendError::TreeFull)
            }
        }

        match retention {
            Retention::Marked => {
                append(&mut self.leaves, value, DEPTH)?;
                self.mark();
            }
            Retention::Checkpoint { id, marking } => {
                let latest_checkpoint = self.checkpoints.keys().next_back();
                if Some(&id) > latest_checkpoint {
                    append(&mut self.leaves, value, DEPTH)?;
                    if marking == Marking::Marked {
                        self.mark();
                    }
                    self.checkpoint(id, self.current_position());
                } else {
                    return Err(AppendError::CheckpointOutOfOrder {
                        current_max: latest_checkpoint.cloned(),
                        checkpoint: id,
                    });
                }
            }
            Retention::Ephemeral | Retention::Reference => {
                append(&mut self.leaves, value, DEPTH)?;
            }
        }

        Ok(())
    }

    pub(crate) fn current_position(&self) -> Option<Position> {
        if self.leaves.is_empty() {
            None
        } else {
            // this unwrap is safe because nobody is ever going to create a complete
            // tree with more than 2^64 leaves
            Some((self.leaves.len() - 1).try_into().unwrap())
        }
    }

    /// Marks the current tree state leaf as a value that we're interested in
    /// marking. Returns the current position if the tree is non-empty.
    fn mark(&mut self) -> Option<Position> {
        if let Some(pos) = self.current_position() {
            if !self.marks.contains(&pos) {
                self.marks.insert(pos);

                if let Some(checkpoint) = self.checkpoints.values_mut().next_back() {
                    checkpoint.marked.insert(pos);
                }
            }

            Some(pos)
        } else {
            None
        }
    }

    // Creates a new checkpoint with the specified identifier and the given tree position; if `pos`
    // is not provided, the position of the most recently appended leaf is used, or a new
    // checkpoint of the empty tree is added if appropriate.
    fn checkpoint(&mut self, id: C, pos: Option<Position>) {
        self.checkpoints.insert(
            id,
            Checkpoint::at_length(pos.map_or_else(
                || self.leaves.len(),
                |p| usize::try_from(p).expect(MAX_COMPLETE_SIZE_ERROR) + 1,
            )),
        );
        if self.checkpoints.len() > self.max_checkpoints {
            self.drop_oldest_checkpoint();
        }
    }

    fn leaves_at_checkpoint_depth(&self, checkpoint_depth: usize) -> Option<usize> {
        self.checkpoints
            .iter()
            .rev()
            .skip(checkpoint_depth)
            .map(|(_, c)| c.leaves_len)
            .next()
    }

    /// Removes the oldest checkpoint. Returns true if successful and false if
    /// there are fewer than `self.max_checkpoints` checkpoints.
    fn drop_oldest_checkpoint(&mut self) -> bool {
        if self.checkpoints.len() > self.max_checkpoints {
            let (id, c) = self.checkpoints.iter().next().unwrap();
            for pos in c.forgotten.iter() {
                self.marks.remove(pos);
            }
            let id = id.clone(); // needed to avoid mutable/immutable borrow conflict
            self.checkpoints.remove(&id);
            true
        } else {
            false
        }
    }
}

impl<H, C: Ord, const DEPTH: u8> CompleteTree<H, C, DEPTH>
where
    H: Serialize + for<'de> Deserialize<'de>,
    C: Serialize + for<'de> Deserialize<'de>,
{
    /// Serialize the tree to a JSON file
    pub fn write_to_file(&self, path: &str) -> io::Result<()> {
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        let mut file = File::create(path)?;
        file.write_all(json.as_bytes())?;
        Ok(())
    }

    /// Deserialize the tree from a JSON file
    pub fn read_from_file(path: &str) -> io::Result<Self> {
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        let tree = serde_json::from_str(&contents)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        Ok(tree)
    }

    /// Serialize the tree to a binary file (more efficient)
    pub fn write_to_file_binary(&self, path: &str) -> io::Result<()> {
        let encoded = bincode::serialize(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        let mut file = File::create(path)?;
        file.write_all(&encoded)?;
        Ok(())
    }

    /// Deserialize the tree from a binary file
    pub fn read_from_file_binary(path: &str) -> io::Result<Self> {
        let mut file = File::open(path)?;
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        let tree = bincode::deserialize(&buffer)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        Ok(tree)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AppendError<C> {
    TreeFull,
    CheckpointOutOfOrder {
        current_max: Option<C>,
        checkpoint: C,
    },
}

impl<H: Hashable + PartialEq + Clone, C: Ord + Clone + core::fmt::Debug, const DEPTH: u8> Tree<H, C>
    for CompleteTree<H, C, DEPTH>
{
    fn depth(&self) -> u8 {
        DEPTH
    }

    fn append(&mut self, value: H, retention: Retention<C>) -> bool {
        Self::append(self, value, retention).is_ok()
    }

    fn current_position(&self) -> Option<Position> {
        Self::current_position(self)
    }

    fn marked_positions(&self) -> BTreeSet<Position> {
        self.marks.clone()
    }

    fn get_marked_leaf(&self, position: Position) -> Option<H> {
        if self.marks.contains(&position) {
            self.leaves
                .get(usize::try_from(position).expect(MAX_COMPLETE_SIZE_ERROR))
                .and_then(|opt: &Option<H>| opt.clone())
        } else {
            None
        }
    }

    fn root(&self, checkpoint_depth: Option<usize>) -> Option<H> {
        checkpoint_depth.map_or_else(
            || root(&self.leaves[..], DEPTH),
            |depth| {
                self.leaves_at_checkpoint_depth(depth)
                    .and_then(|len| root(&self.leaves[0..len], DEPTH))
            },
        )
    }

    fn witness(&self, position: Position, checkpoint_depth: usize) -> Option<Vec<H>> {
        if self.marks.contains(&position) {
            let leaves_len = self.leaves_at_checkpoint_depth(checkpoint_depth)?;
            if u64::from(position) >= u64::try_from(leaves_len).unwrap() {
                // The requested position was marked after the checkpoint was created, so we
                // cannot create a witness.
                None
            } else {
                let mut path = vec![];

                let mut leaf_idx: usize = position.try_into().expect(MAX_COMPLETE_SIZE_ERROR);
                for bit in 0..DEPTH {
                    leaf_idx ^= 1 << bit;
                    path.push(if leaf_idx < leaves_len {
                        let subtree_end = min(leaf_idx + (1 << bit), leaves_len);
                        root(&self.leaves[leaf_idx..subtree_end], bit)?
                    } else {
                        H::empty_root(Level::from(bit))
                    });
                    leaf_idx &= usize::MAX << (bit + 1);
                }

                Some(path)
            }
        } else {
            None
        }
    }

    fn remove_mark(&mut self, position: Position) -> bool {
        if self.marks.contains(&position) {
            if let Some(c) = self.checkpoints.values_mut().next_back() {
                c.forgotten.insert(position);
            } else {
                self.marks.remove(&position);
            }
            true
        } else {
            false
        }
    }

    fn checkpoint(&mut self, id: C) -> bool {
        if Some(&id) > self.checkpoints.keys().next_back() {
            Self::checkpoint(self, id, self.current_position());
            true
        } else {
            false
        }
    }

    fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    fn rewind(&mut self, depth: usize) -> bool {
        if self.checkpoints.len() > depth {
            let mut to_delete = vec![];
            for (idx, (id, c)) in self
                .checkpoints
                .iter_mut()
                .rev()
                .enumerate()
                .take(depth + 1)
            {
                for pos in c.marked.iter() {
                    self.marks.remove(pos);
                }
                if idx < depth {
                    to_delete.push(id.clone());
                } else {
                    self.leaves.truncate(c.leaves_len);
                    c.marked.clear();
                    c.forgotten.clear();
                }
            }
            for cid in to_delete.iter() {
                self.checkpoints.remove(cid);
            }

            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::CompleteTree;
    use crate::{
        check_append, check_checkpoint_rewind, check_rewind_remove_mark, check_root_hashes,
        check_witnesses, compute_root_from_witness, PHashable, SipHashable, Tree, F,
    };
    use ark_ff::Zero;
    use incrementalmerkletree::{Hashable, Level, Position, Retention};
    use std::convert::TryFrom;

    #[test]
    fn correct_empty_root() {
        const DEPTH: u8 = 5;
        let mut expected = SipHashable(0u64);
        for lvl in 0u8..DEPTH {
            expected = SipHashable::combine(lvl.into(), &expected, &expected);
        }

        let tree = CompleteTree::<SipHashable, (), DEPTH>::new(100);
        assert_eq!(tree.root(None), Some(expected));
    }

    #[test]
    fn correct_empty_root_f() {
        const DEPTH: u8 = 5;
        let mut expected = PHashable(F::zero());
        for lvl in 0u8..DEPTH {
            expected = PHashable::combine(lvl.into(), &expected, &expected);
        }

        let tree = CompleteTree::<PHashable, (), DEPTH>::new(100);
        assert_eq!(tree.root(None), Some(expected));
    }

    #[test]
    fn correct_root() {
        const DEPTH: u8 = 3;
        let values = (0..(1 << DEPTH)).map(SipHashable);

        let mut tree = CompleteTree::<SipHashable, (), DEPTH>::new(100);
        for value in values {
            assert!(tree.append(value, Retention::Ephemeral).is_ok());
        }
        assert!(tree.append(SipHashable(0), Retention::Ephemeral).is_err());

        let expected = SipHashable::combine(
            Level::from(2),
            &SipHashable::combine(
                Level::from(1),
                &SipHashable::combine(Level::from(1), &SipHashable(0), &SipHashable(1)),
                &SipHashable::combine(Level::from(1), &SipHashable(2), &SipHashable(3)),
            ),
            &SipHashable::combine(
                Level::from(1),
                &SipHashable::combine(Level::from(1), &SipHashable(4), &SipHashable(5)),
                &SipHashable::combine(Level::from(1), &SipHashable(6), &SipHashable(7)),
            ),
        );

        assert_eq!(tree.root(None), Some(expected));
    }

    #[test]
    fn append() {
        check_append(CompleteTree::<String, usize, 4>::new);
    }

    #[test]
    fn root_hashes() {
        check_root_hashes(CompleteTree::<String, usize, 4>::new);
    }

    #[test]
    fn witnesses() {
        check_witnesses(CompleteTree::<String, usize, 4>::new);
    }

    #[test]
    fn correct_witness() {
        use crate::Tree;
        use incrementalmerkletree::Retention;

        const DEPTH: u8 = 3;
        let values = (0..(1 << DEPTH)).map(SipHashable);

        let mut tree = CompleteTree::<SipHashable, (), DEPTH>::new(100);
        for value in values {
            assert!(Tree::append(&mut tree, value, Retention::Marked));
        }
        assert!(tree.append(SipHashable(0), Retention::Ephemeral).is_err());

        let expected = SipHashable::combine(
            <Level>::from(2),
            &SipHashable::combine(
                Level::from(1),
                &SipHashable::combine(Level::from(1), &SipHashable(0), &SipHashable(1)),
                &SipHashable::combine(Level::from(1), &SipHashable(2), &SipHashable(3)),
            ),
            &SipHashable::combine(
                Level::from(1),
                &SipHashable::combine(Level::from(1), &SipHashable(4), &SipHashable(5)),
                &SipHashable::combine(Level::from(1), &SipHashable(6), &SipHashable(7)),
            ),
        );

        assert_eq!(tree.root(None), Some(expected.clone()));
        tree.checkpoint((), None);
        assert_eq!(tree.root(Some(0)), Some(expected.clone()));

        for i in 0u64..(1 << DEPTH) {
            let position = Position::from(i);
            let path = tree.witness(position, 0).unwrap();
            assert_eq!(
                compute_root_from_witness(SipHashable(i), position, &path),
                expected
            );
        }
    }

    #[test]
    fn checkpoint_rewind() {
        check_checkpoint_rewind(|max_checkpoints| {
            CompleteTree::<String, usize, 4>::new(max_checkpoints)
        });
    }

    #[test]
    fn rewind_remove_mark() {
        check_rewind_remove_mark(|max_checkpoints| {
            CompleteTree::<String, usize, 4>::new(max_checkpoints)
        });
    }

    #[test]
    fn test_write_and_read_json_empty_tree() {
        const DEPTH: u8 = 4;
        let tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        let path = "test_empty_tree.json";
        tree.write_to_file(path).expect("Failed to write to file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file(path)
            .expect("Failed to read from file");

        assert_eq!(tree.current_position(), loaded_tree.current_position());
        assert_eq!(tree.marked_positions(), loaded_tree.marked_positions());
        assert_eq!(tree.checkpoint_count(), loaded_tree.checkpoint_count());

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_write_and_read_json_with_data() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        // Add some values
        for i in 0..8 {
            assert!(tree.append(SipHashable(i), Retention::Marked).is_ok());
        }

        // Create checkpoints
        tree.checkpoint(1, Some(Position::from(2)));
        tree.checkpoint(2, Some(Position::from(5)));

        let original_root = tree.root(None);
        let original_positions = tree.marked_positions();

        let path = "test_tree_with_data.json";
        tree.write_to_file(path).expect("Failed to write to file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file(path)
            .expect("Failed to read from file");

        // Verify tree state is preserved
        assert_eq!(original_root, loaded_tree.root(None));
        assert_eq!(original_positions, loaded_tree.marked_positions());
        assert_eq!(tree.current_position(), loaded_tree.current_position());
        assert_eq!(tree.checkpoint_count(), loaded_tree.checkpoint_count());

        // Verify we can get marked leaves
        for i in 0..8 {
            let pos = Position::from(i);
            assert_eq!(tree.get_marked_leaf(pos), loaded_tree.get_marked_leaf(pos));
        }

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_write_and_read_json_with_checkpoints() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(10);

        // Add values with different retention types
        for i in 0..5 {
            let retention = if i % 2 == 0 {
                Retention::Marked
            } else {
                Retention::Ephemeral
            };
            assert!(tree.append(SipHashable(i), retention).is_ok());
        }

        // Create multiple checkpoints
        for checkpoint_id in 0..3 {
            tree.checkpoint(checkpoint_id, tree.current_position());
        }

        let path = "test_tree_checkpoints.json";
        tree.write_to_file(path).expect("Failed to write to file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file(path)
            .expect("Failed to read from file");

        // Verify checkpoint roots
        for depth in 0..3 {
            assert_eq!(tree.root(Some(depth)), loaded_tree.root(Some(depth)));
        }

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_write_and_read_binary_empty_tree() {
        const DEPTH: u8 = 4;
        let tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        let path = "test_empty_tree.bin";
        tree.write_to_file_binary(path).expect("Failed to write binary file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file_binary(path)
            .expect("Failed to read binary file");

        assert_eq!(tree.current_position(), loaded_tree.current_position());
        assert_eq!(tree.marked_positions(), loaded_tree.marked_positions());
        assert_eq!(tree.checkpoint_count(), loaded_tree.checkpoint_count());

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_write_and_read_binary_with_data() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        // Add some values
        for i in 0..10 {
            assert!(tree.append(SipHashable(i), Retention::Marked).is_ok());
        }

        // Create checkpoints
        tree.checkpoint(1, Some(Position::from(3)));
        tree.checkpoint(2, Some(Position::from(7)));

        let original_root = tree.root(None);
        let original_positions = tree.marked_positions();

        let path = "test_tree_with_data.bin";
        tree.write_to_file_binary(path).expect("Failed to write binary file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file_binary(path)
            .expect("Failed to read binary file");

        // Verify tree state is preserved
        assert_eq!(original_root, loaded_tree.root(None));
        assert_eq!(original_positions, loaded_tree.marked_positions());
        assert_eq!(tree.current_position(), loaded_tree.current_position());
        assert_eq!(tree.checkpoint_count(), loaded_tree.checkpoint_count());

        // Verify we can get marked leaves
        for i in 0..10 {
            let pos = Position::from(i);
            assert_eq!(tree.get_marked_leaf(pos), loaded_tree.get_marked_leaf(pos));
        }

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_write_and_read_binary_with_witnesses() {
        const DEPTH: u8 = 3;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        // Add marked values
        for i in 0..(1 << DEPTH) {
            assert!(tree.append(SipHashable(i), Retention::Marked).is_ok());
        }

        tree.checkpoint(0, None);

        let path = "test_tree_witnesses.bin";
        tree.write_to_file_binary(path).expect("Failed to write binary file");

        let loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file_binary(path)
            .expect("Failed to read binary file");

        // Verify witnesses are the same
        for i in 0u64..(1 << DEPTH) {
            let position = Position::from(i);
            let original_witness = tree.witness(position, 0);
            let loaded_witness = loaded_tree.witness(position, 0);
            assert_eq!(original_witness, loaded_witness);
        }

        // Cleanup
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn test_roundtrip_json_and_binary_equivalence() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(50);

        // Build a complex tree
        for i in 0..12 {
            let retention = match i % 3 {
                0 => Retention::Marked,
                1 => Retention::Ephemeral,
                _ => Retention::Reference,
            };
            assert!(tree.append(SipHashable(i), retention).is_ok());
        }

        for checkpoint_id in 0..5 {
            tree.checkpoint(checkpoint_id, tree.current_position());
        }

        let json_path = "test_roundtrip.json";
        let binary_path = "test_roundtrip.bin";

        tree.write_to_file(json_path).expect("Failed to write JSON file");
        tree.write_to_file_binary(binary_path).expect("Failed to write binary file");

        let tree_from_json = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file(json_path)
            .expect("Failed to read JSON file");
        let tree_from_binary = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file_binary(binary_path)
            .expect("Failed to read binary file");

        // Both should produce the same tree
        assert_eq!(tree_from_json.root(None), tree_from_binary.root(None));
        assert_eq!(tree_from_json.marked_positions(), tree_from_binary.marked_positions());
        assert_eq!(tree_from_json.current_position(), tree_from_binary.current_position());
        assert_eq!(tree_from_json.checkpoint_count(), tree_from_binary.checkpoint_count());

        // Cleanup
        std::fs::remove_file(json_path).ok();
        std::fs::remove_file(binary_path).ok();
    }

    #[test]
    fn test_serialization_with_string_type() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<String, usize, DEPTH>::new(100);

        // Add string values
        for i in 0..5 {
            tree.append(format!("value_{}", i), Retention::Marked);
        }

        tree.checkpoint(1, tree.current_position());

        let json_path = "test_string_tree.json";
        tree.write_to_file(json_path).expect("Failed to write JSON file");

        let loaded_tree = CompleteTree::<String, usize, DEPTH>::read_from_file(json_path)
            .expect("Failed to read JSON file");

        // Verify string values are preserved
        for i in 0..5 {
            let pos = Position::from(i as u64);
            assert_eq!(tree.get_marked_leaf(pos), loaded_tree.get_marked_leaf(pos));
        }

        // Cleanup
        std::fs::remove_file(json_path).ok();
    }

    #[test]
    fn test_serialization_preserves_tree_operations() {
        const DEPTH: u8 = 4;
        let mut tree = CompleteTree::<SipHashable, usize, DEPTH>::new(100);

        // Build tree with operations
        for i in 0..6 {
            tree.append(SipHashable(i), Retention::Marked);
        }
        tree.checkpoint(1, tree.current_position());

        // Serialize
        let path = "test_operations.json";
        tree.write_to_file(path).expect("Failed to write file");

        // Load and continue operations
        let mut loaded_tree = CompleteTree::<SipHashable, usize, DEPTH>::read_from_file(path)
            .expect("Failed to read file");

        // Add more values to loaded tree
        for i in 6..10 {
            assert!(loaded_tree.append(SipHashable(i), Retention::Marked).is_ok());
        }
        loaded_tree.checkpoint(2, loaded_tree.current_position());

        // Original tree should have different state
        assert_ne!(tree.current_position(), loaded_tree.current_position());

        // But should be able to operate on both independently
        assert!(tree.append(SipHashable(100), Retention::Ephemeral).is_ok());
        assert!(loaded_tree.append(SipHashable(200), Retention::Ephemeral).is_ok());

        // Cleanup
        std::fs::remove_file(path).ok();
    }
}
