use crate::complete_tree::CompleteTree;
use crate::incremental_int_tree::IncIntTree;
use crate::tree_util::{
    create_auth_path_inc, leaf_hash, leaf_hash_zk, PoseidonTreeConfig, PoseidonTreeConfigVar,
    TreeParams,
};
use crate::util::poseidon_hash;
use crate::{PHashable, Tree};
use ark_crypto_primitives::merkle_tree::constraints::PathVar;
use ark_crypto_primitives::merkle_tree::{MerkleTree, Path};
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{One, PrimeField, Zero};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::ns;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Valid, Write,
};
use incrementalmerkletree::{Position, Retention};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::Add;

/// Represents the semi-open range `[a, b)`.
pub type FpRange<F: PrimeField + Absorb> = (F, F);
/// The leaf of a range tree. This is just an `FpRange`, i.e., a semi-open range `[a, b)`.
pub type RangeTreeLeaf<F: PrimeField + Absorb> = FpRange<F>;

/// The root of a range tree
pub type RangeTreeRoot<F: PrimeField + Absorb> = F;

/// An authentication path representing the membership of a given range in the range tree
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RangeTreePath<F: PrimeField + Absorb> {
    pub leaf: RangeTreeLeaf<F>,
    pub path: Path<PoseidonTreeConfig<F>>,
}

// Now the ZK definitions

pub type RangeTreeLeafVar<F: PrimeField + Absorb> = (FpVar<F>, FpVar<F>);

pub type RangeTreeRootVar<F: PrimeField + Absorb> = FpVar<F>;

#[derive(Clone)]
pub struct RangeTreePathVar<F: PrimeField + Absorb> {
    pub(crate) leaf: RangeTreeLeafVar<F>,
    pub(crate) path: PathVar<PoseidonTreeConfig<F>, F, PoseidonTreeConfigVar>,
}

/// The base Merkle tree impl we will use for our nullifier-complement set and credential tree
pub type PoseidonMerkleTree<F: PrimeField + Absorb> = MerkleTree<PoseidonTreeConfig<F>>;

#[derive(Clone)]
pub struct RangeTree<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> {
    pub leaves: Vec<RangeTreeLeaf<F>>,
    pub merkle_tree: PoseidonMerkleTree<F>,
    pub write_idx: usize,
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> Default for RangeTree<F, INT_TREE_DEPTH> {
    fn default() -> Self {
        RangeTree::<F, INT_TREE_DEPTH>::blank()
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> fmt::Debug for RangeTree<F, INT_TREE_DEPTH> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RangeTree")
            .field("root", &self.merkle_tree.root())
            .field("write_idx", &self.write_idx)
            .field("leaves", &self.leaves)
            .finish()
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> Valid for RangeTree<F, INT_TREE_DEPTH> {
    fn check(&self) -> Result<(), SerializationError> {
        // Validate that the leaves and write_idx are consistent
        if self.write_idx > self.leaves.len() {
            return Err(SerializationError::InvalidData);
        }
        Ok(())
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> CanonicalSerialize
    for RangeTree<F, INT_TREE_DEPTH>
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        // Serialize the leaves
        self.leaves.serialize_with_mode(&mut writer, compress)?;

        // Serialize the write_idx
        self.write_idx.serialize_with_mode(&mut writer, compress)?;

        Ok(())
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.leaves.serialized_size(compress) + self.write_idx.serialized_size(compress)
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> CanonicalDeserialize
    for RangeTree<F, INT_TREE_DEPTH>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        // Deserialize the leaves
        let leaves: Vec<RangeTreeLeaf<F>> =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;

        // Deserialize the write_idx
        let write_idx: usize =
            CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;

        // Reconstruct the Merkle tree from the leaves
        let TreeParams {
            leaf_params,
            two_to_one_params,
        } = TreeParams::new();

        let mut leaf_hashes = Vec::new();
        for entry in leaves.iter() {
            leaf_hashes.push([leaf_hash(&[entry.0, entry.1])]);
        }

        let merkle_tree = MerkleTree::new(&leaf_params, &two_to_one_params, leaf_hashes)
            .map_err(|_| SerializationError::InvalidData)?;

        let range_tree = RangeTree {
            leaves,
            merkle_tree,
            write_idx,
        };

        // Validate if required
        if validate == ark_serialize::Validate::Yes {
            range_tree.check()?;
        }

        Ok(range_tree)
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> RangeTree<F, INT_TREE_DEPTH> {
    /// Returns the number of leaves in this tree. This is always a power of two.
    fn num_leaves(&self) -> usize {
        self.leaves.len()
    }

    /// Returns the number of written leaves in this tree.
    fn num_written_leaves(&self) -> usize {
        self.write_idx
    }

    /// Returns the leaf at index `idx`.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub(crate) fn get_leaf(&self, idx: usize) -> RangeTreeLeaf<F> {
        *self.leaves.get(idx).unwrap()
    }

    /// Makes a Merkle tree of the given height, where all the leaves are the empty interval
    /// `[0, 0)`.
    pub fn blank() -> Self {
        let TreeParams {
            leaf_params,
            two_to_one_params,
        } = TreeParams::new();

        // Every leaf is all zeros
        let empty_range = (F::zero(), F::zero());

        // Make a tree with the given leaves
        let num_leaves = 1 << (INT_TREE_DEPTH - 1);
        let leaves = vec![empty_range; num_leaves];

        // Compute the hashes and make a new tree (same as new() method)
        let mut leaf_hashes = Vec::new();
        for entry in leaves.iter() {
            leaf_hashes.push([leaf_hash(&[entry.0, entry.1])]);
        }

        let merkle_tree = MerkleTree::new(&leaf_params, &two_to_one_params, leaf_hashes).unwrap();

        RangeTree {
            leaves,
            merkle_tree,
            write_idx: 0,
        }
    }

    /// Makes a complete Merkle tree which represents the COMPLEMENT of the given set of field
    /// elements
    #[allow(non_snake_case)]
    pub fn new(mut fps: Vec<F>) -> Self {
        let TreeParams {
            leaf_params,
            two_to_one_params,
        } = TreeParams::new();

        // Compute the complement set
        let mut leaves = complement_ranges(&fps);
        let write_idx = leaves.len();

        // Pad the leaves to a power of two
        let height: usize = (leaves.len() as f32).log2().ceil() as usize;
        while leaves.len() < (1 << height) {
            leaves.push((F::zero(), F::zero()));
        }

        // Compute the hashes and make a new tree
        let mut leaf_hashes = Vec::new();
        for entry in leaves.iter() {
            leaf_hashes.push([leaf_hash(&[entry.0, entry.1])]);
        }

        let merkle_tree = MerkleTree::new(&leaf_params, &two_to_one_params, leaf_hashes).unwrap();

        RangeTree {
            leaves,
            merkle_tree,
            write_idx,
        }
    }

    pub fn get_leaf_idx(&self, elem: F) -> usize {
        let mut sorted_index: usize = usize::MAX;
        for (idx, interval) in self.leaves.iter().enumerate() {
            if interval.0 <= elem && interval.1 > elem {
                sorted_index = idx;
                break;
            }
        }

        return sorted_index;
    }

    pub fn get_leaf_idx_value(&self, elem: F) -> (usize, (F, F)) {
        let mut sorted_index: usize = usize::MAX;
        let mut value = (F::zero(), F::zero());
        for (idx, interval) in self.leaves.iter().enumerate() {
            if interval.0 <= elem && interval.1 > elem {
                sorted_index = idx;
                value = interval.clone();
                break;
            }
        }

        return (sorted_index, value);
    }

    /// This function updates the ranges to remove a value
    pub fn append_value(&mut self, value: F) {
        let (idx_to_update, mut range_to_update) = self.get_leaf_idx_value(value);
        assert_ne!(idx_to_update, usize::MAX);

        // case 1: if value == range_to_update.0
        // update the range to exclude it
        if value == range_to_update.0 {
            if range_to_update.0 + F::one() != range_to_update.1 {
                range_to_update.0 = range_to_update.0 + F::one();
            } else {
                range_to_update = (F::zero(), F::zero());
            }

            self.leaves[idx_to_update] = range_to_update;

            self.update_leaf(idx_to_update, range_to_update);
        } else if value == range_to_update.1 {
            // case 2: value == range_to_update.1
            // do nothing, value already excluded
        } else {
            // case3: value is in the interval
            range_to_update.1 = value;
            self.update_leaf(idx_to_update, range_to_update);
            let new_range = (value + F::one(), range_to_update.1);
            self.update_leaf(self.write_idx, new_range);
            self.write_idx += 1;
        }
    }

    pub fn update_leaf(&mut self, idx: usize, leaf: FpRange<F>) {
        self.leaves[idx] = leaf;
        self.merkle_tree
            .update(idx, &[leaf_hash(&[leaf.0, leaf.1])])
            .unwrap();
    }

    /*
    pub fn update_leaf(&mut self, idx: usize, low: F, high: F) {
        self.leaves[idx] = (low, high);
        self.merkle_tree
            .update(idx, &[leaf_hash(&[low, high])])
            .unwrap();
    }
     */

    /// Returns an authentication path that proves that the leaf at `idx` is in the current tree.
    /// Return value includes the leaf values themselves, so they can be range-checked later.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub fn auth_path(&self, idx: usize) -> RangeTreePath<F> {
        RangeTreePath {
            leaf: self.get_leaf(idx),
            path: self.merkle_tree.generate_proof(idx).unwrap(),
        }
    }

    /// Returns the root.
    pub fn get_root(&self) -> F {
        self.merkle_tree.root()
    }
}

impl<F: PrimeField + Absorb> RangeTreePath<F> {
    /// Verifies that the given nullifier occurs in the range represented by this authentication
    /// path. This proves that `x` is not in the set of observed nullifiers.
    pub fn verify(&self, x: &F, root_hash: &RangeTreeRoot<F>) -> bool {
        // Check a <= x < b, and then do a normal path authentication
        let ge_a = {
            let eq_a = x == &self.leaf.0;
            let gt_a = x.cmp(&self.leaf.0) == Ordering::Greater;
            eq_a || gt_a
        };
        let lt_b = x.cmp(&self.leaf.1) == Ordering::Less;
        let range_verifies = ge_a && lt_b;

        let TreeParams {
            leaf_params,
            two_to_one_params,
        } = TreeParams::new();

        let range_hash = leaf_hash(&[self.leaf.0.clone(), self.leaf.1.clone()]);

        let auth_path_verifies = self
            .path
            .verify(&leaf_params, &two_to_one_params, &root_hash, [range_hash])
            .unwrap();

        range_verifies && auth_path_verifies
    }
}

impl<F: PrimeField + Absorb> RangeTreePathVar<F> {
    /// Checks whether the given nullifier occurs in the range represented by this authentication
    /// path. This proves that `x` is not in the set of observed nullifiers.
    pub(crate) fn verify(
        &self,
        x: &FpVar<F>,
        root_hash_var: &RangeTreeRootVar<F>,
    ) -> Result<Boolean<F>, SynthesisError> {
        // Check a <= x < b, and then do a normal path authentication
        let ge_a = x.is_cmp_unchecked(&self.leaf.0, Ordering::Greater, true)?;
        let lt_b = x.is_cmp_unchecked(&self.leaf.1, Ordering::Less, false)?;
        let range_verifies_var = ge_a & lt_b;

        let range_hash = leaf_hash_zk(&[self.leaf.0.clone(), self.leaf.1.clone()])?;

        let tree_params_var = TreeParams::new().to_var();
        let auth_path_verifies_var = self.path.verify_membership(
            &tree_params_var.leaf_params,
            &tree_params_var.two_to_one_params,
            &root_hash_var,
            &[range_hash],
        )?;
        Ok(range_verifies_var & auth_path_verifies_var)
    }
    pub(crate) fn is_correct_leaf(&self, x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
        // Check a <= x < b, and then do a normal path authentication
        let ge_a = x.is_cmp_unchecked(&self.leaf.0, Ordering::Greater, true)?;
        let lt_b = x.is_cmp_unchecked(&self.leaf.1, Ordering::Less, false)?;
        let range_verifies_var = ge_a & lt_b;

        Ok(range_verifies_var)
    }
}

pub fn is_correct_leaf<F: PrimeField + Absorb>(
    x: &FpVar<F>,
    leaf_low: &FpVar<F>,
    leaf_high: &FpVar<F>,
) -> Result<Boolean<F>, SynthesisError> {
    // Check a <= x < b, and then do a normal path authentication
    let ge_a = x.is_cmp_unchecked(leaf_low, Ordering::Greater, true)?;
    let lt_b = x.is_cmp_unchecked(leaf_high, Ordering::Less, false)?;
    let range_verifies_var = ge_a & lt_b;
    Ok(range_verifies_var)
}

impl<F: PrimeField + Absorb> AllocVar<RangeTreePath<F>, F> for RangeTreePathVar<F> {
    fn new_variable<T: Borrow<RangeTreePath<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let res = f();

        res.and_then(|treepath| {
            let treepath = treepath.borrow();
            let leaf_0_var =
                FpVar::new_variable(ns!(cs, "bytestring"), || Ok(treepath.leaf.0), mode)?;

            let leaf_1_var =
                FpVar::new_variable(ns!(cs, "bytestring"), || Ok(treepath.leaf.1), mode)?;

            let path_var =
                PathVar::new_variable(ns!(cs, "expiry"), || Ok(treepath.path.clone()), mode)?;

            Ok(RangeTreePathVar {
                leaf: (leaf_0_var, leaf_1_var),
                path: path_var,
            })
        })
    }
}

/// Given a set of field elements, produces a set of semi-open ranges [a, b) representing the complement of the set provided
/// (a is not in the set but b is)
pub fn complement_ranges<F: PrimeField + Absorb>(mut fps_ptr: &Vec<F>) -> Vec<FpRange<F>> {
    let mut fps = fps_ptr.clone();
    // Helpful constants
    let zero = F::zero();
    let one = F::one();
    let fmax = zero - one;

    // Base case
    if fps.len() == 0 {
        let empty_range = (zero, zero);
        return vec![empty_range];
    }

    // Sort the list
    fps.sort();

    // The interval before the first leaf
    let mut ranges = Vec::new();
    if !fps[0].is_zero() {
        ranges.push((zero, fps[0]));
    }

    // The intervals between leaves
    for (idx, _) in fps.iter().enumerate() {
        if idx == fps.len() - 1 {
            continue;
        }

        // if fps[idx] = is the same or one less than fps[idx+1]
        if fps[idx] == fps[idx + 1] || fps[idx] + one == fps[idx + 1] {
            continue;
        }

        ranges.push((fps[idx] + one, fps[idx + 1]));
    }

    // The interval after the last leaf
    if fps.last().unwrap().lt(&fmax) {
        ranges.push((fps[fps.len() - 1].add(one), fmax));
    }

    ranges
}

#[cfg(test)]
mod test {
    use super::*;

    use ark_bn254::Fr as F;
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    #[allow(non_snake_case)]
    #[test]
    fn new_nullifier_complement_tree_correctness() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 4;
        let nul_list_size = 2 << NUL_HEIGHT;
        let mut nul_list: Vec<F> = Vec::new();

        // Creating a random list of nullifiers
        for _ in 0..nul_list_size {
            nul_list.push(F::rand(&mut rng));
        }

        // Creating a sorted version
        let mut sorted_nul_list = nul_list.clone();
        sorted_nul_list.sort();

        let nul_complement_tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list);

        // Verifying that the intervals were created properly
        // there is a slight chance this will fail if random nullifiers are the same or off by one of each other

        assert_eq!(nul_complement_tree.leaves[0].0, F::zero());
        let ZERO = F::zero();
        let ONE = F::one();
        let FMAX = ZERO - ONE;

        assert_eq!(nul_complement_tree.leaves[0].1, sorted_nul_list[0]);

        for idx in 0..sorted_nul_list.len() {
            // checking the lower value of the semi-open range `[a, b)` is correct
            assert_eq!(
                nul_complement_tree.leaves[idx + 1].0,
                sorted_nul_list[idx].add(ONE)
            );

            // checking the higher value of the semi-open range `[a, b)` is correct
            assert_eq!(nul_complement_tree.leaves[idx].1, sorted_nul_list[idx]);
        }

        assert_eq!(nul_complement_tree.leaves[nul_list_size].1, FMAX);
    }

    #[test]
    fn auth_path_correctness() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 4;
        let nul_list_size = 2 << NUL_HEIGHT;
        let cs = ConstraintSystem::new_ref();

        let mut nul_list: Vec<F> = Vec::new();

        // Creating a random list of nullifiers
        for _ in 0..nul_list_size {
            nul_list.push(F::rand(&mut rng));
        }

        // Creating a sorted version
        let mut sorted_nul_list = nul_list.clone();
        sorted_nul_list.sort();

        let nul_complement_tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list);

        let root = nul_complement_tree.merkle_tree.root();
        let root_var = RangeTreeRootVar::new_witness(ns!(cs, "test_path"), || Ok(&root)).unwrap();

        for idx in 0..nul_complement_tree.leaves.len() {
            let test_path: RangeTreePath<F> = nul_complement_tree.auth_path(idx);
            let test_path_var =
                RangeTreePathVar::new_witness(ns!(cs, "test_path"), || Ok(&test_path)).unwrap();

            assert_eq!(test_path.leaf, nul_complement_tree.leaves[idx]);

            if test_path.leaf.0.add(&F::one()).le(&test_path.leaf.1) {
                let val_in_range = test_path.leaf.0.add(&F::one());
                let val_in_range_var =
                    FpVar::new_witness(ns!(cs, "val"), || Ok(&val_in_range)).unwrap();

                assert!(test_path.verify(&val_in_range, &root));
                test_path_var
                    .verify(&val_in_range_var, &root_var)
                    .unwrap()
                    .enforce_equal(&Boolean::TRUE)
                    .unwrap();
            }
        }

        assert!(cs.is_satisfied().unwrap());
    }
}

/*
impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> IncRangeTree<F, INT_TREE_DEPTH> {
    pub fn current_position(&self) -> Option<Position> {
        self.merkle_tree.current_position()
    }

    /// Returns the number of leaves in this tree. This is always a power of two.
    fn num_leaves(&self) -> usize {
        self.leaves.len()
    }

    /// Returns the leaf at index `idx`.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub(crate) fn get_leaf(&self, idx: usize) -> RangeTreeLeaf<F> {
        *self.leaves.get(idx).unwrap()
    }

    /// Makes a Merkle tree of the given height, where all the leaves are the empty interval
    /// `[0, 0)`.
    pub fn blank() -> Self {
        let merkle_tree = CompleteTree::<PHashable<F>, usize, INT_TREE_DEPTH>::new(100);

        IncRangeTree {
            leaves: vec![],
            merkle_tree,
        }
    }

    /// Makes a complete Merkle tree which represents the COMPLEMENT of the given set of field
    /// elements
    #[allow(non_snake_case)]
    pub fn new(mut fps: Vec<F>) -> Self {
        //let TreeParams = TreeParams::new();

        // Compute the complement set
        let mut leaves = complement_ranges(&fps);

        // Compute the hashes and make a new tree

        let mut merkle_tree = CompleteTree::<PHashable<F>, usize, INT_TREE_DEPTH>::new(100);

        for entry in leaves.iter() {
            Tree::append(
                &mut merkle_tree,
                PHashable(poseidon_hash(&[entry.0, entry.1])),
                Retention::Marked,
            );
        }

        IncRangeTree {
            leaves,
            merkle_tree,
        }
    }

    pub fn get_leaf_idx(&self, elem: F) -> usize {
        let mut sorted_index: usize = usize::MAX;
        for (idx, interval) in self.leaves.iter().enumerate() {
            if interval.0 <= elem && interval.1 > elem {
                sorted_index = idx;
                break;
            }
        }

        return sorted_index;
    }

    /// Returns an authentication path that proves that the leaf at `idx` is in the current tree.
    /// Return value includes the leaf values themselves, so they can be range-checked later.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub fn auth_path(&self, idx: usize) -> RangeTreePath<F> {
        let position = Position::try_from(idx).unwrap();
        let inc_path: Vec<PHashable<F>> = self.merkle_tree.witness(position, 0).unwrap();
        let path = create_auth_path_inc(inc_path, idx);
        RangeTreePath {
            leaf: self.get_leaf(idx),
            path,
        }
    }

    /// Returns the root.
    pub fn get_root(&self) -> F {
        self.merkle_tree.root(None).unwrap().0
    }

    pub fn rewind(&mut self, depth: usize) {
        self.merkle_tree.rewind(depth);

        let cur_pos = self.merkle_tree.current_position();
        if cur_pos.is_some() {
            let cur_pos_u64: u64 = cur_pos.unwrap().try_into().unwrap();
            self.leaves.truncate(cur_pos_u64 as usize);
        } else {
            self.leaves.clear();
        }
    }

    pub fn append_range(&mut self, value: RangeTreeLeaf<F>) {
        self.leaves.push(value);

        Tree::append(
            &mut self.merkle_tree,
            PHashable(poseidon_hash(&[value.0, value.1])),
            Retention::Marked,
        );
    }

    /// This function updates the ranges to remove a vlue
    pub fn append_value(&mut self, value: F) {
        let idx_to_update = self.get_leaf_idx(value);
        assert_ne!(idx_to_update, usize::MAX);
        let mut range_to_update = self.get_leaf(idx_to_update);

        // case 1: if value == range_to_update.0
        // update the range to exclude it
        if value == range_to_update.0 {
            if range_to_update.0 + F::one() != range_to_update.1 {
                range_to_update.0 = range_to_update.0 + F::one();
            } else {
                range_to_update = (F::zero(), F::zero());
            }

            self.leaves[idx_to_update] = range_to_update;

            self.merkle_tree.append()
        }

        self.leaves.push(value);

        Tree::append(
            &mut self.merkle_tree,
            PHashable(poseidon_hash(&[value.0, value.1])),
            Retention::Marked,
        );
    }
}

/// Given a set of field elements, produces a set of semi-open ranges [a, b) representing the complement of the set provided
/// (a is not in the set but b is)
pub fn complement_ranges<F: PrimeField + Absorb>(mut fps_ptr: &Vec<F>) -> Vec<FpRange<F>> {
    let mut fps = fps_ptr.clone();
    // Helpful constants
    let zero = F::zero();
    let one = F::one();
    let fmax = zero - one;

    // Base case
    if fps.len() == 0 {
        let empty_range = (zero, zero);
        return vec![empty_range];
    }

    // Sort the list
    fps.sort();

    // The interval before the first leaf
    let mut ranges = Vec::new();
    if !fps[0].is_zero() {
        ranges.push((zero, fps[0]));
    }

    // The intervals between leaves
    for (idx, _) in fps.iter().enumerate() {
        if idx == fps.len() - 1 {
            continue;
        }

        // if fps[idx] = is the same or one less than fps[idx+1]
        if fps[idx] == fps[idx + 1] || fps[idx] + one == fps[idx + 1] {
            continue;
        }

        ranges.push((fps[idx] + one, fps[idx + 1]));
    }

    // The interval after the last leaf
    if fps.last().unwrap().lt(&fmax) {
        ranges.push((fps[fps.len() - 1].add(one), fmax));
    }

    ranges
}

*/

#[cfg(test)]
mod tests {
    use super::*;
    use crate::complement_tree::complement_ranges;
    use ark_bn254::Fr as F;
    use ark_ff::Zero;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::{rand, rand::Rng, test_rng, UniformRand};

    #[test]
    fn complement_ranges_test() {
        let mut rng = rand::thread_rng();

        let mut list: Vec<F> = Vec::new();
        let num_elems = 16;
        // Creating a random list of nullifiers
        for i in 0..num_elems {
            list.push(F::rand(&mut rng));
        }
        list.sort();

        println!("list: {:?}", list);

        let complement_ranges = complement_ranges(&list);

        println!("complement_ranges: {:?}", complement_ranges);

        for i in 0..num_elems {
            if list[i] != F::zero() {
                assert_eq!(list[i], complement_ranges[i].1);
            }
        }
    }

    #[test]
    fn test_serialize_deserialize_blank_tree() {
        const NUL_HEIGHT: u8 = 4;

        // Create a blank tree
        let tree: RangeTree<F, NUL_HEIGHT> = RangeTree::blank();

        // Serialize
        let mut bytes = Vec::new();
        tree.serialize_compressed(&mut bytes).unwrap();

        // Deserialize
        let restored: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_compressed(&bytes[..]).unwrap();

        // Verify
        assert_eq!(tree.leaves, restored.leaves);
        assert_eq!(tree.write_idx, restored.write_idx);
        assert_eq!(tree.get_root(), restored.get_root());
        assert_eq!(tree.num_leaves(), restored.num_leaves());
    }

    #[test]
    fn test_serialize_deserialize_tree_with_values() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 4;
        let nul_list_size = 2 << NUL_HEIGHT;
        let mut nul_list: Vec<F> = Vec::new();

        // Create a random list of nullifiers
        for _ in 0..nul_list_size {
            nul_list.push(F::rand(&mut rng));
        }

        // Create tree
        let tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list.clone());
        let original_root = tree.get_root();
        let original_leaves = tree.leaves.clone();
        let original_write_idx = tree.write_idx;

        // Serialize
        let mut bytes = Vec::new();
        tree.serialize_compressed(&mut bytes).unwrap();

        println!("Serialized size: {} bytes", bytes.len());

        // Deserialize
        let restored: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_compressed(&bytes[..]).unwrap();

        // Verify basic properties
        assert_eq!(original_leaves, restored.leaves);
        assert_eq!(original_write_idx, restored.write_idx);
        assert_eq!(original_root, restored.get_root());
        assert_eq!(tree.num_leaves(), restored.num_leaves());
        assert_eq!(tree.num_written_leaves(), restored.num_written_leaves());
    }

    #[test]
    fn test_serialize_deserialize_auth_paths() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 4;
        let nul_list_size = 8;
        let mut nul_list: Vec<F> = Vec::new();

        // Create a smaller random list
        for _ in 0..nul_list_size {
            nul_list.push(F::rand(&mut rng));
        }

        // Create tree
        let tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list.clone());
        let original_root = tree.get_root();

        // Serialize and deserialize
        let mut bytes = Vec::new();
        tree.serialize_compressed(&mut bytes).unwrap();
        let restored: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_compressed(&bytes[..]).unwrap();

        // Test that auth paths work correctly on restored tree
        for idx in 0..tree.num_written_leaves() {
            let original_path = tree.auth_path(idx);
            let restored_path = restored.auth_path(idx);

            // Verify leaves match
            assert_eq!(original_path.leaf, restored_path.leaf);

            // Verify paths authenticate against the same root
            if original_path
                .leaf
                .0
                .add(&F::one())
                .le(&original_path.leaf.1)
            {
                let val_in_range = original_path.leaf.0.add(&F::one());

                assert!(original_path.verify(&val_in_range, &original_root));
                assert!(restored_path.verify(&val_in_range, &original_root));
            }
        }
    }

    #[test]
    fn test_serialize_deserialize_uncompressed() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 3;
        let mut nul_list: Vec<F> = vec![F::rand(&mut rng), F::rand(&mut rng), F::rand(&mut rng)];

        let tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list);
        let original_root = tree.get_root();

        // Serialize uncompressed
        let mut bytes = Vec::new();
        tree.serialize_uncompressed(&mut bytes).unwrap();

        // Deserialize uncompressed
        let restored: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_uncompressed(&bytes[..]).unwrap();

        assert_eq!(tree.leaves, restored.leaves);
        assert_eq!(tree.write_idx, restored.write_idx);
        assert_eq!(original_root, restored.get_root());
    }

    #[test]
    fn test_serialize_deserialize_with_updates() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 5;
        let mut nul_list: Vec<F> = Vec::new();

        // Create initial list
        for _ in 0..4 {
            nul_list.push(F::rand(&mut rng));
        }

        // Create and modify tree
        let mut tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list.clone());

        // Perform some updates
        let new_leaf = (F::from(100u64), F::from(200u64));
        tree.update_leaf(0, new_leaf);

        let original_root = tree.get_root();
        let original_leaves = tree.leaves.clone();

        // Serialize
        let mut bytes = Vec::new();
        tree.serialize_compressed(&mut bytes).unwrap();

        // Deserialize
        let restored: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_compressed(&bytes[..]).unwrap();

        // Verify the update persisted
        assert_eq!(original_leaves, restored.leaves);
        assert_eq!(restored.get_leaf(0), new_leaf);
        assert_eq!(original_root, restored.get_root());
    }

    #[test]
    fn test_multiple_serialize_deserialize_cycles() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 3;
        let nul_list: Vec<F> = vec![F::rand(&mut rng), F::rand(&mut rng)];

        let mut tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list);
        let original_root = tree.get_root();

        // Multiple serialization cycles
        for _ in 0..3 {
            let mut bytes = Vec::new();
            tree.serialize_compressed(&mut bytes).unwrap();
            tree = RangeTree::deserialize_compressed(&bytes[..]).unwrap();
        }

        // Root should remain unchanged
        assert_eq!(original_root, tree.get_root());
    }

    #[test]
    fn test_serialized_size() {
        let mut rng = ark_std::test_rng();
        const NUL_HEIGHT: u8 = 4;
        let nul_list: Vec<F> = vec![F::rand(&mut rng), F::rand(&mut rng), F::rand(&mut rng)];

        let tree: RangeTree<F, NUL_HEIGHT> = RangeTree::new(nul_list);

        // Check that serialized_size matches actual size
        let reported_size = tree.serialized_size(ark_serialize::Compress::Yes);

        let mut bytes = Vec::new();
        tree.serialize_compressed(&mut bytes).unwrap();
        let actual_size = bytes.len();

        assert_eq!(reported_size, actual_size);
    }

    #[test]
    #[should_panic]
    fn test_deserialize_invalid_data() {
        const NUL_HEIGHT: u8 = 4;

        // Try to deserialize garbage data
        let invalid_bytes = vec![0u8; 10];
        let _: RangeTree<F, NUL_HEIGHT> =
            RangeTree::deserialize_compressed(&invalid_bytes[..]).unwrap();
    }
}
