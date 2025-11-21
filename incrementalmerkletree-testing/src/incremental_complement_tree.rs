use std::ops::Add;
use ark_crypto_primitives::merkle_tree::constraints::PathVar;
use ark_crypto_primitives::merkle_tree::Path;
use ark_ff::{One, Zero};
use ark_r1cs_std::fields::fp::FpVar;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use incrementalmerkletree::{Position, Retention};
use crate::complete_tree::CompleteTree;
use crate::incremental_int_tree::IncIntTree;
use crate::{PHashable, Tree};
use crate::tree_util::{create_auth_path_inc, PoseidonTreeConfig, PoseidonTreeConfigVar, TreeParams};
use crate::util::{poseidon_hash, F};

/// Represents the semi-open range `[a, b)`.
pub type FpRange = (F, F);
/// The leaf of a range tree. This is just an `FpRange`, i.e., a semi-open range `[a, b)`.
pub type RangeTreeLeaf = FpRange;

/// The root of a range tree
pub type RangeTreeRoot = F;

/// An authentication path representing the membership of a given range in the range tree
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RangeTreePath {
    pub leaf: RangeTreeLeaf,
    pub path: Path<PoseidonTreeConfig>,
}

// Now the ZK definitions

pub type RangeTreeLeafVar = (FpVar<F>, FpVar<F>);

pub type RangeTreeRootVar = FpVar<F>;

pub struct RangeTreePathVar {
    pub(crate) leaf: RangeTreeLeafVar,
    pub(crate) path: PathVar<PoseidonTreeConfig, F, PoseidonTreeConfigVar>,
}
#[derive(Clone)]
pub struct IncRangeTree<const INT_TREE_DEPTH: u8> {
    pub leaves: Vec<RangeTreeLeaf>,
    pub merkle_tree: CompleteTree<PHashable, usize, INT_TREE_DEPTH>,
}

impl<const INT_TREE_DEPTH: u8> IncRangeTree<INT_TREE_DEPTH> {
    pub fn current_position(&self) -> Option<Position> {
        self.merkle_tree.current_position()
    }

    /// Returns the number of leaves in this tree. This is always a power of two.
    fn num_leaves(&self) -> usize {
        self.leaves.len()
    }

    /// Returns the leaf at index `idx`.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub(crate) fn get_leaf(&self, idx: usize) -> RangeTreeLeaf {
        *self.leaves.get(idx).unwrap()
    }

    /// Makes a Merkle tree of the given height, where all the leaves are the empty interval
    /// `[0, 0)`.
    pub fn blank() -> Self {
        let merkle_tree = CompleteTree::<PHashable, usize, INT_TREE_DEPTH>::new(100);

        IncRangeTree {
            leaves: vec![],
            merkle_tree,
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
        let mut leaves = complement_ranges(fps);

        // Compute the hashes and make a new tree

        let mut merkle_tree = CompleteTree::<PHashable, usize, INT_TREE_DEPTH>::new(100);

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
    pub fn auth_path(&self, idx: usize) -> RangeTreePath {
        let position = Position::try_from(idx).unwrap();
        let inc_path: Vec<PHashable> = self.merkle_tree.witness(position, 0).unwrap();
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

    pub fn append(&mut self, value: RangeTreeLeaf) {
        self.leaves.push(value);

        Tree::append(
            &mut self.merkle_tree,
            PHashable(poseidon_hash(&[value.0, value.1])),
            Retention::Marked,
        );
    }
}

/// Given a set of field elements, produces a set of semi-open ranges [a, b) representing the complement of the set provided
pub fn complement_ranges(mut fps: Vec<F>) -> Vec<FpRange> {
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
