use crate::complete_tree::CompleteTree;
use crate::tree_util::{create_auth_path_inc, PoseidonTreeConfig, PoseidonTreeConfigVar};
use crate::util::poseidon_hash;
use crate::{PHashable, Tree};
use ark_crypto_primitives::merkle_tree::constraints::PathVar;
use ark_crypto_primitives::merkle_tree::Path;
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use incrementalmerkletree::Position;
use incrementalmerkletree::Retention;
use serde::{Deserialize, Serialize};

/// The root of an integer tree
pub type IntTreeRoot<F: PrimeField + Absorb> = F;

/// The authentication path in an integer tree
pub type IntTreePath<F: PrimeField + Absorb> = Path<PoseidonTreeConfig<F>>;

/// The root of an integer tree
pub type IntTreeRootVar<F: PrimeField + Absorb> = FpVar<F>;

/// The ZK version of an authentication path in an integer tree
pub type IntTreePathVar<F: PrimeField + Absorb> =
    PathVar<PoseidonTreeConfig<F>, F, PoseidonTreeConfigVar>;

/// A Merkle tree that represents a set of integers, represented as field elements
#[derive(Clone, Serialize, Deserialize)]
pub struct IncIntTree<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> {
    pub leaves: Vec<F>,
    pub merkle_tree: CompleteTree<PHashable<F>, usize, INT_TREE_DEPTH>,
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> IncIntTree<F, INT_TREE_DEPTH> {
    pub fn current_position(&self) -> Option<Position> {
        self.merkle_tree.current_position()
    }

    /// Returns the number of leaves in this tree. This is always a power of two.
    pub(crate) fn num_leaves(&self) -> usize {
        self.leaves.len()
    }

    /// Returns the leaf at index `idx`.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub(crate) fn get_leaf(&self, idx: usize) -> F {
        *self.leaves.get(idx).unwrap()
    }

    /// Makes a Merkle tree of the given height
    pub fn blank() -> Self {
        let merkle_tree = CompleteTree::<PHashable<F>, usize, INT_TREE_DEPTH>::new(100);

        IncIntTree {
            leaves: vec![],
            merkle_tree,
        }
    }

    /// Makes a complete Merkle tree whose leaves are `ints`
    pub fn new(values: &[F]) -> Self {
        // Need to cast the ints to &[F] because that's technically the leaf type of the tree
        let leaves = values.to_vec();
        let mut merkle_tree = CompleteTree::<PHashable<F>, usize, INT_TREE_DEPTH>::new(100);

        for value in values {
            Tree::append(
                &mut merkle_tree,
                PHashable(poseidon_hash(&[*value])),
                Retention::Marked,
            );
        }

        Self {
            merkle_tree,
            leaves,
        }
    }

    /// Returns an authentication path that proves that the leaf at `idx` is in the current tree.
    /// **Panics:** if `idx >= self.num_leaves()`.
    pub fn auth_path(&self, idx: usize) -> IntTreePath<F> {
        let position = Position::try_from(idx).unwrap();
        let path: Vec<PHashable<F>> = self.merkle_tree.witness(position, 0).unwrap();
        create_auth_path_inc(path, idx)
    }

    /// Returns the root.
    pub fn get_root(&self) -> F {
        self.merkle_tree.root(None).unwrap().0
    }

    /// Returns the index of the first leaf that matches the query.
    /// If none are found, output 0.
    pub fn get_leaf_index(&self, leaf: F) -> usize {
        let mut index = 0;

        for (idx_i, leaf_i) in self.leaves.iter().enumerate() {
            if leaf.eq(&leaf_i) {
                index = idx_i;
                break;
            }
        }

        return index;
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

    pub fn append(&mut self, value: F) {
        self.leaves.push(value);

        assert!(Tree::append(
            &mut self.merkle_tree,
            PHashable(poseidon_hash(&[value])),
            Retention::Marked,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use crate::int_tree::IntTree;
    use crate::tree_util::{PoseidonTreeConfig, TreeParams};
    use ark_crypto_primitives::merkle_tree::Path;
    use ark_ff::One;
    use incrementalmerkletree::{Position, Retention};
    //use incrementalmerkletree_testing::complete_tree::CompleteTree;
    //use incrementalmerkletree_testing::{compute_root_from_witness, PHashable, SipHashable, Tree};
    use crate::compute_root_from_witness;
    use ark_bn254::Fr as F;

    #[test]
    fn inc_int_tree_correct_empty_root_f() {
        const DEPTH: u8 = 5;
        const DEPTH_TO_ADD: u8 = DEPTH - 2;

        //let mut tree = CompleteTree::<PHashable, (), DEPTH>::new(100);
        let mut inc_int_tree = IncIntTree::<F, DEPTH>::new(&[]);

        let pre_root_hash = inc_int_tree.merkle_tree.root(None).unwrap().0.clone();
        println!("pre_root_hash is {:?}", pre_root_hash);

        for value in 0..(1 << DEPTH_TO_ADD) {
            inc_int_tree.append(F::from(value as u64));
            /*
            assert!(Tree::append(
                &mut inc_int_tree,
                PHashable(poseidon_hash(&[F::from(value as u64)])),
                Retention::Marked
            ));

             */
        }

        let root_hash = inc_int_tree.get_root();
        println!("root_hash is {:?}", root_hash);
        //inc_int_tree.checkpoint(());
        inc_int_tree.merkle_tree.checkpoint(0);

        for i in 0u64..(1 << DEPTH_TO_ADD) {
            let position = Position::try_from(i).unwrap();
            let path: Vec<PHashable<F>> = inc_int_tree.merkle_tree.witness(position, 0).unwrap();

            assert_eq!(
                compute_root_from_witness(PHashable(poseidon_hash(&[F::from(i)])), position, &path),
                inc_int_tree.merkle_tree.root(None).unwrap()
            );

            let mut f_path = Vec::new();
            for i in 1..path.len() {
                f_path.push(path[i].0);
            }
            f_path.reverse();

            let path_proof: Path<PoseidonTreeConfig<F>> = Path {
                leaf_sibling_hash: path[0].0,
                auth_path: f_path,
                leaf_index: i as usize,
            };

            let TreeParams {
                leaf_params,
                two_to_one_params,
            } = TreeParams::new();

            let root_hash = inc_int_tree.merkle_tree.root(None).unwrap().0.clone();
            assert_eq!(
                path_proof
                    .verify(&leaf_params, &two_to_one_params, &root_hash, [F::from(i)])
                    .unwrap(),
                true
            );

            let path_proof_from_func = create_auth_path_inc(path, i as usize);
            assert_eq!(
                path_proof_from_func
                    .verify(&leaf_params, &two_to_one_params, &root_hash, [F::from(i)])
                    .unwrap(),
                true
            );
        }
    }
}
