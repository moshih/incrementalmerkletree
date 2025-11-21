use ark_crypto_primitives::crh::{poseidon, CRHScheme, CRHSchemeGadget, TwoToOneCRHScheme, TwoToOneCRHSchemeGadget};
use crate::util::poseidon_hash;
use crate::util::F;
use ark_crypto_primitives::merkle_tree::{MerkleTree, Path};
use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig, PoseidonDefaultConfigEntry};
use ark_crypto_primitives::merkle_tree::{
constraints::ConfigGadget as TreeConfigGadget, Config as TreeConfig,
IdentityDigestConverter,
};
use ark_ff::{PrimeField, Zero};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use incrementalmerkletree::{Hashable, Level, Position, Retention};
use crate::complete_tree::CompleteTree;
use crate::{PHashable, Tree};

// Define all the leaf and two-to-one hashes for Poseidon
pub type LeafH = poseidon::CRH<F>;
pub type LeafHG = poseidon::constraints::CRHGadget<F>;
pub type CompressH = poseidon::TwoToOneCRH<F>;
pub type CompressHG = poseidon::constraints::TwoToOneCRHGadget<F>;

#[derive(Clone)]
pub struct PoseidonTreeConfig;

pub struct PoseidonTreeConfigVar;

pub struct TreeParams {
    pub leaf_params: PoseidonConfig<F>,
    pub two_to_one_params: PoseidonConfig<F>,
}

pub struct TreeParamsVar {
    pub leaf_params: poseidon::constraints::CRHParametersVar<F>,
    pub two_to_one_params: poseidon::constraints::CRHParametersVar<F>,
}

impl TreeParams {
    pub(crate) fn new() -> Self {
        TreeParams {
            leaf_params: gen_poseidon_params(2, false),
            two_to_one_params: gen_poseidon_params(2, false),
        }
    }

    pub(crate) fn to_var(self) -> TreeParamsVar {
        TreeParamsVar {
            leaf_params: poseidon::constraints::CRHParametersVar {
                parameters: self.leaf_params,
            },
            two_to_one_params: poseidon::constraints::CRHParametersVar {
                parameters: self.two_to_one_params,
            },
        }
    }
}

// Define the structs necessary to make a Merkle tree over the Poseidon hash

impl TreeConfig for PoseidonTreeConfig {
    type Leaf = [F];

    type LeafHash = LeafH;
    type TwoToOneHash = CompressH;

    type LeafDigest = <LeafH as CRHScheme>::Output;
    type LeafInnerDigestConverter = IdentityDigestConverter<Self::LeafDigest>;
    type InnerDigest = <CompressH as TwoToOneCRHScheme>::Output;
}

impl TreeConfigGadget<PoseidonTreeConfig, F> for PoseidonTreeConfigVar {
    type Leaf = [FpVar<F>];

    type LeafDigest = <LeafHG as CRHSchemeGadget<LeafH, F>>::OutputVar;
    type LeafInnerConverter = IdentityDigestConverter<Self::LeafDigest>;
    type InnerDigest = <CompressHG as TwoToOneCRHSchemeGadget<CompressH, F>>::OutputVar;
    type LeafHash = LeafHG;
    type TwoToOneHash = CompressHG;
}

// Generates Poseidon params for BLS12-381. This is copied from
//     https://github.com/arkworks-rs/crypto-primitives/blob/54b3ac24b8943fbd984863558c749997e96ff399/src/sponge/poseidon/traits.rs#L69
// and
//     https://github.com/arkworks-rs/crypto-primitives/blob/54b3ac24b8943fbd984863558c749997e96ff399/src/sponge/test.rs
pub(crate) fn gen_poseidon_params(rate: usize, optimized_for_weights: bool) -> PoseidonConfig<F> {
    let params_set = if !optimized_for_weights {
        [
            PoseidonDefaultConfigEntry::new(2, 17, 8, 31, 0),
            PoseidonDefaultConfigEntry::new(3, 5, 8, 56, 0),
            PoseidonDefaultConfigEntry::new(4, 5, 8, 56, 0),
            PoseidonDefaultConfigEntry::new(5, 5, 8, 57, 0),
            PoseidonDefaultConfigEntry::new(6, 5, 8, 57, 0),
            PoseidonDefaultConfigEntry::new(7, 5, 8, 57, 0),
            PoseidonDefaultConfigEntry::new(8, 5, 8, 57, 0),
        ]
    } else {
        [
            PoseidonDefaultConfigEntry::new(2, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(3, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(4, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(5, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(6, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(7, 257, 8, 13, 0),
            PoseidonDefaultConfigEntry::new(8, 257, 8, 13, 0),
        ]
    };

    for param in params_set.iter() {
        if param.rate == rate {
            let (ark, mds) = find_poseidon_ark_and_mds::<F>(
                F::MODULUS_BIT_SIZE as u64,
                rate,
                param.full_rounds as u64,
                param.partial_rounds as u64,
                param.skip_matrices as u64,
            );

            return PoseidonConfig {
                full_rounds: param.full_rounds,
                partial_rounds: param.partial_rounds,
                alpha: param.alpha as u64,
                ark,
                mds,
                rate: param.rate,
                capacity: 1,
            };
        }
    }

    panic!("could not generate poseidon params");
}

pub fn leaf_hash(input: &[F]) -> F {
    let TreeParams { leaf_params, .. } = TreeParams::new();
    poseidon::CRH::evaluate(&leaf_params, input).unwrap()
}

pub(crate) fn leaf_hash_zk(input: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
    let TreeParamsVar { leaf_params, .. } = TreeParams::new().to_var();
    poseidon::constraints::CRHGadget::evaluate(&leaf_params, input)
}

pub fn create_auth_path(
    mut rng: impl Rng,
    leaf: F,
    path_len: usize,
) -> (F, Path<PoseidonTreeConfig>) {
    let mut auth_path: Vec<F> = Vec::new();

    // Creating a random list of elements
    for i in 0..path_len {
        auth_path.push(F::rand(&mut rng));
    }

    let path_proof: Path<PoseidonTreeConfig> = Path {
        leaf_sibling_hash: F::rand(&mut rng),
        auth_path,
        leaf_index: 0,
    };

    let tree_params = TreeParams::new();
    let claimed_leaf_hash =
        <PoseidonTreeConfig as ark_crypto_primitives::merkle_tree::Config>::LeafHash::evaluate(
            &tree_params.leaf_params,
            [leaf],
        )
            .unwrap();

    let mut curr_path_node =
        <PoseidonTreeConfig as ark_crypto_primitives::merkle_tree::Config>::TwoToOneHash::evaluate(
            &tree_params.two_to_one_params,
            &claimed_leaf_hash,
            &path_proof.leaf_sibling_hash,
        )
            .unwrap();

    for iter in (0..path_len).rev() {
        curr_path_node = <PoseidonTreeConfig as ark_crypto_primitives::merkle_tree::Config>::TwoToOneHash::evaluate(
            &tree_params.two_to_one_params,
            &curr_path_node,
            &path_proof.auth_path[iter],
        ).unwrap();
    }

    (curr_path_node, path_proof)
}

pub fn create_auth_path_inc(inc_path: Vec<PHashable>, index: usize) -> Path<PoseidonTreeConfig> {
    let mut f_path = Vec::new();
    for i in 1..inc_path.len() {
        f_path.push(inc_path[i].0);
    }
    f_path.reverse();

    Path {
        leaf_sibling_hash: inc_path[0].0,
        auth_path: f_path,
        leaf_index: index,
    }
}

