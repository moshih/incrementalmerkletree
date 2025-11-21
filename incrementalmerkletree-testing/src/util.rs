use std::borrow::Borrow;
use std::cmp::Ordering;
pub use ark_bn254::Fr as F;
use ark_crypto_primitives::crh::{poseidon, CRHScheme, CRHSchemeGadget};
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::convert::ToBitsGadget;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::uint8::UInt8;
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::iterable::Iterable;
use crate::gen_poseidon_params;

/// Returns the little-endian byte representation of the canonical integer representitive of the
/// given field element
pub(crate) fn fp_to_bytes(x: F) -> Vec<u8> {
    x.into_bigint().to_bytes_le()
}

pub(crate) fn cond_select_power_of_two_vec<F: Field, C: CondSelectGadget<F>>(
    position: &[Boolean<F>],
    values: &[Vec<C>],
) -> Result<Vec<C>, SynthesisError> {
    let out_size = values[0].len();
    // Ensure all the inputs are the same length
    for v in values.iter() {
        assert_eq!(v.len(), out_size);
    }

    // Index by index select the correct value from the input vectors
    let mut result = Vec::with_capacity(out_size);
    for i in 0..out_size {
        let vals_at_idx_i = values.iter().map(|v| v[i].clone()).collect::<Vec<_>>();
        let val = C::conditionally_select_power_of_two_vector(position, &vals_at_idx_i)?;
        result.push(val);
    }

    Ok(result)
}

pub(crate) fn fpvar_to_u64_check(
    a: &FpVar<F>,
) -> Result<(UInt64<F>, Boolean<F>), SynthesisError> {
    let mut a_bits: Vec<Boolean<F>> = a.to_bits_le().unwrap();
    if a_bits.len() < 256 {
        let zeros = vec![Boolean::<F>::FALSE; 256 - a_bits.len()];
        a_bits.extend(zeros);
    }

    let output: UInt64<F> = UInt64::from_bits_le(&a_bits[0..64]);
    let upper1: UInt64<F> = UInt64::from_bits_le(&a_bits[64..128]);
    let upper2: UInt64<F> = UInt64::from_bits_le(&a_bits[128..192]);
    let upper3: UInt64<F> = UInt64::from_bits_le(&a_bits[192..]);

    let is_zero1 = upper1.is_eq(&UInt64::constant(0)).unwrap();
    let is_zero2 = upper2.is_eq(&UInt64::constant(0)).unwrap();
    let is_zero3 = upper3.is_eq(&UInt64::constant(0)).unwrap();

    let fits_u64 = &is_zero1 & &is_zero2 & &is_zero3;

    Ok((output, fits_u64))
}

pub(crate) fn fpvar_to_u64(a: &FpVar<F>) -> Result<UInt64<F>, SynthesisError> {
    let mut a_bits: Vec<Boolean<F>> = a.to_bits_le().unwrap();
    if a_bits.len() < 256 {
        let zeros = vec![Boolean::<F>::FALSE; 256 - a_bits.len()];
        a_bits.extend(zeros);
    }

    let output: UInt64<F> = UInt64::from_bits_le(&a_bits[0..64]);
    return Ok(output);
}

pub fn fp_to_u64(a: &F) -> u64 {
    let a_bytes = a.to_sponge_bytes_as_vec();
    let a_u64 = u64::from_le_bytes(a_bytes[0..8].try_into().unwrap());

    return a_u64;
}

pub fn u64_to_bits_f(a: u64) -> Vec<F> {
    let bytes = a.to_le_bytes();
    let mut bit_array: Vec<u8> = Vec::new();

    for byte in bytes {
        for idx in 0..8 {
            let mask: u8 = 1 << idx;
            bit_array.push((byte & mask) >> idx);
        }
    }

    let mut field_array: Vec<F> = Vec::new();
    for entry in bit_array {
        field_array.extend_from_slice(&entry.to_sponge_field_elements_as_vec());
    }

    return field_array;
}

pub fn bits_f_to_u64(a: &[F]) -> u64 {
    let mut byte_array: Vec<u8> = Vec::new();
    assert!(a.len() >= 64);
    let mut temp: u8 = 0;
    for iter in 0..64 {
        let fp_bytes = fp_to_bytes(a[iter]);
        temp += (fp_bytes[0] & 1) << (iter % 8);

        if (iter + 1) % 8 == 0 {
            byte_array.push(temp);
            temp = 0;
        }
    }

    let output: u64 = u64::from_le_bytes(byte_array[..].try_into().unwrap());
    return output;
}

pub fn bytes_to_bits_f(bytes: &[u8]) -> Vec<F> {
    let mut bit_array: Vec<u8> = Vec::new();

    for byte in bytes {
        for idx in 0..8 {
            let mask: u8 = 1 << idx;
            bit_array.push((byte & mask) >> idx);
        }
    }

    let mut field_array: Vec<F> = Vec::new();
    for entry in bit_array {
        field_array.extend_from_slice(&entry.to_sponge_field_elements_as_vec());
    }

    return field_array;
}

pub fn bits_f_to_bytes(a: &[F]) -> Vec<u8> {
    let mut byte_array: Vec<u8> = Vec::new();
    assert!(a.len() % 8 == 0);
    let mut temp: u8 = 0;
    for iter in 0..a.len() {
        let fp_bytes = fp_to_bytes(a[iter]);
        temp += (fp_bytes[0] & 1) << (iter % 8);

        if (iter + 1) % 8 == 0 {
            byte_array.push(temp);
            temp = 0;
        }
    }
    return byte_array;
}

pub(crate) fn uint64_greater_than(
    a: &UInt64<F>,
    b: &UInt64<F>,
) -> Result<Boolean<F>, SynthesisError> {
    let a_val = a.to_bits_le()?;
    let b_val = b.to_bits_le()?;

    let a_fp = Boolean::le_bits_to_fp(&a_val)?;
    let b_fp = Boolean::le_bits_to_fp(&b_val)?;

    a_fp.is_cmp(&b_fp, Ordering::Greater, false)
}

pub(crate) fn fp_greater_than(a: &FpVar<F>, b: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    a.is_cmp(&b, Ordering::Greater, false)
}

pub fn poseidon_hash(input: &[F]) -> F {
    let params = gen_poseidon_params(2, false);
    poseidon::CRH::evaluate(&params, input).unwrap()
}

pub(crate) fn poseidon_hash_zk(input: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
    let params = gen_poseidon_params(2, false);
    let params_var = poseidon::constraints::CRHParametersVar { parameters: params };
    poseidon::constraints::CRHGadget::evaluate(&params_var, input)
}

#[derive(Clone, Debug)]
pub struct Bytestring<ConstraintF: PrimeField>(pub Vec<UInt8<ConstraintF>>);

impl<ConstraintF: PrimeField> EqGadget<ConstraintF> for Bytestring<ConstraintF> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.0.is_eq(&other.0)
    }
}

impl<ConstraintF: PrimeField> R1CSVar<ConstraintF> for Bytestring<ConstraintF> {
    type Value = Vec<u8>;

    fn cs(&self) -> ConstraintSystemRef<ConstraintF> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.0.value()
    }
}

impl<ConstraintF: PrimeField> AllocVar<[u8], ConstraintF> for Bytestring<ConstraintF> {
    fn new_variable<T: Borrow<[u8]>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let res = f();

        res.and_then(|v| {
            let v = v.borrow();
            let bs: Result<Vec<_>, SynthesisError> = v
                .iter()
                .map(|byte| UInt8::new_variable(ns!(cs, "byte"), || Ok(byte), mode))
                .collect();
            bs.map(Bytestring)
        })
    }
}

impl<ConstraintF: PrimeField> CondSelectGadget<ConstraintF> for Bytestring<ConstraintF> {
    fn conditionally_select(
        cond: &Boolean<ConstraintF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.0.len(), false_value.0.len());

        let bytes: Result<Vec<_>, _> = true_value
            .0
            .iter()
            .zip(false_value.0.iter())
            .map(|(t, f)| UInt8::conditionally_select(cond, t, f))
            .collect();
        bytes.map(Bytestring)
    }

    fn conditionally_select_power_of_two_vector(
        position: &[Boolean<ConstraintF>],
        values: &[Self],
    ) -> Result<Self, SynthesisError> {
        let m = values.len();
        let n = position.len();

        // Assert m is a power of 2, and n = log(m)
        assert!(m.is_power_of_two());
        assert_eq!(1 << n, m);

        let mut cur_mux_values = values.to_vec();

        // Traverse the evaluation tree from bottom to top in level order traversal.
        // This is method 5.1 from https://github.com/mir-protocol/r1cs-workshop/blob/master/workshop.pdf
        // TODO: Add method 5.2/5.3
        for i in 0..n {
            // Size of current layer.
            let cur_size = 1 << (n - i);
            assert_eq!(cur_mux_values.len(), cur_size);

            let mut next_mux_values = Vec::new();
            for j in (0..cur_size).step_by(2) {
                let cur = Self::conditionally_select(
                    &position[n - 1 - i],
                    // true case
                    &cur_mux_values[j + 1],
                    // false case
                    &cur_mux_values[j],
                )?;
                next_mux_values.push(cur);
            }
            cur_mux_values = next_mux_values;
        }

        Ok(cur_mux_values[0].clone())
    }
}