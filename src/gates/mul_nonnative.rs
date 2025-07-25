use crate::gadgets::biguint::convert_base;
use anyhow::Result;
use num::{BigUint, Integer};
use plonky2::{
    field::{
        extension::Extendable,
        types::{Field, PrimeField},
    },
    gates::gate::Gate,
    hash::hash_types::RichField,
    iop::{
        ext_target::ExtensionTarget,
        generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef},
        target::Target,
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData},
        vars::{EvaluationTargets, EvaluationVars},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};
use std::marker::PhantomData;

#[derive(Debug)]
pub struct MulNonnativeGate<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    // W: size of chunks
    pub num_limbs: usize,
    _phantom: PhantomData<FF>,
    _phantom2: PhantomData<F>,
}

// ASSUMES X, Y, R, Q ARE ALREADY RANGE CHECKED
impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> MulNonnativeGate<F, D, FF> {
    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_limbs() -> usize {
        9
    }

    pub fn x(&self, i: usize) -> usize {
        i
    }

    pub fn y(&self, i: usize) -> usize {
        i + self.num_limbs
    }

    pub fn r(&self, i: usize) -> usize {
        i + 2 * self.num_limbs
    }

    pub fn q(&self, i: usize) -> usize {
        i + 3 * self.num_limbs
    }

    pub fn check_sum(&self, i: usize) -> usize {
        i + 4 * self.num_limbs
    }
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> MulNonnativeGate<F, D, FF> {
    pub fn new_from_config(_config: &CircuitConfig) -> Self {
        Self {
            num_limbs: Self::num_limbs(),
            _phantom: PhantomData::<FF>,
            _phantom2: PhantomData::<F>,
        }
    }
}

// Given the nonnative targets x, y (each with 9 limbs, 9 * 29 = 261 > 256) and modulus m, we want to get r, such that
// x * y - (q * m + r) = 0, where q and r are also nonnative targets with 29-bit limbs
// This gates takes advantage of the limbs being 29-bits in size to optimize modular nonnative multiplication
// It calculates the 17-limb convolution check_sum = x * y - (q * m + r) without doing carries
// so that the value of every limb of check_sum lies in (-2^62, 2^62)
// Then the CheckSum gate is used to check that check_sum = 0 after doing the carries in 29-bits
//
// NOTE: This gate is not sound for being used on its own as it needs the CheckSum gate and additional range checks for correctness
// See the mul_nonnative() gadget in gadgets/nonnative.rs for appropriate usage
impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> Gate<F, D>
    for MulNonnativeGate<F, D, FF>
{
    fn id(&self) -> String {
        format!("MulNonnative() {}", FF::order())
    }

    fn num_wires(&self) -> usize {
        self.num_limbs * 6 - 1
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn num_constraints(&self) -> usize {
        self.num_limbs * 2 - 1
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        let modulus: BigUint = FF::order();
        let modulus_base_29: Vec<u32> = convert_base(&modulus.to_u32_digits(), 32, 29);
        let modulus_base_29_f: Vec<_> = modulus_base_29
            .clone()
            .into_iter()
            .map(F::Extension::from_canonical_u32)
            .collect();
        assert!(modulus_base_29.len() == self.num_limbs);
        for i in 0..self.num_limbs * 2 - 1 {
            let l = ((i as i32) - (self.num_limbs as i32) + 1).max(0) as usize;
            let r = (i + 1).min(self.num_limbs);
            let mut accum = F::Extension::from_canonical_u32(0);
            for j in l..r {
                assert!(i - j < self.num_limbs);
                assert!(j < self.num_limbs);
                let q = vars.local_wires[self.q(i - j)];
                let qm = modulus_base_29_f[j] * q;
                let xy = vars.local_wires[self.x(j)] * vars.local_wires[self.y(i - j)];
                accum += qm;
                accum -= xy;
            }
            if i < self.num_limbs {
                accum += vars.local_wires[self.r(i)];
            }
            res.push(accum - vars.local_wires[self.check_sum(i)]);
        }
        res
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut res = Vec::new();
        let modulus: BigUint = FF::order();
        let modulus_base_29: Vec<u32> = convert_base(&modulus.to_u32_digits(), 32, 29);
        assert!(modulus_base_29.len() == self.num_limbs);
        for i in 0..self.num_limbs * 2 - 1 {
            let l = ((i as i32) - (self.num_limbs as i32) + 1).max(0) as usize;
            let r = (i + 1).min(self.num_limbs);
            let mut sum = builder.constant_extension(F::Extension::from_canonical_u32(0));
            for j in l..r {
                assert!(i - j < self.num_limbs);
                assert!(j < self.num_limbs);
                let m = builder
                    .constant_extension(F::Extension::from_canonical_u32(modulus_base_29[j]));
                let qm = builder.mul_extension(m, vars.local_wires[self.q(i - j)]);
                let xy = builder
                    .mul_extension(vars.local_wires[self.x(j)], vars.local_wires[self.y(i - j)]);
                let diff = builder.sub_extension(qm, xy);
                sum = builder.add_extension(sum, diff);
            }
            let accum;
            if i < self.num_limbs {
                accum = builder.add_extension(sum, vars.local_wires[self.r(i)]);
            } else {
                accum = sum;
            };
            res.push(builder.sub_extension(accum, vars.local_wires[self.check_sum(i)]));
        }

        res
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        vec![WitnessGeneratorRef::new(
            MulNonnativeGenerator::<F, D, FF> {
                row,
                num_limbs: self.num_limbs,
                _phantom: PhantomData::<FF>,
                _phantom2: PhantomData::<F>,
            }
            .adapter(),
        )]
    }

    // Nothing special in serialized form
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_limbs)?;
        Ok(())
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let num_limbs = src
            .read_usize()
            .expect("Failed to read num_ops from serialized MulNonnativeGate");
        Ok(Self {
            num_limbs,
            _phantom: PhantomData::<FF>,
            _phantom2: PhantomData::<F>,
        })
    }
}

// Witness generator for the gate
#[derive(Debug)]
pub struct MulNonnativeGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    row: usize,
    num_limbs: usize,
    _phantom: PhantomData<FF>,
    _phantom2: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> MulNonnativeGenerator<F, D, FF> {
    fn x(&self, i: usize) -> Target {
        Target::wire(self.row, i)
    }

    fn y(&self, i: usize) -> Target {
        Target::wire(self.row, i + self.num_limbs)
    }

    fn r(&self, i: usize) -> Target {
        Target::wire(self.row, i + 2 * self.num_limbs)
    }

    fn q(&self, i: usize) -> Target {
        Target::wire(self.row, i + 3 * self.num_limbs)
    }

    fn check_sum(&self, i: usize) -> Target {
        Target::wire(self.row, i + 4 * self.num_limbs)
    }
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F, D>
    for MulNonnativeGenerator<F, D, FF>
{
    fn id(&self) -> String {
        format!(
            "MulNonnativeGenerator(row={}, FF= {})",
            self.row,
            FF::order()
        )
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        for i in 0..self.num_limbs {
            res.push(self.x(i));
            res.push(self.y(i));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let modulus = FF::order();
        let mut modulus_base_29: Vec<u32> = convert_base(&modulus.to_u32_digits(), 32, 29);
        let x_base_29: Vec<u32> = (0..self.num_limbs)
            .map(|i| {
                witness
                    .get_target(self.x(i))
                    .to_canonical_u64()
                    .try_into()
                    .expect("Value doesn't fit in u32")
            })
            .collect();
        let y_base_29: Vec<u32> = (0..self.num_limbs)
            .map(|i| {
                witness
                    .get_target(self.y(i))
                    .to_canonical_u64()
                    .try_into()
                    .expect("Value doesn't fit in u32")
            })
            .collect();
        for i in 0..self.num_limbs {
            assert!(x_base_29[i] < (1u32 << 29));
            assert!(y_base_29[i] < (1u32 << 29));
        }
        let x_base_32 = convert_base(&x_base_29, 29, 32);
        let y_base_32 = convert_base(&y_base_29, 29, 32);

        let x_biguint = BigUint::from_slice(&x_base_32[..]);
        let y_biguint = BigUint::from_slice(&y_base_32[..]);

        let mul = x_biguint.clone() * y_biguint.clone();
        let (q_bigint, r_bigint) = mul.div_rem(&modulus);

        let mut q_base_29 = convert_base(&q_bigint.to_u32_digits(), 32, 29);
        let mut r_base_29 = convert_base(&r_bigint.to_u32_digits(), 32, 29);
        while q_base_29.len() < self.num_limbs {
            q_base_29.push(0);
        }
        while r_base_29.len() < self.num_limbs {
            r_base_29.push(0);
        }

        while modulus_base_29.len() < self.num_limbs {
            modulus_base_29.push(0);
        }

        for i in 0..self.num_limbs {
            out_buffer.set_target(self.q(i), F::from_canonical_u32(q_base_29[i]))?;
            out_buffer.set_target(self.r(i), F::from_canonical_u32(r_base_29[i]))?;
        }

        for i in 0..(self.num_limbs * 2 - 1) {
            let l = ((i as i32) - (self.num_limbs as i32) + 1).max(0) as usize;
            let r = (i + 1).min(self.num_limbs);
            let mut accum: F = F::from_canonical_u32(0);
            for j in l..r {
                let m: F = F::from_canonical_u64(modulus_base_29[j].into());
                let q: F = F::from_canonical_u64(q_base_29[i - j].into());
                let x: F = F::from_canonical_u64(x_base_29[j].into());
                let y: F = F::from_canonical_u64(y_base_29[i - j].into());
                accum += q * m - x * y;
            }

            if i < self.num_limbs {
                accum += F::from_canonical_u64(r_base_29[i].into());
            }

            out_buffer.set_target(self.check_sum(i), accum)?;
        }
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.num_limbs)?;
        Ok(())
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let num_limbs = src.read_usize()?;
        Ok(Self {
            row,
            num_limbs,
            _phantom: PhantomData::<FF>,
            _phantom2: PhantomData::<F>,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct CheckSumGate<F: RichField + Extendable<D>, const D: usize> {
    // W: size of chunks
    pub num_limbs: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> CheckSumGate<F, D> {
    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_limbs() -> usize {
        9
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Default for CheckSumGate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

// This gate takes as input a value with 17 limbs, where the value of every limb lies between (-2^62, 2^62)
// It checks that after doing carries in base 2^29, this value is equal to zero
// It does this by calculating the carries in an array b, so that
// b_0 * 2^29 = a_0
// b_1 * 2^29 = a_1 + b_0
// ...
// a_16 + b_15 = 0
//
// External range checks should be performed outside of this gate to ensure that all values of b are in the range (-2^33, 2^33)
// Note that the actual b values that this gate computes are offsetted by 2^33, so that it suffices to check that b_i are in the range (0, 2^34)
// This is handled in mul_nonnative() gadget in gadgets/nonnative.rs

impl<F: RichField + Extendable<D>, const D: usize> CheckSumGate<F, D> {
    pub fn new_from_config(_config: &CircuitConfig) -> Self {
        Self {
            num_limbs: Self::num_limbs(),
            _phantom: PhantomData,
        }
    }

    pub fn a(&self, i: usize) -> usize {
        i
    }

    pub fn b(&self, i: usize) -> usize {
        i + self.num_limbs * 2 - 1
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for CheckSumGate<F, D> {
    fn id(&self) -> String {
        "CheckSum()".to_string()
    }

    fn num_wires(&self) -> usize {
        self.num_limbs * 4 - 3
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn num_constraints(&self) -> usize {
        self.num_limbs * 2 - 1
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        let base = F::Extension::from_canonical_u64(1 << 29);
        let offset = F::Extension::from_canonical_u64(1u64 << 33);
        let mut last = F::Extension::from_canonical_u64(0);
        for i in 0..(self.num_limbs * 2 - 1) {
            if i < (self.num_limbs * 2 - 2) {
                let offseted_b_i = vars.local_wires[self.b(i)] - offset;
                res.push(vars.local_wires[self.a(i)] + last - base * offseted_b_i);
                last = offseted_b_i;
            } else {
                // the last one should be zero
                res.push(vars.local_wires[self.a(i)] + last);
            }
        }
        res
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut res = Vec::new();
        let base = builder.constant_extension(F::Extension::from_canonical_u64(1 << 29));
        let offset = builder.constant_extension(F::Extension::from_canonical_u64(1u64 << 33));
        let mut last = builder.constant_extension(F::Extension::from_canonical_u64(0));
        for i in 0..(self.num_limbs * 2 - 1) {
            if i < (self.num_limbs * 2 - 2) {
                let offseted_b_i = builder.sub_extension(vars.local_wires[self.b(i)], offset);
                let m = builder.mul_extension(base, offseted_b_i);
                let s = builder.add_extension(vars.local_wires[self.a(i)], last);
                res.push(builder.sub_extension(s, m));
                last = offseted_b_i;
            } else {
                // the last one should be zero
                res.push(builder.add_extension(vars.local_wires[self.a(i)], last));
            }
        }

        res
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        vec![WitnessGeneratorRef::new(
            CheckSumGenerator::<F, D> {
                row,
                num_limbs: self.num_limbs,
                _phantom: PhantomData,
            }
            .adapter(),
        )]
    }

    // Nothing special in serialized form
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_limbs)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            num_limbs: src
                .read_usize()
                .expect("Failed to read num_ops from serialized CheckSumGate"),
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
pub struct CheckSumGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    num_limbs: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> CheckSumGenerator<F, D> {
    fn a(&self, i: usize) -> Target {
        Target::wire(self.row, i)
    }

    fn b(&self, i: usize) -> Target {
        Target::wire(self.row, i + self.num_limbs * 2 - 1)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for CheckSumGenerator<F, D>
{
    fn id(&self) -> String {
        format!("CheckSumGenerator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        for i in 0..(2 * self.num_limbs - 1) {
            res.push(self.a(i));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let base = F::from_canonical_u64(1 << 29);
        let mut last = F::from_canonical_u64(0);
        let offset = F::from_canonical_u64(1u64 << 33);
        for i in 0..(self.num_limbs * 2 - 2) {
            let a_i = witness.get_target(self.a(i));
            let b_i_field = (a_i + last) / base;

            out_buffer.set_target(self.b(i), b_i_field + offset)?;
            last = b_i_field;
            assert!((b_i_field + offset).to_canonical_u64() < 1u64 << 34);
        }
        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.num_limbs)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let num_limbs = src.read_usize()?;
        Ok(Self {
            row,
            num_limbs,
            _phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::secp256k1_base::Secp256K1Base;
    use plonky2::gates::gate_testing::{test_eval_fns, test_low_degree};
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        type FF = Secp256K1Base;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        const D: usize = 2;
        let config = CircuitConfig::standard_ecc_config();
        test_low_degree::<GoldilocksField, _, D>(MulNonnativeGate::<F, D, FF>::new_from_config(
            &config,
        ))
    }

    #[test]
    fn eval_fns() -> Result<()> {
        type FF = Secp256K1Base;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        const D: usize = 2;
        let config = CircuitConfig::standard_ecc_config();
        test_eval_fns::<F, C, _, D>(MulNonnativeGate::<F, D, FF>::new_from_config(&config))
    }
}
