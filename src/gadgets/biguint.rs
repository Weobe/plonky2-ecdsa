use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Result;
use core::marker::PhantomData;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{IoResult, Read, Write};

use num::{BigUint, Integer, Zero};
use plonky2::field::extension::Extendable;
use plonky2::field::types::{PrimeField, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, Witness};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ux::{
    gadgets::{
        arithmetic_ux::{CircuitBuilderUX, UXTarget},
        multiple_comparison::list_le_ux_circuit,
    },
    witness::{GeneratedValuesUX, WitnessUX},
};

// from base 2^from to base 2^to
// requires from, to <= 32
pub fn convert_base(x: &Vec<u32>, from: usize, to: usize) -> Vec<u32> {
    let mut res: Vec<u32> = Vec::new();
    let mut rem: u64 = 0;
    let mut offset = 0;
    let mask = (1u64 << to) - 1;

    for &i in x {
        rem += (i as u64) << offset;
        offset += from;
        while offset >= to {
            let curr: u64 = rem & mask;
            res.push(curr.try_into().expect("Value doesn't fit in u32"));
            rem >>= to;
            offset -= to;
        }
    }
    if rem != 0 {
        res.push(rem.try_into().expect("Value doesn't fit in u32"));
    }
    assert!(mask < (1u64 << to));
    for i in &res {
        assert!((*i as u64) < (1u64 << to));
    }
    res
}

#[derive(Clone, Debug)]
pub struct BigUintTarget<const BITS: usize> {
    pub limbs: Vec<UXTarget<BITS>>,
}

impl<const BITS: usize> BigUintTarget<BITS> {
    pub fn num_limbs(&self) -> usize {
        self.limbs.len()
    }

    pub fn get_limb(&self, i: usize) -> UXTarget<BITS> {
        self.limbs[i]
    }

    pub fn to_target_vec(&self) -> Vec<Target> {
        self.limbs.iter().map(|t| t.0).collect()
    }

    pub fn from_target_vec(ts: &[Target]) -> Self {
        Self {
            limbs: ts.iter().map(|t| UXTarget(*t)).collect(),
        }
    }
}

pub trait CircuitBuilderBiguint<F: RichField + Extendable<D>, const D: usize> {
    fn constant_biguint<const BITS: usize>(&mut self, value: &BigUint) -> BigUintTarget<BITS>;

    fn zero_biguint<const BITS: usize>(&mut self) -> BigUintTarget<BITS>;

    fn connect_biguint<const BITS: usize>(
        &mut self,
        lhs: &BigUintTarget<BITS>,
        rhs: &BigUintTarget<BITS>,
    );

    fn pad_biguints<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>);

    fn cmp_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BoolTarget;

    fn add_virtual_biguint_target<const BITS: usize>(
        &mut self,
        num_limbs: usize,
    ) -> BigUintTarget<BITS>;

    /// Add two `BigUintTarget`s.
    fn add_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;

    /// Subtract two `BigUintTarget`s. We assume that the first is larger than the second.
    fn sub_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;

    fn mul_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;

    fn square_biguint<const BITS: usize>(&mut self, a: &BigUintTarget<BITS>)
        -> BigUintTarget<BITS>;

    fn mul_biguint_by_bool<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: BoolTarget,
    ) -> BigUintTarget<BITS>;

    /// Returns x * y + z. This is no more efficient than mul-then-add; it's purely for convenience (only need to call one CircuitBuilder function).
    fn mul_add_biguint<const BITS: usize>(
        &mut self,
        x: &BigUintTarget<BITS>,
        y: &BigUintTarget<BITS>,
        z: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;

    fn div_rem_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>);

    fn div_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;

    fn rem_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderBiguint<F, D>
    for CircuitBuilder<F, D>
{
    fn constant_biguint<const BITS: usize>(&mut self, value: &BigUint) -> BigUintTarget<BITS> {
        let limb_values = convert_base(&value.to_u32_digits(), 32, BITS);
        let limbs = limb_values
            .iter()
            .map(|&l| {
                assert!(l < (1 << BITS));
                self.constant_ux(l)
            })
            .collect();
        BigUintTarget { limbs }
    }

    fn zero_biguint<const BITS: usize>(&mut self) -> BigUintTarget<BITS> {
        self.constant_biguint(&BigUint::zero())
    }

    fn connect_biguint<const BITS: usize>(
        &mut self,
        lhs: &BigUintTarget<BITS>,
        rhs: &BigUintTarget<BITS>,
    ) {
        let min_limbs = lhs.num_limbs().min(rhs.num_limbs());
        for i in 0..min_limbs {
            self.connect_ux(lhs.get_limb(i), rhs.get_limb(i));
        }

        for i in min_limbs..lhs.num_limbs() {
            self.assert_zero_ux(lhs.get_limb(i));
        }
        for i in min_limbs..rhs.num_limbs() {
            self.assert_zero_ux(rhs.get_limb(i));
        }
    }

    fn pad_biguints<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>) {
        if a.num_limbs() > b.num_limbs() {
            let mut padded_b = b.clone();
            for _ in b.num_limbs()..a.num_limbs() {
                padded_b.limbs.push(self.zero_ux());
            }

            (a.clone(), padded_b)
        } else {
            let mut padded_a = a.clone();
            for _ in a.num_limbs()..b.num_limbs() {
                padded_a.limbs.push(self.zero_ux());
            }

            (padded_a, b.clone())
        }
    }

    fn cmp_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BoolTarget {
        let (a, b) = self.pad_biguints(a, b);

        list_le_ux_circuit(self, a.limbs, b.limbs)
    }

    fn add_virtual_biguint_target<const BITS: usize>(
        &mut self,
        num_limbs: usize,
    ) -> BigUintTarget<BITS> {
        let limbs = self.add_virtual_ux_targets(num_limbs);

        BigUintTarget { limbs }
    }

    fn add_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let num_limbs = a.num_limbs().max(b.num_limbs());

        let mut combined_limbs = vec![];
        let mut carry = self.zero_ux();
        for i in 0..num_limbs {
            let a_limb = if i < a.num_limbs() {
                a.limbs[i]
            } else {
                self.zero_ux()
            };
            let b_limb = if i < b.num_limbs() {
                b.limbs[i]
            } else {
                self.zero_ux()
            };

            let (new_limb, new_carry) = self.add_many_ux(&[carry, a_limb, b_limb]);
            carry = new_carry;
            combined_limbs.push(new_limb);
        }
        combined_limbs.push(carry);

        BigUintTarget {
            limbs: combined_limbs,
        }
    }

    fn sub_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let (a, b) = self.pad_biguints(a, b);
        let num_limbs = a.limbs.len();

        let mut result_limbs = vec![];

        let mut borrow = self.zero_ux();
        for i in 0..num_limbs {
            let (result, new_borrow) = self.sub_ux(a.limbs[i], b.limbs[i], borrow);
            result_limbs.push(result);
            borrow = new_borrow;
        }
        // Borrow should be zero here.

        BigUintTarget {
            limbs: result_limbs,
        }
    }

    fn mul_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let total_limbs = a.limbs.len() + b.limbs.len();

        let mut to_add = vec![vec![]; total_limbs];
        for i in 0..a.limbs.len() {
            for j in 0..b.limbs.len() {
                let (product, carry) = self.mul_ux(a.limbs[i], b.limbs[j]);
                to_add[i + j].push(product);
                to_add[i + j + 1].push(carry);
            }
        }

        let mut combined_limbs = vec![];
        let mut carry = self.zero_ux();
        for summands in &mut to_add {
            let (new_result, new_carry) = self.add_uxs_with_carry(summands, carry);
            combined_limbs.push(new_result);
            carry = new_carry;
        }
        combined_limbs.push(carry);

        BigUintTarget {
            limbs: combined_limbs,
        }
    }

    fn square_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let n = a.limbs.len();
        let total_limbs = n * 2;

        let mut to_add = vec![vec![]; total_limbs];
        for i in 0..n {
            for j in 0..(i + 1) {
                let (product, carry) = self.mul_ux(a.limbs[i], a.limbs[j]);
                to_add[i + j].push(product);
                to_add[i + j + 1].push(carry);
                //do the other way round
                if j != i {
                    to_add[i + j].push(product);
                    to_add[i + j + 1].push(carry);
                }
            }
        }

        let mut combined_limbs = vec![];
        let mut carry = self.zero_ux();
        for summands in &mut to_add {
            let (new_result, new_carry) = self.add_uxs_with_carry(summands, carry);
            combined_limbs.push(new_result);
            carry = new_carry;
        }
        combined_limbs.push(carry);

        BigUintTarget {
            limbs: combined_limbs,
        }
    }

    fn mul_biguint_by_bool<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: BoolTarget,
    ) -> BigUintTarget<BITS> {
        let t = b.target;

        BigUintTarget {
            limbs: a
                .limbs
                .iter()
                .map(|&l| UXTarget(self.mul(l.0, t)))
                .collect(),
        }
    }

    fn mul_add_biguint<const BITS: usize>(
        &mut self,
        x: &BigUintTarget<BITS>,
        y: &BigUintTarget<BITS>,
        z: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let prod = self.mul_biguint(x, y);
        self.add_biguint(&prod, z)
    }

    fn div_rem_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> (BigUintTarget<BITS>, BigUintTarget<BITS>) {
        let a_len = a.limbs.len();
        let b_len = b.limbs.len();
        let div_num_limbs = if b_len > a_len + 1 {
            0
        } else {
            a_len - b_len + 1
        };
        let div = self.add_virtual_biguint_target(div_num_limbs);
        let rem = self.add_virtual_biguint_target(b_len);

        self.add_simple_generator(BigUintDivRemGenerator::<F, D, BITS> {
            a: a.clone(),
            b: b.clone(),
            div: div.clone(),
            rem: rem.clone(),
            _phantom: PhantomData,
        });

        let div_b = self.mul_biguint(&div, b);
        let div_b_plus_rem = self.add_biguint(&div_b, &rem);
        self.connect_biguint(a, &div_b_plus_rem);

        let cmp_rem_b = self.cmp_biguint(&rem, b);
        self.assert_one(cmp_rem_b.target);

        (div, rem)
    }

    fn div_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let (div, _rem) = self.div_rem_biguint(a, b);
        div
    }

    fn rem_biguint<const BITS: usize>(
        &mut self,
        a: &BigUintTarget<BITS>,
        b: &BigUintTarget<BITS>,
    ) -> BigUintTarget<BITS> {
        let (_div, rem) = self.div_rem_biguint(a, b);
        rem
    }
}

pub trait WitnessBigUint<F: PrimeField64, const BITS: usize>: Witness<F> {
    fn get_biguint_target(&self, target: BigUintTarget<BITS>) -> BigUint;
    fn set_biguint_target(&mut self, target: &BigUintTarget<BITS>, value: &BigUint) -> Result<()>;
}

impl<T: Witness<F>, F: PrimeField64, const BITS: usize> WitnessBigUint<F, BITS> for T {
    fn get_biguint_target(&self, target: BigUintTarget<BITS>) -> BigUint {
        target
            .limbs
            .into_iter()
            .rev()
            .fold(BigUint::zero(), |acc, limb| {
                (acc << BITS) + self.get_target(limb.0).to_canonical_biguint()
            })
    }

    fn set_biguint_target(&mut self, target: &BigUintTarget<BITS>, value: &BigUint) -> Result<()> {
        let mut limbs = convert_base(&value.to_u32_digits(), 32, BITS);
        assert!(target.num_limbs() >= limbs.len());
        limbs.resize(target.num_limbs(), 0);
        for i in 0..target.num_limbs() {
            self.set_ux_target(target.limbs[i], limbs[i])?;
        }

        Ok(())
    }
}

pub trait GeneratedValuesBigUint<F: PrimeField, const BITS: usize> {
    fn set_biguint_target(&mut self, target: &BigUintTarget<BITS>, value: &BigUint) -> Result<()>;
}

impl<F: PrimeField, const BITS: usize> GeneratedValuesBigUint<F, BITS> for GeneratedValues<F> {
    fn set_biguint_target(&mut self, target: &BigUintTarget<BITS>, value: &BigUint) -> Result<()> {
        let mut limbs = convert_base(&value.to_u32_digits(), 32, BITS);
        assert!(target.num_limbs() >= limbs.len());
        limbs.resize(target.num_limbs(), 0);
        for i in 0..target.num_limbs() {
            self.set_ux_target(target.get_limb(i), limbs[i])?;
        }

        Ok(())
    }
}

#[derive(Debug)]
struct BigUintDivRemGenerator<F: RichField + Extendable<D>, const D: usize, const BITS: usize> {
    a: BigUintTarget<BITS>,
    b: BigUintTarget<BITS>,
    div: BigUintTarget<BITS>,
    rem: BigUintTarget<BITS>,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, const BITS: usize> SimpleGenerator<F, D>
    for BigUintDivRemGenerator<F, D, BITS>
{
    fn id(&self) -> String {
        "BigUintDivRemGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.a
            .limbs
            .iter()
            .chain(&self.b.limbs)
            .map(|&l| l.0)
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let a = witness.get_biguint_target(self.a.clone());
        let b = witness.get_biguint_target(self.b.clone());
        let (div, rem) = a.div_rem(&b);
        out_buffer.set_biguint_target(&self.div, &div)?;
        out_buffer.set_biguint_target(&self.rem, &rem)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        // Serialise each biguint target's limbs.
        dst.write_target_vec(&self.a.to_target_vec())?;
        dst.write_target_vec(&self.b.to_target_vec())?;
        dst.write_target_vec(&self.div.to_target_vec())?;
        dst.write_target_vec(&self.rem.to_target_vec())
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        let a = BigUintTarget::from_target_vec(&src.read_target_vec()?);
        let b = BigUintTarget::from_target_vec(&src.read_target_vec()?);
        let div = BigUintTarget::from_target_vec(&src.read_target_vec()?);
        let rem = BigUintTarget::from_target_vec(&src.read_target_vec()?);

        Ok(Self {
            a,
            b,
            div,
            rem,
            _phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use num::{BigUint, FromPrimitive, Integer};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use rand::rngs::OsRng;
    use rand::Rng;

    use super::*;
    use crate::gadgets::biguint::{CircuitBuilderBiguint, WitnessBigUint};

    const BITS: usize = 29;
    #[test]
    fn test_biguint_add() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut rng = OsRng;

        let x_value = BigUint::from_u128(rng.gen()).unwrap();
        let y_value = BigUint::from_u128(rng.gen()).unwrap();
        let expected_z_value = &x_value + &y_value;

        let config = CircuitConfig::standard_recursion_config();
        let mut pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x: BigUintTarget<BITS> = builder
            .add_virtual_biguint_target(convert_base(&x_value.to_u32_digits(), 32, BITS).len());
        let y = builder
            .add_virtual_biguint_target(convert_base(&y_value.to_u32_digits(), 32, BITS).len());
        let z = builder.add_biguint(&x, &y);
        let expected_z = builder.add_virtual_biguint_target(
            convert_base(&expected_z_value.to_u32_digits(), 32, BITS).len(),
        );
        builder.connect_biguint(&z, &expected_z);

        pw.set_biguint_target(&x, &x_value)?;
        pw.set_biguint_target(&y, &y_value)?;
        pw.set_biguint_target(&expected_z, &expected_z_value)?;

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_biguint_sub() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut rng = OsRng;

        let mut x_value = BigUint::from_u128(rng.gen()).unwrap();
        let mut y_value = BigUint::from_u128(rng.gen()).unwrap();
        if y_value > x_value {
            (x_value, y_value) = (y_value, x_value);
        }
        let expected_z_value = &x_value - &y_value;

        let config = CircuitConfig::standard_recursion_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x: BigUintTarget<BITS> = builder.constant_biguint(&x_value);
        let y = builder.constant_biguint(&y_value);
        let z = builder.sub_biguint(&x, &y);
        let expected_z = builder.constant_biguint(&expected_z_value);

        builder.connect_biguint(&z, &expected_z);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_biguint_mul() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut rng = OsRng;

        let x_value = BigUint::from_u128(rng.gen()).unwrap();
        let y_value = BigUint::from_u128(rng.gen()).unwrap();
        let expected_z_value = &x_value * &y_value;

        let config = CircuitConfig::standard_recursion_config();
        let mut pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x: BigUintTarget<BITS> = builder
            .add_virtual_biguint_target(convert_base(&x_value.to_u32_digits(), 32, BITS).len());
        let y = builder
            .add_virtual_biguint_target(convert_base(&y_value.to_u32_digits(), 32, BITS).len());
        let z = builder.mul_biguint(&x, &y);
        let expected_z = builder.add_virtual_biguint_target(
            convert_base(&expected_z_value.to_u32_digits(), 32, BITS).len(),
        );
        builder.connect_biguint(&z, &expected_z);

        pw.set_biguint_target(&x, &x_value)?;
        pw.set_biguint_target(&y, &y_value)?;
        pw.set_biguint_target(&expected_z, &expected_z_value)?;

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_biguint_cmp() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut rng = OsRng;

        let x_value = BigUint::from_u128(rng.gen()).unwrap();
        let y_value = BigUint::from_u128(rng.gen()).unwrap();

        let config = CircuitConfig::standard_recursion_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x: BigUintTarget<BITS> = builder.constant_biguint(&x_value);
        let y = builder.constant_biguint(&y_value);
        let cmp = builder.cmp_biguint(&x, &y);
        let expected_cmp = builder.constant_bool(x_value <= y_value);

        builder.connect(cmp.target, expected_cmp.target);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_biguint_div_rem() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut rng = OsRng;

        let mut x_value = BigUint::from_u128(rng.gen()).unwrap();
        let mut y_value = BigUint::from_u128(rng.gen()).unwrap();
        if y_value > x_value {
            (x_value, y_value) = (y_value, x_value);
        }
        let (expected_div_value, expected_rem_value) = x_value.div_rem(&y_value);

        let config = CircuitConfig::standard_recursion_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x: BigUintTarget<BITS> = builder.constant_biguint(&x_value);
        let y = builder.constant_biguint(&y_value);
        let (div, rem) = builder.div_rem_biguint(&x, &y);

        let expected_div = builder.constant_biguint(&expected_div_value);
        let expected_rem = builder.constant_biguint(&expected_rem_value);

        builder.connect_biguint(&div, &expected_div);
        builder.connect_biguint(&rem, &expected_rem);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
