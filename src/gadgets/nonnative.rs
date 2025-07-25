use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Result;
use core::marker::PhantomData;
use num::integer::div_ceil;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{Buffer, IoError, IoResult, Read, Write};

use num::{BigUint, Integer, One, Zero};
use plonky2::field::extension::Extendable;
use plonky2::field::types::{Field, PrimeField};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartitionWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_ux::{
    gadgets::{
        arithmetic_ux::{CircuitBuilderUX, UXTarget},
        range_check::range_check_ux_circuit,
    },
    witness::GeneratedValuesUX,
};

use crate::gates::mul_nonnative::{CheckSumGate, MulNonnativeGate};

use crate::gadgets::biguint::{
    BigUintTarget, CircuitBuilderBiguint, GeneratedValuesBigUint, WitnessBigUint,
};

pub const BITS: usize = 29;

#[derive(Clone, Debug)]
pub struct NonNativeTarget<FF: Field> {
    pub value: BigUintTarget<BITS>,
    pub(crate) _phantom: PhantomData<FF>,
}

impl<FF: Field> NonNativeTarget<FF> {
    pub fn to_target_vec(&self) -> Vec<Target> {
        self.value.to_target_vec()
    }

    pub fn from_target_vec(ts: &[Target]) -> Self {
        Self {
            value: BigUintTarget::from_target_vec(ts),
            _phantom: PhantomData,
        }
    }
}

pub trait CircuitBuilderNonNative<F: RichField + Extendable<D>, const D: usize> {
    fn num_nonnative_limbs<FF: Field>() -> usize {
        div_ceil(FF::BITS, BITS)
    }

    fn biguint_to_nonnative<FF: Field>(
        &mut self,
        x: &BigUintTarget<BITS>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn nonnative_to_canonical_biguint<FF: Field>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> BigUintTarget<BITS>;

    fn constant_nonnative<FF: PrimeField>(&mut self, x: FF) -> NonNativeTarget<FF>;

    fn zero_nonnative<FF: PrimeField>(&mut self) -> NonNativeTarget<FF>;

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative<FF: Field>(
        &mut self,
        lhs: &NonNativeTarget<FF>,
        rhs: &NonNativeTarget<FF>,
    );

    fn add_virtual_nonnative_target<FF: Field>(&mut self) -> NonNativeTarget<FF>;

    fn add_virtual_nonnative_target_sized<FF: Field>(
        &mut self,
        num_limbs: usize,
    ) -> NonNativeTarget<FF>;

    fn add_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn mul_nonnative_by_bool<FF: Field>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: BoolTarget,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn if_nonnative<FF: PrimeField>(
        &mut self,
        b: BoolTarget,
        x: &NonNativeTarget<FF>,
        y: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn add_many_nonnative<FF: PrimeField>(
        &mut self,
        to_add: &[NonNativeTarget<FF>],
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn mul_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn mul_many_nonnative<FF: PrimeField>(
        &mut self,
        to_mul: &[NonNativeTarget<FF>],
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn neg_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    fn inv_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF>;

    /// Returns `x % |FF|` as a `NonNativeTarget`.
    fn reduce<FF: Field>(&mut self, x: &BigUintTarget<BITS>) -> NonNativeTarget<FF>;

    fn reduce_nonnative<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF>;

    fn bool_to_nonnative<FF: Field>(&mut self, b: &BoolTarget) -> NonNativeTarget<FF>;

    // Split a nonnative field element to bits.
    fn split_nonnative_to_bits<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> Vec<BoolTarget>;

    fn nonnative_conditional_neg<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        b: BoolTarget,
        range_check: bool,
    ) -> NonNativeTarget<FF>;
}

// For all the functions with range_check argument, range_check should only be false in cases where this is not the last nonnative operation to be performed
// The soundness of the nonnative arithmetic holds even when doing operations with numbers bigger than the modulus as long as
// it is known that the output fits in 9 limbs of 29 bits each (i.e. <= 2^261)
//
// However if this is the final nonnative operation, it should be checked that the output lies in [0, modulus - 1]
// When in doubt, having range_check=true is the safest option, this option is available mainly to optimize gate count when it is a bottleneck

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderNonNative<F, D>
    for CircuitBuilder<F, D>
{
    fn num_nonnative_limbs<FF: Field>() -> usize {
        div_ceil(FF::BITS, BITS)
    }

    fn biguint_to_nonnative<FF: Field>(
        &mut self,
        x: &BigUintTarget<BITS>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        if range_check {
            let modulus = self.constant_biguint(&FF::order());
            let cmp = self.cmp_biguint(x, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }
        assert!(x.limbs.len() <= div_ceil(256, BITS));
        NonNativeTarget {
            value: x.clone(),
            _phantom: PhantomData,
        }
    }

    fn nonnative_to_canonical_biguint<FF: Field>(
        &mut self,
        x: &NonNativeTarget<FF>,
    ) -> BigUintTarget<BITS> {
        x.value.clone()
    }

    fn constant_nonnative<FF: PrimeField>(&mut self, x: FF) -> NonNativeTarget<FF> {
        let x_biguint = self.constant_biguint(&x.to_canonical_biguint());
        self.biguint_to_nonnative(&x_biguint, false)
    }

    fn zero_nonnative<FF: PrimeField>(&mut self) -> NonNativeTarget<FF> {
        self.constant_nonnative(FF::ZERO)
    }

    // Assert that two NonNativeTarget's, both assumed to be in reduced form, are equal.
    fn connect_nonnative<FF: Field>(
        &mut self,
        lhs: &NonNativeTarget<FF>,
        rhs: &NonNativeTarget<FF>,
    ) {
        self.connect_biguint(&lhs.value, &rhs.value);
    }

    fn add_virtual_nonnative_target<FF: Field>(&mut self) -> NonNativeTarget<FF> {
        let num_limbs = Self::num_nonnative_limbs::<FF>();
        let value = self.add_virtual_biguint_target(num_limbs);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn add_virtual_nonnative_target_sized<FF: Field>(
        &mut self,
        num_limbs: usize,
    ) -> NonNativeTarget<FF> {
        let value = self.add_virtual_biguint_target(num_limbs);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn add_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let sum = self.add_virtual_nonnative_target::<FF>();
        let overflow = self.add_virtual_bool_target_unsafe();

        self.add_simple_generator(NonNativeAdditionGenerator::<F, D, FF> {
            a: a.clone(),
            b: b.clone(),
            sum: sum.clone(),
            overflow,
            _phantom: PhantomData,
        });

        let sum_expected = self.add_biguint(&a.value, &b.value);

        let modulus = self.constant_biguint(&FF::order());
        let mod_times_overflow = self.mul_biguint_by_bool(&modulus, overflow);
        let sum_actual = self.add_biguint(&sum.value, &mod_times_overflow);
        self.connect_biguint(&sum_expected, &sum_actual);
        // Range-check result.
        if range_check {
            let cmp = self.cmp_biguint(&sum.value, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }

        sum
    }

    fn mul_nonnative_by_bool<FF: Field>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: BoolTarget,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let value = self.mul_biguint_by_bool(&a.value, b);
        if range_check {
            let modulus = self.constant_biguint(&FF::order());
            let cmp = self.cmp_biguint(&value, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }
        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn if_nonnative<FF: PrimeField>(
        &mut self,
        b: BoolTarget,
        x: &NonNativeTarget<FF>,
        y: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let not_b = self.not(b);
        let maybe_x = self.mul_nonnative_by_bool(x, b, false);
        let maybe_y = self.mul_nonnative_by_bool(y, not_b, false);
        self.add_nonnative(&maybe_x, &maybe_y, range_check)
    }

    fn add_many_nonnative<FF: PrimeField>(
        &mut self,
        to_add: &[NonNativeTarget<FF>],
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        if to_add.len() == 1 {
            return to_add[0].clone();
        }

        let sum = self.add_virtual_nonnative_target::<FF>();
        let overflow = self.add_virtual_ux_target();
        let summands = to_add.to_vec();

        self.add_simple_generator(NonNativeMultipleAddsGenerator::<F, D, FF> {
            summands: summands.clone(),
            sum: sum.clone(),
            overflow,
            _phantom: PhantomData,
        });

        range_check_ux_circuit(self, sum.value.limbs.clone());
        range_check_ux_circuit(self, vec![overflow]);

        let sum_expected = summands
            .iter()
            .fold(self.zero_biguint(), |a, b| self.add_biguint(&a, &b.value));

        let modulus = self.constant_biguint(&FF::order());
        let overflow_biguint = BigUintTarget {
            limbs: vec![overflow],
        };
        let mod_times_overflow = self.mul_biguint(&modulus, &overflow_biguint);
        let sum_actual = self.add_biguint(&sum.value, &mod_times_overflow);
        self.connect_biguint(&sum_expected, &sum_actual);

        // Range-check result.
        // TODO: can potentially leave unreduced until necessary (e.g. when connecting values).
        if range_check {
            let cmp = self.cmp_biguint(&sum.value, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }
        sum
    }

    // Subtract two `NonNativeTarget`s.
    fn sub_nonnative<FF: PrimeField>(
        &mut self,
        a: &NonNativeTarget<FF>,
        b: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let diff = self.add_virtual_nonnative_target::<FF>();
        let overflow = self.add_virtual_bool_target_unsafe();

        self.add_simple_generator(NonNativeSubtractionGenerator::<F, D, FF> {
            a: a.clone(),
            b: b.clone(),
            diff: diff.clone(),
            overflow,
            _phantom: PhantomData,
        });

        range_check_ux_circuit(self, diff.value.limbs.clone());
        self.assert_bool(overflow);

        let diff_plus_b = self.add_biguint(&diff.value, &b.value);
        let modulus = self.constant_biguint(&FF::order());
        let mod_times_overflow = self.mul_biguint_by_bool(&modulus, overflow);
        let diff_plus_b_reduced = self.sub_biguint(&diff_plus_b, &mod_times_overflow);
        self.connect_biguint(&a.value, &diff_plus_b_reduced);

        if range_check {
            let cmp = self.cmp_biguint(&diff.value, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }
        diff
    }

    fn mul_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        y: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let mul_gate = MulNonnativeGate::<F, D, FF>::new_from_config(&self.config);
        let constants = vec![];
        let n = MulNonnativeGate::<F, D, FF>::num_limbs();
        let x_wire_inds: Vec<_> = (0..n).map(|i| mul_gate.x(i)).collect();
        let y_wire_inds: Vec<_> = (0..n).map(|i| mul_gate.y(i)).collect();
        let q_wire_inds: Vec<_> = (0..n).map(|i| mul_gate.q(i)).collect();
        let r_wire_inds: Vec<_> = (0..n).map(|i| mul_gate.r(i)).collect();
        let check_sum_wire_inds: Vec<_> = (0..2 * n - 1).map(|i| mul_gate.check_sum(i)).collect();
        let row = self.add_gate(mul_gate, constants);

        for i in 0..n {
            let wire_x = Target::wire(row, x_wire_inds[i]);
            let wire_y = Target::wire(row, y_wire_inds[i]);
            if i < x.value.limbs.len() {
                let target_x = x.value.limbs[i];
                self.connect(target_x.0, wire_x);
            } else {
                let zero = self.zero();
                self.connect(zero, wire_x);
            }

            if i < y.value.limbs.len() {
                let target_y = y.value.limbs[i];
                self.connect(target_y.0, wire_y);
            } else {
                let zero = self.zero();
                self.connect(zero, wire_y);
            }
        }
        let q: Vec<UXTarget<BITS>> = (0..n)
            .map(|i| UXTarget(Target::wire(row, q_wire_inds[i])))
            .collect();
        let r: Vec<_> = (0..n)
            .map(|i| UXTarget(Target::wire(row, r_wire_inds[i])))
            .collect();

        let check_sum: Vec<_> = (0..2 * n - 1)
            .map(|i| UXTarget::<BITS>(Target::wire(row, check_sum_wire_inds[i])))
            .collect();

        //check that q * m + r - x * m = 0
        let check_gate = CheckSumGate::<F, D>::new_from_config(&self.config);
        let constants = vec![];
        let row = self.add_gate(check_gate, constants);
        let tmp_gate = CheckSumGate::<F, D>::new_from_config(&self.config);
        let n = tmp_gate.num_limbs;
        for i in 0..(2 * n - 1) {
            let wire_a = Target::wire(row, tmp_gate.a(i));
            self.connect(check_sum[i].0, wire_a);
        }

        let b: Vec<_> = (0..2 * n - 2)
            .map(|i| UXTarget(Target::wire(row, tmp_gate.b(i))))
            .collect();

        // range checks

        const CARRY_OVER_BASE: usize = 34;
        range_check_ux_circuit::<F, D, BITS>(self, x.value.limbs.clone());
        range_check_ux_circuit::<F, D, BITS>(self, y.value.limbs.clone());
        range_check_ux_circuit::<F, D, BITS>(self, r.clone());
        range_check_ux_circuit::<F, D, BITS>(self, q);
        range_check_ux_circuit::<F, D, BITS>(self, r.clone());
        range_check_ux_circuit::<F, D, CARRY_OVER_BASE>(self, b[0..8].to_vec());
        range_check_ux_circuit::<F, D, CARRY_OVER_BASE>(self, b[8..].to_vec());

        let r_bigint = BigUintTarget { limbs: r };
        self.biguint_to_nonnative(&r_bigint, range_check)
    }

    fn mul_many_nonnative<FF: PrimeField>(
        &mut self,
        to_mul: &[NonNativeTarget<FF>],
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        if to_mul.len() == 1 {
            return to_mul[0].clone();
        }

        // Only range check the last result
        let mut range_check_curr = range_check;
        if to_mul.len() > 2 {
            range_check_curr = false;
        }
        let mut accumulator = self.mul_nonnative(&to_mul[0], &to_mul[1], range_check_curr);
        for i in 2..to_mul.len() {
            let t = &to_mul[i];
            if i + 1 == to_mul.len() {
                range_check_curr = range_check;
            }
            accumulator = self.mul_nonnative(&accumulator, t, range_check_curr);
        }
        accumulator
    }

    fn neg_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let zero_target = self.constant_biguint(&BigUint::zero());
        let zero_ff = self.biguint_to_nonnative(&zero_target, false);

        self.sub_nonnative(&zero_ff, x, range_check)
    }

    fn inv_nonnative<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let num_limbs = x.value.num_limbs();
        let inv_biguint = self.add_virtual_biguint_target(num_limbs);
        let div = self.add_virtual_biguint_target(num_limbs);

        self.add_simple_generator(NonNativeInverseGenerator::<F, D, FF> {
            x: x.clone(),
            inv: inv_biguint.clone(),
            div: div.clone(),
            _phantom: PhantomData,
        });

        let product = self.mul_biguint(&x.value, &inv_biguint);

        let modulus = self.constant_biguint(&FF::order());
        let mod_times_div = self.mul_biguint(&modulus, &div);
        let one = self.constant_biguint(&BigUint::one());
        let expected_product = self.add_biguint(&mod_times_div, &one);
        self.connect_biguint(&product, &expected_product);

        if range_check {
            let cmp = self.cmp_biguint(&inv_biguint, &modulus);
            let one = self.one();
            self.connect(cmp.target, one);
        }

        NonNativeTarget::<FF> {
            value: inv_biguint,
            _phantom: PhantomData,
        }
    }

    /// Returns `x % |FF|` as a `NonNativeTarget`.
    fn reduce<FF: Field>(&mut self, x: &BigUintTarget<BITS>) -> NonNativeTarget<FF> {
        let modulus = FF::order();
        let order_target = self.constant_biguint(&modulus);
        let value = self.rem_biguint(x, &order_target);

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    fn reduce_nonnative<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> NonNativeTarget<FF> {
        let x_biguint = self.nonnative_to_canonical_biguint(x);
        self.reduce(&x_biguint)
    }

    fn bool_to_nonnative<FF: Field>(&mut self, b: &BoolTarget) -> NonNativeTarget<FF> {
        let limbs = vec![UXTarget(b.target)];
        let value = BigUintTarget { limbs };

        NonNativeTarget {
            value,
            _phantom: PhantomData,
        }
    }

    // Split a nonnative field element to bits.
    fn split_nonnative_to_bits<FF: Field>(&mut self, x: &NonNativeTarget<FF>) -> Vec<BoolTarget> {
        let num_limbs = x.value.num_limbs();
        let mut result = Vec::with_capacity(num_limbs * BITS);

        for i in 0..num_limbs {
            let limb = x.value.get_limb(i);
            let bit_targets = self.split_le_base::<2>(limb.0, BITS);
            let mut bits: Vec<_> = bit_targets
                .iter()
                .map(|&t| BoolTarget::new_unsafe(t))
                .collect();

            result.append(&mut bits);
        }

        result
    }

    fn nonnative_conditional_neg<FF: PrimeField>(
        &mut self,
        x: &NonNativeTarget<FF>,
        b: BoolTarget,
        range_check: bool,
    ) -> NonNativeTarget<FF> {
        let not_b = self.not(b);
        let neg = self.neg_nonnative(x, false);
        let x_if_true = self.mul_nonnative_by_bool(&neg, b, false);
        let x_if_false = self.mul_nonnative_by_bool(x, not_b, false);

        self.add_nonnative(&x_if_true, &x_if_false, range_check)
    }
}

#[derive(Debug)]
struct NonNativeAdditionGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    a: NonNativeTarget<FF>,
    b: NonNativeTarget<FF>,
    sum: NonNativeTarget<FF>,
    overflow: BoolTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F, D>
    for NonNativeAdditionGenerator<F, D, FF>
{
    fn id(&self) -> String {
        "NonNativeAdditionGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.a
            .value
            .limbs
            .iter()
            .cloned()
            .chain(self.b.value.limbs.clone())
            .map(|l| l.0)
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let a = FF::from_noncanonical_biguint(witness.get_biguint_target(self.a.value.clone()));
        let b = FF::from_noncanonical_biguint(witness.get_biguint_target(self.b.value.clone()));
        let a_biguint = a.to_canonical_biguint();
        let b_biguint = b.to_canonical_biguint();
        let sum_biguint = a_biguint + b_biguint;
        let modulus = FF::order();
        let (overflow, sum_reduced) = if sum_biguint > modulus {
            (true, sum_biguint - modulus)
        } else {
            (false, sum_biguint)
        };

        out_buffer.set_biguint_target(&self.sum.value, &sum_reduced)?;
        out_buffer.set_bool_target(self.overflow, overflow)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target_vec(&self.a.to_target_vec())?;
        dst.write_target_vec(&self.b.to_target_vec())?;
        dst.write_target_vec(&self.sum.to_target_vec())?;
        dst.write_target_bool(self.overflow)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let a = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let b = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let sum = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let overflow = src.read_target_bool()?;

        Ok(Self {
            a,
            b,
            sum,
            overflow,
            _phantom: PhantomData,
        })
    }
}

#[derive(Debug)]
struct NonNativeMultipleAddsGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField>
{
    summands: Vec<NonNativeTarget<FF>>,
    sum: NonNativeTarget<FF>,
    overflow: UXTarget<BITS>,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F, D>
    for NonNativeMultipleAddsGenerator<F, D, FF>
{
    fn id(&self) -> String {
        "NonNativeMultipleAddsGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.summands
            .iter()
            .flat_map(|summand| summand.value.limbs.iter().map(|limb| limb.0))
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let summands: Vec<_> = self
            .summands
            .iter()
            .map(|summand| {
                FF::from_noncanonical_biguint(witness.get_biguint_target(summand.value.clone()))
            })
            .collect();
        let summand_biguints: Vec<_> = summands
            .iter()
            .map(|summand| summand.to_canonical_biguint())
            .collect();

        let sum_biguint = summand_biguints
            .iter()
            .fold(BigUint::zero(), |a, b| a + b.clone());

        let modulus = FF::order();
        let (overflow_biguint, sum_reduced) = sum_biguint.div_rem(&modulus);

        let overflow;
        if overflow_biguint.is_zero() {
            overflow = 0;
        } else {
            overflow = overflow_biguint.to_u64_digits()[0] as u32;
        }
        out_buffer.set_biguint_target(&self.sum.value, &sum_reduced)?;
        out_buffer.set_ux_target(self.overflow, overflow)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        let summands_len = self.summands.len();
        dst.write_usize(summands_len)?;
        self.summands
            .iter()
            .try_for_each(|summand| dst.write_target_vec(&summand.to_target_vec()))?;

        dst.write_target_vec(&self.sum.to_target_vec())?;
        dst.write_target(self.overflow.0)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let summands_len = src.read_usize()?;
        let summands: Vec<_> = (0..summands_len)
            .map(|_| {
                Ok::<_, IoError>(NonNativeTarget::<FF>::from_target_vec(
                    &src.read_target_vec()?,
                ))
            })
            .collect::<IoResult<_>>()?;
        let sum = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let overflow = UXTarget(src.read_target()?);

        Ok(Self {
            summands,
            sum,
            overflow,
            _phantom: PhantomData,
        })
    }
}

#[derive(Debug)]
struct NonNativeSubtractionGenerator<F: RichField + Extendable<D>, const D: usize, FF: Field> {
    a: NonNativeTarget<FF>,
    b: NonNativeTarget<FF>,
    diff: NonNativeTarget<FF>,
    overflow: BoolTarget,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F, D>
    for NonNativeSubtractionGenerator<F, D, FF>
{
    fn id(&self) -> String {
        "NonNativeSubtractionGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.a
            .value
            .limbs
            .iter()
            .cloned()
            .chain(self.b.value.limbs.clone())
            .map(|l| l.0)
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let a = FF::from_noncanonical_biguint(witness.get_biguint_target(self.a.value.clone()));
        let b = FF::from_noncanonical_biguint(witness.get_biguint_target(self.b.value.clone()));
        let a_biguint = a.to_canonical_biguint();
        let b_biguint = b.to_canonical_biguint();

        let modulus = FF::order();
        let (diff_biguint, overflow) = if a_biguint >= b_biguint {
            (a_biguint - b_biguint, false)
        } else {
            (modulus + a_biguint - b_biguint, true)
        };
        out_buffer.set_biguint_target(&self.diff.value, &diff_biguint)?;
        out_buffer.set_bool_target(self.overflow, overflow)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target_vec(&self.a.to_target_vec())?;
        dst.write_target_vec(&self.b.to_target_vec())?;
        dst.write_target_vec(&self.diff.to_target_vec())?;
        dst.write_target_bool(self.overflow)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let a = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let b = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let diff = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let overflow = src.read_target_bool()?;

        Ok(Self {
            a,
            b,
            diff,
            overflow,
            _phantom: PhantomData,
        })
    }
}

#[derive(Debug)]
struct NonNativeInverseGenerator<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> {
    x: NonNativeTarget<FF>,
    inv: BigUintTarget<BITS>,
    div: BigUintTarget<BITS>,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize, FF: PrimeField> SimpleGenerator<F, D>
    for NonNativeInverseGenerator<F, D, FF>
{
    fn id(&self) -> String {
        "NonNativeInverseGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.x.value.limbs.iter().map(|&l| l.0).collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let x = FF::from_noncanonical_biguint(witness.get_biguint_target(self.x.value.clone()));
        let inv = x.inverse();

        let x_biguint = x.to_canonical_biguint();
        let inv_biguint = inv.to_canonical_biguint();
        let prod = x_biguint * &inv_biguint;
        let modulus = FF::order();
        let (div, _rem) = prod.div_rem(&modulus);
        out_buffer.set_biguint_target(&self.div, &div)?;
        out_buffer.set_biguint_target(&self.inv, &inv_biguint)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target_vec(&self.x.to_target_vec())?;
        dst.write_target_vec(&self.inv.to_target_vec())?;
        dst.write_target_vec(&self.div.to_target_vec())
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let x = NonNativeTarget::from_target_vec(&src.read_target_vec()?);
        let inv = BigUintTarget::from_target_vec(&src.read_target_vec()?);
        let div = BigUintTarget::from_target_vec(&src.read_target_vec()?);

        Ok(Self {
            x,
            inv,
            div,
            _phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::secp256k1_base::Secp256K1Base;
    use plonky2::field::types::{Field, PrimeField, Sample};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use crate::gadgets::nonnative::CircuitBuilderNonNative;

    #[test]
    fn test_nonnative_add() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let sum_ff = x_ff + y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);
        let sum = builder.add_nonnative(&x, &y, true);

        let sum_expected = builder.constant_nonnative(sum_ff);
        builder.connect_nonnative(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_many_adds() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let a_ff = FF::rand();
        let b_ff = FF::rand();
        let c_ff = FF::rand();
        let d_ff = FF::rand();
        let e_ff = FF::rand();
        let f_ff = FF::rand();
        let g_ff = FF::rand();
        let h_ff = FF::rand();
        let sum_ff = a_ff + b_ff + c_ff + d_ff + e_ff + f_ff + g_ff + h_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = builder.constant_nonnative(a_ff);
        let b = builder.constant_nonnative(b_ff);
        let c = builder.constant_nonnative(c_ff);
        let d = builder.constant_nonnative(d_ff);
        let e = builder.constant_nonnative(e_ff);
        let f = builder.constant_nonnative(f_ff);
        let g = builder.constant_nonnative(g_ff);
        let h = builder.constant_nonnative(h_ff);
        let all = [a, b, c, d, e, f, g, h];
        let sum = builder.add_many_nonnative(&all, true);

        let sum_expected = builder.constant_nonnative(sum_ff);
        builder.connect_nonnative(&sum, &sum_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_sub() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let x_ff = FF::rand();
        let mut y_ff = FF::rand();
        while y_ff.to_canonical_biguint() > x_ff.to_canonical_biguint() {
            y_ff = FF::rand();
        }
        let diff_ff = x_ff - y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);
        let diff = builder.sub_nonnative(&x, &y, true);

        let diff_expected = builder.constant_nonnative(diff_ff);
        builder.connect_nonnative(&diff, &diff_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_mul() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let n = 10;
        let x_ff = FF::rand();
        let y_ff = FF::rand();
        let mut product_ff = x_ff * y_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let y = builder.constant_nonnative(y_ff);

        let mut product = builder.mul_nonnative(&x, &y, true);
        let mut product_expected = builder.constant_nonnative(product_ff);

        for _ in 0..n {
            let z_ff = FF::rand();
            let z = builder.constant_nonnative(z_ff);
            product_ff = product_ff * z_ff;
            product = builder.mul_nonnative(&product, &z, true);
            product_expected = builder.constant_nonnative(product_ff);
        }
        builder.connect_nonnative(&product, &product_expected);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_neg() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let neg_x_ff = -x_ff;

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let neg_x = builder.neg_nonnative(&x, true);

        let neg_x_expected = builder.constant_nonnative(neg_x_ff);
        builder.connect_nonnative(&neg_x, &neg_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    fn test_nonnative_inv() -> Result<()> {
        type FF = Secp256K1Base;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let x_ff = FF::rand();
        let inv_x_ff = x_ff.inverse();

        let config = CircuitConfig::standard_ecc_config();
        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.constant_nonnative(x_ff);
        let inv_x = builder.inv_nonnative(&x, true);

        let inv_x_expected = builder.constant_nonnative(inv_x_ff);
        builder.connect_nonnative(&inv_x, &inv_x_expected);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }
}
