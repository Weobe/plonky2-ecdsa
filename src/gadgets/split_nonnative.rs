use crate::gadgets::nonnative::{NonNativeTarget, BITS};
use alloc::vec::Vec;
use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

pub trait CircuitBuilderSplit<F: RichField + Extendable<D>, const D: usize> {
    fn split_nonnative_to_4_bit_limbs<FF: Field>(
        &mut self,
        val: &NonNativeTarget<FF>,
    ) -> Vec<Target>;

    fn split_nonnative_to_2_bit_limbs<FF: Field>(
        &mut self,
        val: &NonNativeTarget<FF>,
    ) -> Vec<Target>;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderSplit<F, D>
    for CircuitBuilder<F, D>
{
    fn split_nonnative_to_4_bit_limbs<FF: Field>(
        &mut self,
        val: &NonNativeTarget<FF>,
    ) -> Vec<Target> {
        let mut bits: Vec<Target> = val
            .value
            .limbs
            .iter()
            .flat_map(|&l| self.split_le_base::<2>(l.0, BITS))
            .collect();
        while bits.len() % 4 != 0 {
            bits.push(self.zero());
        }
        let two = self.constant(F::from_canonical_usize(2));
        let four = self.constant(F::from_canonical_usize(4));
        let combined_limbs = bits
            .iter()
            .tuples()
            .map(|(&a, &b, &c, &d)| {
                let lower = self.mul_add(b, two, a);
                let upper = self.mul_add(d, two, c);
                self.mul_add(upper, four, lower)
            })
            .collect();
        combined_limbs
    }

    fn split_nonnative_to_2_bit_limbs<FF: Field>(
        &mut self,
        val: &NonNativeTarget<FF>,
    ) -> Vec<Target> {
        let mut bits: Vec<Target> = val
            .value
            .limbs
            .iter()
            .flat_map(|&l| self.split_le_base::<2>(l.0, BITS))
            .collect();
        while bits.len() % 2 != 0 {
            bits.push(self.zero());
        }
        let two = self.constant(F::from_canonical_usize(2));
        let combined_limbs = bits
            .iter()
            .tuples()
            .map(|(&a, &b)| self.mul_add(b, two, a))
            .collect();
        combined_limbs
    }
}
