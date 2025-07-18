use alloc::vec::Vec;
use core::marker::PhantomData;
use num::integer::div_ceil;
use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_u32::gadgets::arithmetic_ux::{CircuitBuilderUX, UXTarget};

use crate::gadgets::biguint::BigUintTarget;
use crate::gadgets::nonnative::{NonNativeTarget, BITS};

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
        let mut bits: Vec<Target> = val.value
            .limbs
            .iter()
            .flat_map(|&l| self.split_le_base::<2>(l.0, BITS))
            .collect();
        while bits.len() % 4 !=0{
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
        let mut bits: Vec<Target> = val.value
            .limbs
            .iter()
            .flat_map(|&l| self.split_le_base::<2>(l.0, BITS))
            .collect();
        while bits.len() % 2 !=0{
            bits.push(self.zero());
        }
        let two = self.constant(F::from_canonical_usize(2));
        let combined_limbs = bits
            .iter()
            .tuples()
            .map(|(&a, &b)| {
                self.mul_add(b, two, a)
            })
            .collect();
        combined_limbs
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::secp256k1_scalar::Secp256K1Scalar;
    use plonky2::field::types::Sample;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use super::*;
    use crate::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};
    // #[ignore]
    // #[test]
    // fn test_split_nonnative() -> Result<()> {
    //     type FF = Secp256K1Scalar;
    //     const D: usize = 2;
    //     type C = PoseidonGoldilocksConfig;
    //     type F = <C as GenericConfig<D>>::F;

    //     let config = CircuitConfig::standard_ecc_config();
    //     let pw = PartialWitness::new();
    //     let mut builder = CircuitBuilder::<F, D>::new(config);

    //     let x = FF::rand();
    //     let x_target = builder.constant_nonnative(x);
    //     let split = builder.split_nonnative_to_4_bit_limbs(&x_target);
    //     let combined: NonNativeTarget<Secp256K1Scalar> =
    //         builder.recombine_nonnative_4_bit_limbs(split);
    //     builder.connect_nonnative(&x_target, &combined);

    //     let data = builder.build::<C>();
    //     let proof = data.prove(pw).unwrap();
    //     data.verify(proof)
    // }
}
