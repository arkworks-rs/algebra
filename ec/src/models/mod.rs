use ark_ff::{fields::BitIteratorBE, Field, PrimeField, SquareRootField, Zero};

pub mod bls12;
pub mod bn;
pub mod bw6;
pub mod mnt4;
pub mod mnt6;
pub mod short_weierstrass_jacobian;
pub mod twisted_edwards_extended;

/// Required for the is_in_correct_subgroup_assuming_on_curve() function in ModelParameters.
pub trait MultipliablePoint<R: Zero> {
    fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> R;
}

/// Model parameters for an elliptic curve.
pub trait ModelParameters: Send + Sync + 'static {
    type BaseField: Field + SquareRootField;
    type ScalarField: PrimeField + SquareRootField + Into<<Self::ScalarField as PrimeField>::BigInt>;

    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;

    /// Checks that the current point is in the prime order subgroup given
    /// the point on the curve.
    /// Requires type parameters G: the type of point passed in, and H: the type of
    /// point that results from multiplying G by a scalar.
    fn is_in_correct_subgroup_assuming_on_curve<G, H>(item: &G) -> bool
    where
        G: MultipliablePoint<H>,
        H: Zero,
    {
        item.mul_bits(BitIteratorBE::new(Self::ScalarField::characteristic()))
            .is_zero()
    }
}

/// Model parameters for a Short Weierstrass curve.
pub trait SWModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        if !Self::COEFF_B.is_zero() {
            let mut copy = *elem;
            copy += &Self::COEFF_B;
            return copy;
        }
        *elem
    }
}

/// Model parameters for a Twisted Edwards curve.
pub trait TEModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_D: Self::BaseField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    type MontgomeryModelParameters: MontgomeryModelParameters<BaseField = Self::BaseField>;

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }
}

/// Model parameters for a Montgomery curve.
pub trait MontgomeryModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;

    type TEModelParameters: TEModelParameters<BaseField = Self::BaseField>;
}
