use core::num::traits::{One, Zero};
use fraction_verification::abs::Abs;


#[derive(Copy, Drop, Hash, Serde)]
pub struct Fraction {
    numerator: i128,
    denominator: u128,
}


#[generate_trait]
pub impl FractionlImpl of FractionTrait {
    fn new(numerator: i128, denominator: u128) -> Fraction {
        /// TODO : consider  reducing a fraction to its simplest form.
        assert(denominator != 0, 'Denominator must be non-zero');
        Fraction { numerator, denominator }
    }

    fn numerator(self: @Fraction) -> i128 {
        *self.numerator
    }

    fn denominator(self: @Fraction) -> u128 {
        *self.denominator
    }
}

impl FractionNeg of Neg<Fraction> {
    fn neg(a: Fraction) -> Fraction {
        Fraction { numerator: -a.numerator, denominator: a.denominator }
    }
}

impl FractionZero of Zero<Fraction> {
    fn zero() -> Fraction {
        Fraction { numerator: 0, denominator: 1 }
    }

    fn is_zero(self: @Fraction) -> bool {
        *self.numerator == 0
    }

    fn is_non_zero(self: @Fraction) -> bool {
        !self.is_zero()
    }
}

impl FractionOne of One<Fraction> {
    fn one() -> Fraction {
        Fraction { numerator: 1, denominator: 1 }
    }

    fn is_one(self: @Fraction) -> bool {
        let numerator: i128 = *self.numerator;
        let denominator: u128 = *self.denominator;
        if numerator < 0 {
            return false;
        }
        numerator.abs() == denominator
    }
    /// Returns `false` if `self` is equal to the multiplicative identity.
    fn is_non_one(self: @Fraction) -> bool {
        !self.is_one()
    }
}

impl FractionPartialEq of PartialEq<Fraction> {
    fn eq(lhs: @Fraction, rhs: @Fraction) -> bool {
        (lhs <= rhs) && (lhs >= rhs)
    }
}

impl FractionPartialOrd of PartialOrd<Fraction> {
    fn lt(lhs: Fraction, rhs: Fraction) -> bool {
        /// denote lhs as a/b and rhs as c/d
        /// case a <= 0 and c > 0
        if lhs.numerator <= 0 && rhs.numerator > 0 {
            return true;
        }
        /// case a >= 0 and c <= 0
        if lhs.numerator >= 0 && rhs.numerator <= 0 {
            return false;
        }

        // case a < 0 and c = 0
        if lhs.numerator < 0 && rhs.numerator == 0 {
            return true;
        }

        /// from now c != 0 and a != 0, a and c have the same sign.
        /// left = |a| * d
        let mut left: u256 = lhs.numerator.abs().into();
        left = left * rhs.denominator.into();

        /// right = |c| * b
        let mut right: u256 = rhs.numerator.abs().into();
        right = right * lhs.denominator.into();

        /// case a > 0 and c > 0
        if lhs.numerator > 0 {
            return left < right;
        }
        /// The remaining case is a < 0 and c < 0
        left > right
    }
}

mod fv {
    use core::num::traits::{One, Zero};
    use super::*;

    fn fraction_parial_ord_test() {
        let f1 = FractionTrait::new(numerator: 1, denominator: 2);
        let f2 = FractionTrait::new(numerator: 1, denominator: 3);
        assert(f1 > f2, 'fail');
    }
}

