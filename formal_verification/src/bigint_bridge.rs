//! The one place where Verno crosses the `num-bigint` major-version boundary.
//!
//! Noir `v1.0.0-beta.26` is built on `num-bigint 0.5`. Verno is on `0.4`, and so is the
//! Verus `vir` crate it links and hands `BigInt`s to. Cargo resolves the two majors side by
//! side without complaint, but their `BigInt`/`BigUint` types are unrelated to the
//! compiler, so any value that comes out of a Noir API on `0.5` has to be rebuilt before it
//! can be used with `vir`.
//!
//! VN-M1 §6 weighed three ways to close this: convert at the boundary, move Verno to `0.5`
//! and convert at the `vir` edge instead, or move the Verus pin forward to a revision on
//! `0.5`. Converting here is the cheapest and is the only one of the three that leaves the
//! Verus pin — and therefore the serialised `Krate` that `venir` must agree on — untouched.
//!
//! Note that not everything that looks like it crosses the boundary actually does:
//! `FieldElement::into_repr()` yields an `ark_ff` field whose `Into<BigUint>` comes from
//! `ark-ff`, which is itself on `num-bigint 0.4`. Those conversions land on Verno's side
//! already and need nothing. Only values produced by `num-bigint`-typed Noir APIs — of
//! which `AcirField::modulus()` is the one Verno reads — need this module.

use acvm::{AcirField, FieldElement};
use num_bigint::{BigInt, BigUint, Sign};

/// The Noir field modulus `p`, as a `num-bigint 0.4` `BigUint`.
///
/// `AcirField::modulus()` returns a `num-bigint 0.5` `BigUint`; the value is re-encoded
/// through big-endian bytes, which both majors agree on.
pub fn field_modulus() -> BigUint {
    BigUint::from_bytes_be(&FieldElement::modulus().to_bytes_be())
}

/// The Noir field modulus `p`, as a `num-bigint 0.4` `BigInt`. Always positive.
pub fn field_modulus_as_bigint() -> BigInt {
    BigInt::from_biguint(Sign::Plus, field_modulus())
}

/// A field element's canonical representative in `[0, p)`, as a `num-bigint 0.4` `BigUint`.
pub fn field_to_biguint(field: &FieldElement) -> BigUint {
    BigUint::from_bytes_be(&field.to_be_bytes())
}

/// Re-encodes one of Verno's `BigInt`s as the `num-bigint 0.5` `BigInt` Noir's own error
/// types now hold. Sign and magnitude are preserved exactly; only the type changes.
pub fn to_noir_bigint(value: &BigInt) -> num_bigint_noir::BigInt {
    let (sign, magnitude) = value.to_bytes_be();
    let sign = match sign {
        Sign::Minus => num_bigint_noir::Sign::Minus,
        Sign::NoSign => num_bigint_noir::Sign::NoSign,
        Sign::Plus => num_bigint_noir::Sign::Plus,
    };
    num_bigint_noir::BigInt::from_bytes_be(sign, &magnitude)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    /// The bytes-based re-encoding must agree with the value `ark-ff` produces on Verno's
    /// own `num-bigint` version, which is reachable via `into_repr`. If the two ever
    /// disagree, every constant Verno hands to Verus is wrong.
    #[test]
    fn field_to_biguint_agrees_with_ark_conversion() {
        for value in [0u128, 1, 2, 255, 256, u64::MAX as u128, u128::MAX] {
            let field = FieldElement::from(value);
            let via_bytes = field_to_biguint(&field);
            let via_ark: BigUint = field.into_repr().into();
            assert_eq!(via_bytes, via_ark, "mismatch for {value}");
        }
    }

    #[test]
    fn to_noir_bigint_round_trips_sign_and_magnitude() {
        for value in [0i64, 1, -1, 12345, -12345, i64::MAX, i64::MIN] {
            let ours = BigInt::from(value);
            assert_eq!(to_noir_bigint(&ours).to_string(), ours.to_string());
        }
    }

    #[test]
    fn modulus_is_positive_and_reduces_to_zero_in_the_field() {
        let modulus = field_modulus();
        assert!(!modulus.is_zero());
        // -1 in the field is p - 1, so (p - 1) + 1 == p.
        let minus_one = field_to_biguint(&-FieldElement::one());
        assert_eq!(minus_one + BigUint::from(1u32), modulus);
    }
}
