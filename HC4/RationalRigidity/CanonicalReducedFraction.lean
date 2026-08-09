import HC4.Polynomial.RankThreeFractionBridge
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-!
# Canonical reduced fractions for the rank-three autonomous equation

The previous phases produced two honest rational functions over `Polynomial K`:

* the logarithmic source

      rho = E(phi) / phi,

  where `E(phi) = X * phi'`;

* the rank-three autonomous target

      R = N / D,

  with the explicit polynomials `rankThreeEtaNumeratorPolynomial` and
  `rankThreeEtaDenominatorPolynomial` from Phase 83.

Phase 82 is deliberately formulated for reduced numerator/denominator pairs.
Rather than choosing gcd representatives ourselves, this file uses Mathlib's
canonical `RatFunc.num` and `RatFunc.denom`.  Mathlib normalises the denominator
to be monic and proves that the two polynomials are coprime.

This file is therefore only a representation bridge.  It contains no pole
removal and no rank-three case split.  Those are downstream consequences.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The rational function represented by a polynomial pair `P / Q`. -/
def polynomialPairRatFunc (P Q : Polynomial K) : RatFunc K :=
  (algebraMap (Polynomial K) (RatFunc K)) P /
    (algebraMap (Polynomial K) (RatFunc K)) Q

/-- Mathlib's canonical reduced numerator for the fraction `P / Q`. -/
def canonicalReducedNumerator (P Q : Polynomial K) : Polynomial K :=
  (polynomialPairRatFunc P Q).num

/-- Mathlib's canonical monic reduced denominator for the fraction `P / Q`. -/
def canonicalReducedDenominator (P Q : Polynomial K) : Polynomial K :=
  (polynomialPairRatFunc P Q).denom

/-- The canonical reduced pair is coprime. -/
theorem canonicalReduced_isCoprime (P Q : Polynomial K) :
    IsCoprime (canonicalReducedNumerator P Q)
      (canonicalReducedDenominator P Q) := by
  exact RatFunc.isCoprime_num_denom (polynomialPairRatFunc P Q)

/-- The canonical reduced denominator is never the zero polynomial. -/
theorem canonicalReduced_denominator_ne_zero (P Q : Polynomial K) :
    canonicalReducedDenominator P Q ≠ 0 := by
  exact RatFunc.denom_ne_zero (polynomialPairRatFunc P Q)

/-- The canonical reduced denominator is monic. -/
theorem canonicalReduced_denominator_monic (P Q : Polynomial K) :
    (canonicalReducedDenominator P Q).Monic := by
  exact RatFunc.monic_denom (polynomialPairRatFunc P Q)

/-- The canonical reduced pair represents exactly the original rational
function. -/
theorem canonicalReduced_fraction_eq (P Q : Polynomial K) :
    (algebraMap (Polynomial K) (RatFunc K)) (canonicalReducedNumerator P Q) /
        (algebraMap (Polynomial K) (RatFunc K)) (canonicalReducedDenominator P Q) =
      polynomialPairRatFunc P Q := by
  exact RatFunc.num_div_denom (polynomialPairRatFunc P Q)

/-- The canonical denominator divides the raw polynomial denominator.  This is
useful when transferring support/degree information from the original
presentation. -/
theorem canonicalReduced_denominator_dvd (P Q : Polynomial K) :
    canonicalReducedDenominator P Q ∣ Q := by
  simpa [canonicalReducedDenominator, polynomialPairRatFunc] using
    (RatFunc.denom_div_dvd P Q)

/-- The logarithmic source rational function `rho = E(phi) / phi`. -/
def logarithmicSourceRatFunc (phi : Polynomial K) : RatFunc K :=
  polynomialPairRatFunc (HC4.Polynomial.eulerDerivative phi) phi

/-- Canonical reduced numerator of `rho = E(phi) / phi`. -/
def logarithmicSourceNumerator (phi : Polynomial K) : Polynomial K :=
  canonicalReducedNumerator (HC4.Polynomial.eulerDerivative phi) phi

/-- Canonical reduced denominator of `rho = E(phi) / phi`. -/
def logarithmicSourceDenominator (phi : Polynomial K) : Polynomial K :=
  canonicalReducedDenominator (HC4.Polynomial.eulerDerivative phi) phi

/-- The reduced logarithmic source pair is coprime. -/
theorem logarithmicSource_isCoprime (phi : Polynomial K) :
    IsCoprime (logarithmicSourceNumerator phi)
      (logarithmicSourceDenominator phi) := by
  exact canonicalReduced_isCoprime _ _

/-- The reduced logarithmic source denominator is nonzero. -/
theorem logarithmicSource_denominator_ne_zero (phi : Polynomial K) :
    logarithmicSourceDenominator phi ≠ 0 := by
  exact canonicalReduced_denominator_ne_zero _ _

/-- The reduced logarithmic source denominator is monic. -/
theorem logarithmicSource_denominator_monic (phi : Polynomial K) :
    (logarithmicSourceDenominator phi).Monic := by
  exact canonicalReduced_denominator_monic _ _

/-- The canonical logarithmic source pair represents `E(phi) / phi`. -/
theorem logarithmicSource_fraction_eq (phi : Polynomial K) :
    (algebraMap (Polynomial K) (RatFunc K)) (logarithmicSourceNumerator phi) /
        (algebraMap (Polynomial K) (RatFunc K)) (logarithmicSourceDenominator phi) =
      logarithmicSourceRatFunc phi := by
  exact canonicalReduced_fraction_eq _ _

/-- The reduced logarithmic source denominator divides `phi`. -/
theorem logarithmicSource_denominator_dvd (phi : Polynomial K) :
    logarithmicSourceDenominator phi ∣ phi := by
  exact canonicalReduced_denominator_dvd _ _

/-- The explicit rank-three target rational function `N / D` from Phase 83. -/
def rankThreeTargetRatFunc
    (v2 v3 v4 w1 w2 w3 w4 : K) : RatFunc K :=
  polynomialPairRatFunc
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      v2 v3 v4 w1 w2 w3 w4)
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      v2 v3 v4 w1 w2 w3 w4)

/-- Canonical reduced numerator of the rank-three autonomous target. -/
def rankThreeTargetNumerator
    (v2 v3 v4 w1 w2 w3 w4 : K) : Polynomial K :=
  canonicalReducedNumerator
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      v2 v3 v4 w1 w2 w3 w4)
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      v2 v3 v4 w1 w2 w3 w4)

/-- Canonical reduced denominator of the rank-three autonomous target. -/
def rankThreeTargetDenominator
    (v2 v3 v4 w1 w2 w3 w4 : K) : Polynomial K :=
  canonicalReducedDenominator
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      v2 v3 v4 w1 w2 w3 w4)
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      v2 v3 v4 w1 w2 w3 w4)

/-- The canonical rank-three target pair is coprime. -/
theorem rankThreeTarget_isCoprime
    (v2 v3 v4 w1 w2 w3 w4 : K) :
    IsCoprime
      (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4)
      (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4) := by
  exact canonicalReduced_isCoprime _ _

/-- The canonical rank-three target denominator is nonzero. -/
theorem rankThreeTarget_denominator_ne_zero
    (v2 v3 v4 w1 w2 w3 w4 : K) :
    rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 ≠ 0 := by
  exact canonicalReduced_denominator_ne_zero _ _

/-- The canonical rank-three target denominator is monic. -/
theorem rankThreeTarget_denominator_monic
    (v2 v3 v4 w1 w2 w3 w4 : K) :
    (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4).Monic := by
  exact canonicalReduced_denominator_monic _ _

/-- The canonical rank-three target pair represents the explicit Phase 83
rational function. -/
theorem rankThreeTarget_fraction_eq
    (v2 v3 v4 w1 w2 w3 w4 : K) :
    (algebraMap (Polynomial K) (RatFunc K))
          (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4) /
        (algebraMap (Polynomial K) (RatFunc K))
          (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4) =
      rankThreeTargetRatFunc v2 v3 v4 w1 w2 w3 w4 := by
  exact canonicalReduced_fraction_eq _ _

/-- The reduced rank-three target denominator divides the raw denominator
polynomial from Phase 83. -/
theorem rankThreeTarget_denominator_dvd
    (v2 v3 v4 w1 w2 w3 w4 : K) :
    rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 ∣
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 := by
  exact canonicalReduced_denominator_dvd _ _

end

end HC4.RationalRigidity
