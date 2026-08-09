import HC4.RationalRigidity.LogarithmicSourceRatFunc
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic

/-!
# Reduced target assembly for the rank-three autonomous equation

This file connects the concrete Phase 83 rank-three fraction equation to the
canonical reduced target pair from Phase 84.

The key point is that cancellation of common factors in the *raw target*
`N_raw / D_raw` is performed as an identity of rational functions, never by
pointwise cancellation at a scalar.  This preserves multiplicities at common
zeros and is exactly what is needed before the Phase 82 pole-removal theorem.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The Phase 83 raw numerator evaluated in `RatFunc K` is polynomial
substitution into the formal numerator polynomial. -/
theorem aeval_rankThreeEtaNumeratorPolynomial
    (v2 v3 v4 w1 w2 w3 w4 : K) (rho : RatFunc K) :
    Polynomial.aeval rho
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          v2 v3 v4 w1 w2 w3 w4) =
      HC4.Polynomial.rankThreeEtaNumerator
        (algebraMap K (RatFunc K) v2)
        (algebraMap K (RatFunc K) v3)
        (algebraMap K (RatFunc K) v4)
        (algebraMap K (RatFunc K) w1)
        (algebraMap K (RatFunc K) w2)
        (algebraMap K (RatFunc K) w3)
        (algebraMap K (RatFunc K) w4) rho := by
  simp [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
    HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum] <;> ring

/-- The analogous substitution identity for the Phase 83 raw denominator. -/
theorem aeval_rankThreeEtaDenominatorPolynomial
    (v2 v3 v4 w1 w2 w3 w4 : K) (rho : RatFunc K) :
    Polynomial.aeval rho
        (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          v2 v3 v4 w1 w2 w3 w4) =
      HC4.Polynomial.rankThreeEtaDenominator
        (algebraMap K (RatFunc K) v2)
        (algebraMap K (RatFunc K) v3)
        (algebraMap K (RatFunc K) v4)
        (algebraMap K (RatFunc K) w1)
        (algebraMap K (RatFunc K) w2)
        (algebraMap K (RatFunc K) w3)
        (algebraMap K (RatFunc K) w4) rho := by
  simp [HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
    HC4.Polynomial.rankThreeEtaDenominator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    HC4.Polynomial.rankThreeWeightedCofactorSum,
    HC4.Polynomial.rankThreeDirectionDefect] <;> ring

/-- The concrete rank-three autonomous equation, now expressed in the canonical
rational-function field `RatFunc K`. -/
def RankThreeRatFuncEquation
    (phi : Polynomial K)
    (v2 v3 v4 w1 w2 w3 w4 : K) : Prop :=
  let rho := logarithmicSourceRatFunc phi
  let eta := logarithmicSourceEtaRatFunc phi
  HC4.Polynomial.rankThreeEtaNumerator
      (algebraMap K (RatFunc K) v2)
      (algebraMap K (RatFunc K) v3)
      (algebraMap K (RatFunc K) v4)
      (algebraMap K (RatFunc K) w1)
      (algebraMap K (RatFunc K) w2)
      (algebraMap K (RatFunc K) w3)
      (algebraMap K (RatFunc K) w4) rho =
    eta * HC4.Polynomial.rankThreeEtaDenominator
      (algebraMap K (RatFunc K) v2)
      (algebraMap K (RatFunc K) v3)
      (algebraMap K (RatFunc K) v4)
      (algebraMap K (RatFunc K) w1)
      (algebraMap K (RatFunc K) w2)
      (algebraMap K (RatFunc K) w3)
      (algebraMap K (RatFunc K) w4) rho

/-- Transport the Phase 83 equation from the generic fraction field to
`RatFunc K`.  The reduced Phase 85 presentation of `eta` is substituted only
after the field-of-fractions transport. -/
theorem rankThree_ratFunc_equation_of_fraction_equation
    {phi : Polynomial K} (hphi : phi ≠ 0)
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : HC4.Polynomial.RankThreeFractionEquation
      phi v2 v3 v4 w1 w2 w3 w4) :
    RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4 := by
  let e : FractionRing (Polynomial K) ≃ₐ[Polynomial K] RatFunc K :=
    FractionRing.algEquiv (Polynomial K) (RatFunc K)
  have hmapped := congrArg e hEq
  unfold RankThreeRatFuncEquation
  rw [logarithmicSourceEtaRatFunc_eq_raw phi hphi]
  simpa [HC4.Polynomial.RankThreeFractionEquation,
    logarithmicSourceRatFunc, polynomialPairRatFunc, e,
    HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeEtaDenominator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    HC4.Polynomial.rankThreeWeightedCofactorSum,
    HC4.Polynomial.rankThreeDirectionDefect] using hmapped

/-- The canonical target numerator/denominator satisfy the ordinary polynomial
cross identity with the raw Phase 83 presentation. -/
theorem rankThreeTarget_cross_identity
    (v2 v3 v4 w1 w2 w3 w4 : K)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0) :
    rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4 *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          v2 v3 v4 w1 w2 w3 w4 =
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          v2 v3 v4 w1 w2 w3 w4 *
        rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 := by
  have h :
      (rankThreeTargetRatFunc v2 v3 v4 w1 w2 w3 w4).num *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            v2 v3 v4 w1 w2 w3 w4 =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            v2 v3 v4 w1 w2 w3 w4 *
          (rankThreeTargetRatFunc v2 v3 v4 w1 w2 w3 w4).denom := by
    apply
      (RatFunc.num_mul_eq_mul_denom_iff
        (x := rankThreeTargetRatFunc v2 v3 v4 w1 w2 w3 w4)
        hRawD).2
    simp [rankThreeTargetRatFunc, polynomialPairRatFunc]
  simpa [rankThreeTargetNumerator, rankThreeTargetDenominator,
    canonicalReducedNumerator, canonicalReducedDenominator] using h

/-- The scalar-form rank-three equation is exactly the raw polynomial
substitution equation. -/
theorem rankThree_raw_aeval_equation_of_ratFunc_equation
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4) :
    Polynomial.aeval (logarithmicSourceRatFunc phi)
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          v2 v3 v4 w1 w2 w3 w4) =
      logarithmicSourceEtaRatFunc phi *
        Polynomial.aeval (logarithmicSourceRatFunc phi)
          (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            v2 v3 v4 w1 w2 w3 w4) := by
  simpa [RankThreeRatFuncEquation,
    aeval_rankThreeEtaNumeratorPolynomial,
    aeval_rankThreeEtaDenominatorPolynomial] using hEq

/-- After canonical target reduction, the same autonomous equation holds with
its coprime numerator and denominator.  The proof evaluates the polynomial
cross identity in the *rational function field* and cancels the raw target
denominator there.  No pointwise cancellation is used. -/
theorem rankThree_reduced_target_equation
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hRhoTrans : Transcendental K (logarithmicSourceRatFunc phi)) :
    Polynomial.aeval (logarithmicSourceRatFunc phi)
        (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4) =
      logarithmicSourceEtaRatFunc phi *
        Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4) := by
  let rho := logarithmicSourceRatFunc phi
  let eta := logarithmicSourceEtaRatFunc phi
  let rawN := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    v2 v3 v4 w1 w2 w3 w4
  let rawD := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    v2 v3 v4 w1 w2 w3 w4
  let A := rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4
  let B := rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4

  have hRaw : Polynomial.aeval rho rawN = eta * Polynomial.aeval rho rawD := by
    simpa [rho, eta, rawN, rawD] using
      rankThree_raw_aeval_equation_of_ratFunc_equation hEq

  have hRawDEval : Polynomial.aeval rho rawD ≠ 0 := by
    intro hz
    have hzero : rawD = 0 := (transcendental_iff.mp hRhoTrans) rawD hz
    exact hRawD (by simpa [rawD] using hzero)

  have hPoly : A * rawD = rawN * B := by
    simpa [A, B, rawN, rawD] using
      rankThreeTarget_cross_identity
        v2 v3 v4 w1 w2 w3 w4 hRawD
  have hAeval := congrArg (Polynomial.aeval rho) hPoly
  simp only [map_mul] at hAeval

  apply mul_right_cancel₀ hRawDEval
  calc
    Polynomial.aeval rho A * Polynomial.aeval rho rawD =
        Polynomial.aeval rho rawN * Polynomial.aeval rho B := hAeval
    _ = (eta * Polynomial.aeval rho B) * Polynomial.aeval rho rawD := by
      rw [hRaw]
      ring

/-- Concrete finite-pole removal for the rank-three target.  The only datum
not manufactured automatically by the previous phases is the single infinity
cleared identity. -/
theorem rankThreeTargetDenominator_constant_of_ratFunc_equation
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hRhoTrans : Transcendental K (logarithmicSourceRatFunc phi))
    (hRhoDegree : 0 < (logarithmicSourceRatFunc phi).denom.natDegree)
    (etaInfinity : K)
    (hInfinityClear :
      (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4).eval
          (rationalInfinityValue
            (logarithmicSourceRatFunc phi).num
            (logarithmicSourceRatFunc phi).denom) =
        etaInfinity *
          (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4).eval
            (rationalInfinityValue
              (logarithmicSourceRatFunc phi).num
              (logarithmicSourceRatFunc phi).denom)) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  apply constant_target_denominator_of_ratFunc_identity
    hRhoDegree
    (rankThreeTarget_isCoprime v2 v3 v4 w1 w2 w3 w4)
    (fun x hx => logarithmicSourceEtaRatFunc_regularAt phi hx)
    (rankThree_reduced_target_equation hEq hRawD hRhoTrans)
    etaInfinity
    hInfinityClear

/-- End-to-end denominator removal starting from the Phase 83 generic
fraction-field equation.  All finite-chart hypotheses are manufactured by
Phases 84--86; only the single infinity certificate remains explicit. -/
theorem rankThreeTargetDenominator_constant_of_fraction_equation
    [IsAlgClosed K]
    {phi : Polynomial K} (hphi : phi ≠ 0)
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : HC4.Polynomial.RankThreeFractionEquation
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hRhoTrans : Transcendental K (logarithmicSourceRatFunc phi))
    (hRhoDegree : 0 < (logarithmicSourceRatFunc phi).denom.natDegree)
    (etaInfinity : K)
    (hInfinityClear :
      (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4).eval
          (rationalInfinityValue
            (logarithmicSourceRatFunc phi).num
            (logarithmicSourceRatFunc phi).denom) =
        etaInfinity *
          (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4).eval
            (rationalInfinityValue
              (logarithmicSourceRatFunc phi).num
              (logarithmicSourceRatFunc phi).denom)) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  exact rankThreeTargetDenominator_constant_of_ratFunc_equation
    (rankThree_ratFunc_equation_of_fraction_equation hphi hEq)
    hRawD hRhoTrans hRhoDegree etaInfinity hInfinityClear

/-- Same denominator-removal endpoint starting directly from vanishing of the
substituted rank-three logarithmic core. -/
theorem rankThreeTargetDenominator_constant_of_core_det_zero
    [IsAlgClosed K]
    {phi : Polynomial K} (hphi : phi ≠ 0)
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hdet : HC4.Polynomial.RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hRhoTrans : Transcendental K (logarithmicSourceRatFunc phi))
    (hRhoDegree : 0 < (logarithmicSourceRatFunc phi).denom.natDegree)
    (etaInfinity : K)
    (hInfinityClear :
      (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4).eval
          (rationalInfinityValue
            (logarithmicSourceRatFunc phi).num
            (logarithmicSourceRatFunc phi).denom) =
        etaInfinity *
          (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4).eval
            (rationalInfinityValue
              (logarithmicSourceRatFunc phi).num
              (logarithmicSourceRatFunc phi).denom)) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  apply rankThreeTargetDenominator_constant_of_fraction_equation
    hphi
    (HC4.Polynomial.rankThree_fraction_equation_of_core_det_zero hdet)
    hRawD hRhoTrans hRhoDegree etaInfinity hInfinityClear

end

end HC4.RationalRigidity
