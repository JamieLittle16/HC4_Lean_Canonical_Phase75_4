import HC4.Polynomial.RankThreeLogHessian
import HC4.Polynomial.LogarithmicInitialSlope
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# Fraction-field bridge for the rank-three autonomous equation

Phase 76 proved the scalar logarithmic-Hessian identity

    det(core) = N(rho) - eta * D(rho).

This file performs the concrete substitution used in the manuscript:

    rho = E(phi) / phi,
    eta = A(phi) / phi^2,

inside the fraction field of `K[X]`, where

    E(phi) = X phi',
    A(phi) = X E(phi)' * phi - E(phi)^2.

The point of the file is deliberately modest but important.  It identifies
vanishing of the actual rank-three logarithmic core with an autonomous
fraction equation for the honest polynomial `phi`, without dividing by the
rank-three target denominator.  Thus no nonvanishing assumption on that
denominator is hidden in the bridge.

We also package the numerator and denominator of the rank-three autonomous
right-hand side as ordinary polynomials in a formal variable and verify that
evaluation recovers the scalar formula.  These are the target polynomials
used by the reduced-fraction / pole-removal phases.
-/

namespace HC4.Polynomial

noncomputable section

/-- Polynomial in the formal variable `rho` representing the numerator of
 the rank-three autonomous right-hand side. -/
def rankThreeEtaNumeratorPolynomial
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 : K) : Polynomial K :=
  rankThreeEtaNumerator (K := Polynomial K)
    (Polynomial.C v2) (Polynomial.C v3) (Polynomial.C v4)
    (Polynomial.C w1) (Polynomial.C w2)
    (Polynomial.C w3) (Polynomial.C w4)
    Polynomial.X

/-- Polynomial in the formal variable `rho` representing the denominator of
 the rank-three autonomous right-hand side. -/
def rankThreeEtaDenominatorPolynomial
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 : K) : Polynomial K :=
  rankThreeEtaDenominator (K := Polynomial K)
    (Polynomial.C v2) (Polynomial.C v3) (Polynomial.C v4)
    (Polynomial.C w1) (Polynomial.C w2)
    (Polynomial.C w3) (Polynomial.C w4)
    Polynomial.X

/-- Evaluation of the formal numerator polynomial is the scalar numerator. -/
theorem eval_rankThreeEtaNumeratorPolynomial
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) :
    Polynomial.eval rho
        (rankThreeEtaNumeratorPolynomial v2 v3 v4 w1 w2 w3 w4) =
      rankThreeEtaNumerator v2 v3 v4 w1 w2 w3 w4 rho := by
  simp [rankThreeEtaNumeratorPolynomial, rankThreeEtaNumerator,
    rankThreeLogProduct, rankThreeLogSum] <;> ring

/-- Evaluation of the formal denominator polynomial is the scalar denominator. -/
theorem eval_rankThreeEtaDenominatorPolynomial
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) :
    Polynomial.eval rho
        (rankThreeEtaDenominatorPolynomial v2 v3 v4 w1 w2 w3 w4) =
      rankThreeEtaDenominator v2 v3 v4 w1 w2 w3 w4 rho := by
  simp [rankThreeEtaDenominatorPolynomial, rankThreeEtaDenominator,
    rankThreeLogProduct, rankThreeLogSum, rankThreeWeightedCofactorSum,
    rankThreeDirectionDefect] <;> ring

/-- The rank-three logarithmic core after substituting the honest logarithmic
 quantities of a polynomial `phi` in the fraction field of `K[X]`. -/
def RankThreeFractionCoreDetZero
    {K : Type*} [Field K]
    (phi : Polynomial K)
    (v2 v3 v4 w1 w2 w3 w4 : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p := ι phi
  let E := ι (eulerDerivative phi)
  let A := ι (logarithmicEtaNumerator phi)
  (rankThreeLogHessianCore
      (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
      (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
      (ι (Polynomial.C w3)) (ι (Polynomial.C w4))
      (E / p) (A / p^2)).det = 0

/-- The autonomous rank-three fraction equation obtained after the same
 substitution.  It is kept in cross-multiplied scalar form

    N(rho) = eta * D(rho),

so no target-denominator nonvanishing assumption is required. -/
def RankThreeFractionEquation
    {K : Type*} [Field K]
    (phi : Polynomial K)
    (v2 v3 v4 w1 w2 w3 w4 : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p := ι phi
  let E := ι (eulerDerivative phi)
  let A := ι (logarithmicEtaNumerator phi)
  let rho := E / p
  let eta := A / p^2
  rankThreeEtaNumerator
      (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
      (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
      (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho =
    eta * rankThreeEtaDenominator
      (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
      (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
      (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho

/-- Vanishing of the substituted rank-three logarithmic core gives the exact
 autonomous fraction equation.  This is the denominator-free form of the
 manuscript step `det = 0 => t rho' = R(rho)`. -/
theorem rankThree_fraction_equation_of_core_det_zero
    {K : Type*} [Field K]
    {phi : Polynomial K}
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hdet : RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4) :
    RankThreeFractionEquation phi v2 v3 v4 w1 w2 w3 w4 := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p : F := ι phi
  let E : F := ι (eulerDerivative phi)
  let A : F := ι (logarithmicEtaNumerator phi)
  let rho : F := E / p
  let eta : F := A / p^2

  have hdet' :
      (rankThreeLogHessianCore
        (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
        (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
        (ι (Polynomial.C w3)) (ι (Polynomial.C w4))
        rho eta).det = 0 := by
    simpa [RankThreeFractionCoreDetZero, F, ι, p, E, A, rho, eta] using hdet

  have hzero :
      rankThreeEtaNumerator
          (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
          (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
          (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho -
        eta * rankThreeEtaDenominator
          (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
          (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
          (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho = 0 := by
    rw [← det_rankThreeLogHessianCore]
    exact hdet'

  have heq :
      rankThreeEtaNumerator
          (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
          (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
          (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho =
        eta * rankThreeEtaDenominator
          (ι (Polynomial.C v2)) (ι (Polynomial.C v3)) (ι (Polynomial.C v4))
          (ι (Polynomial.C w1)) (ι (Polynomial.C w2))
          (ι (Polynomial.C w3)) (ι (Polynomial.C w4)) rho :=
    sub_eq_zero.mp hzero

  simpa [RankThreeFractionEquation, F, ι, p, E, A, rho, eta] using heq

end

end HC4.Polynomial
