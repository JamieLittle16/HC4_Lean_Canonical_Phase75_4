import HC4.Polynomial.LogHessianMoments
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Rank-three logarithmic Hessian bridge

This file formalises the cleared algebraic form of manuscript equation (6)
for a line leaving a rank-three monomial.

For

    v = (0,v₂,v₃,v₄),
    w = (w₁,w₂,w₃,w₄),
    e = v + ρ w,

and logarithmic second-derivative parameter `η`, the core matrix is

    e eᵀ + η w wᵀ - diag(e).

The determinant identity is recorded without divisions:

    det(core)
      = P(1-S) - η ((1-S) Σ + k² P),

where `P = ∏ eᵢ`, `S = ∑ eᵢ`, `k = -∑ wᵢ`, and
`Σ = ∑ wᵢ² ∏_{j≠i} eⱼ`.

This is exactly the denominator-cleared version of the manuscript's
rank-three logarithmic-Hessian formula.  It plugs directly into the generic
line-moment machinery already verified for the complementary-edge branch.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Base exponent of a rank-three endpoint, after ordering the omitted
coordinate first. -/
def rankThreeLogBaseExponent
    {K : Type*} [Zero K]
    (v2 v3 v4 : K) : Fin 4 → K :=
  ![0, v2, v3, v4]

/-- Direction of the exponent line leaving the rank-three endpoint. -/
def rankThreeLogDirection
    {K : Type*}
    (w1 w2 w3 w4 : K) : Fin 4 → K :=
  ![w1, w2, w3, w4]

/-- Affine logarithmic exponent `e = v + ρw`. -/
def rankThreeLogExponent
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : Fin 4 → K :=
  ![rho * w1,
    v2 + rho * w2,
    v3 + rho * w3,
    v4 + rho * w4]

/-- The logarithmic Hessian core `e eᵀ + η w wᵀ - diag(e)`. -/
def rankThreeLogHessianCore
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho eta : K) :
    Matrix (Fin 4) (Fin 4) K :=
  let e := rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho
  let w := rankThreeLogDirection w1 w2 w3 w4
  Matrix.of fun i j =>
    e i * e j + eta * (w i * w j) - if i = j then e i else 0

/-- Product `P = ∏ eᵢ`, written explicitly to keep the determinant identity
friendly to ring normalisation. -/
def rankThreeLogProduct
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : K :=
  (rho * w1) *
    (v2 + rho * w2) *
    (v3 + rho * w3) *
    (v4 + rho * w4)

/-- Sum `S = ∑ eᵢ`. -/
def rankThreeLogSum
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : K :=
  rho * w1 +
    (v2 + rho * w2) +
    (v3 + rho * w3) +
    (v4 + rho * w4)

/-- Manuscript `k = -∑wᵢ`. -/
def rankThreeDirectionDefect
    {K : Type*} [CommRing K]
    (w1 w2 w3 w4 : K) : K :=
  -(w1 + w2 + w3 + w4)

/-- Cleared version of `P * ∑ wᵢ²/eᵢ`. -/
def rankThreeWeightedCofactorSum
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : K :=
  w1^2 *
      (v2 + rho * w2) * (v3 + rho * w3) * (v4 + rho * w4) +
    w2^2 *
      (rho * w1) * (v3 + rho * w3) * (v4 + rho * w4) +
    w3^2 *
      (rho * w1) * (v2 + rho * w2) * (v4 + rho * w4) +
    w4^2 *
      (rho * w1) * (v2 + rho * w2) * (v3 + rho * w3)

/-- Numerator of the autonomous rational equation obtained from zero Hessian. -/
def rankThreeEtaNumerator
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : K :=
  rankThreeLogProduct v2 v3 v4 w1 w2 w3 w4 rho *
    (1 - rankThreeLogSum v2 v3 v4 w1 w2 w3 w4 rho)

/-- Denominator of the autonomous rational equation obtained from zero Hessian. -/
def rankThreeEtaDenominator
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) : K :=
  (1 - rankThreeLogSum v2 v3 v4 w1 w2 w3 w4 rho) *
      rankThreeWeightedCofactorSum v2 v3 v4 w1 w2 w3 w4 rho +
    rankThreeDirectionDefect w1 w2 w3 w4 ^ 2 *
      rankThreeLogProduct v2 v3 v4 w1 w2 w3 w4 rho

set_option maxHeartbeats 4000000

/-- Cleared form of manuscript equation (6). -/
theorem det_rankThreeLogHessianCore
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho eta : K) :
    (rankThreeLogHessianCore
      v2 v3 v4 w1 w2 w3 w4 rho eta).det =
      rankThreeEtaNumerator v2 v3 v4 w1 w2 w3 w4 rho -
        eta * rankThreeEtaDenominator v2 v3 v4 w1 w2 w3 w4 rho := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [rankThreeLogHessianCore, rankThreeLogExponent,
    rankThreeLogDirection, rankThreeEtaNumerator,
    rankThreeEtaDenominator, rankThreeLogProduct, rankThreeLogSum,
    rankThreeWeightedCofactorSum, rankThreeDirectionDefect,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Scalar autonomous equation extracted from a singular logarithmic core.
This is the manuscript step `det = 0 ⇒ η = R(ρ)` once the displayed
rational denominator is nonzero. -/
theorem rankThree_eta_eq_of_core_det_zero
    {K : Type*} [Field K]
    {v2 v3 v4 w1 w2 w3 w4 rho eta : K}
    (hden : rankThreeEtaDenominator
      v2 v3 v4 w1 w2 w3 w4 rho ≠ 0)
    (hdet : (rankThreeLogHessianCore
      v2 v3 v4 w1 w2 w3 w4 rho eta).det = 0) :
    eta =
      rankThreeEtaNumerator v2 v3 v4 w1 w2 w3 w4 rho /
        rankThreeEtaDenominator v2 v3 v4 w1 w2 w3 w4 rho := by
  have hzero :
      rankThreeEtaNumerator v2 v3 v4 w1 w2 w3 w4 rho -
        eta * rankThreeEtaDenominator v2 v3 v4 w1 w2 w3 w4 rho = 0 := by
    rw [← det_rankThreeLogHessianCore]
    exact hdet
  apply (eq_div_iff hden).2
  exact (sub_eq_zero.mp hzero).symm

/-- The generic moment exponent is exactly the rank-three affine exponent. -/
theorem rankThreeLogExponent_eq_base_add_direction
    {K : Type*} [CommRing K]
    (v2 v3 v4 w1 w2 w3 w4 rho : K) :
    (fun i => rankThreeLogBaseExponent v2 v3 v4 i +
      rho * rankThreeLogDirection w1 w2 w3 w4 i) =
      rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho := by
  funext i
  fin_cases i <;>
    simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      rankThreeLogExponent] <;> ring

/-- The generic line-moment logarithmic core specialises to the rank-three
core used in equation (6). -/
theorem rankThree_logarithmicCoreFromMoments_eq
    {K : Type*} [Field K]
    (v2 v3 v4 w1 w2 w3 w4 S0 S1 S2 : K) :
    logarithmicCoreFromMoments
        (rankThreeLogBaseExponent v2 v3 v4)
        (rankThreeLogDirection w1 w2 w3 w4)
        S0 S1 S2 =
      rankThreeLogHessianCore
        v2 v3 v4 w1 w2 w3 w4
        (S1 / S0) ((S2 * S0 - S1^2) / S0^2) := by
  let rho : K := S1 / S0
  let eta : K := (S2 * S0 - S1^2) / S0^2
  have he :
      (fun i => rankThreeLogBaseExponent v2 v3 v4 i +
        rho * rankThreeLogDirection w1 w2 w3 w4 i) =
        rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho :=
    rankThreeLogExponent_eq_base_add_direction
      v2 v3 v4 w1 w2 w3 w4 rho
  ext i j
  have hei := congrFun he i
  have hej := congrFun he j
  change
    (rankThreeLogBaseExponent v2 v3 v4 i +
          rho * rankThreeLogDirection w1 w2 w3 w4 i) *
        (rankThreeLogBaseExponent v2 v3 v4 j +
          rho * rankThreeLogDirection w1 w2 w3 w4 j) +
        eta *
          (rankThreeLogDirection w1 w2 w3 w4 i *
            rankThreeLogDirection w1 w2 w3 w4 j) -
        (if i = j then
          rankThreeLogBaseExponent v2 v3 v4 i +
            rho * rankThreeLogDirection w1 w2 w3 w4 i
        else 0) =
      rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho i *
          rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho j +
        eta *
          (rankThreeLogDirection w1 w2 w3 w4 i *
            rankThreeLogDirection w1 w2 w3 w4 j) -
        (if i = j then
          rankThreeLogExponent v2 v3 v4 w1 w2 w3 w4 rho i else 0)
  rw [hei, hej]

/-- A zero line-moment determinant gives a zero rank-three logarithmic-core
determinant. -/
theorem rankThree_core_det_zero_of_lineMoment_det_zero
    {K : Type*} [Field K]
    {v2 v3 v4 w1 w2 w3 w4 S0 S1 S2 : K}
    (hS0 : S0 ≠ 0)
    (hdet :
      (lineMomentHessian
        (rankThreeLogBaseExponent v2 v3 v4)
        (rankThreeLogDirection w1 w2 w3 w4)
        S0 S1 S2).det = 0) :
    (rankThreeLogHessianCore
      v2 v3 v4 w1 w2 w3 w4
      (S1 / S0) ((S2 * S0 - S1^2) / S0^2)).det = 0 := by
  have hfactor := det_lineMomentHessian
    (rankThreeLogBaseExponent v2 v3 v4)
    (rankThreeLogDirection w1 w2 w3 w4)
    (S0 := S0) (S1 := S1) (S2 := S2) hS0
  have hz :
      S0^4 *
        (logarithmicCoreFromMoments
          (rankThreeLogBaseExponent v2 v3 v4)
          (rankThreeLogDirection w1 w2 w3 w4)
          S0 S1 S2).det = 0 := by
    rw [← hfactor]
    exact hdet
  have hcore :
      (logarithmicCoreFromMoments
        (rankThreeLogBaseExponent v2 v3 v4)
        (rankThreeLogDirection w1 w2 w3 w4)
        S0 S1 S2).det = 0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hS0)
  rw [rankThree_logarithmicCoreFromMoments_eq] at hcore
  exact hcore

end

end HC4.Polynomial
