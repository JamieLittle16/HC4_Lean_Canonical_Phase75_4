import HC4.Valuation.QuadraticTransverseCapSourceMarkedCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import Mathlib.Tactic

/-!
# Literal transverse cap two on the represented source

The strict quadratic relevel provides HasReverseWeightBound for the
unchanged represented determinant-one source with marked-axis weights
(0,1,1,1). Hence every longitudinal coefficient polynomial carrying
transverse exponent (b,c,d) of total degree at least three is ZERO.

This source-level statement is stronger than saying the first-actual
graded layer is quadratic. It justifies expanding the whole source as
a(x)+b(x)·y+1/2 y^T C(x)y, with no uncontrolled higher transverse
terms, in the forthcoming determinant coefficient adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Every longitudinal coefficient with transverse degree at least
three vanishes under the *whole-source* quadratic marked-axis cap.
No homogeneous-source hypothesis is used. -/
theorem transverseCapTwo_longitudinalCoefficient_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (b c d : ℕ)
    (hlarge : 3 ≤ b + c + d) :
    longitudinalCoefficientPolynomial b c d F = 0 := by
  classical
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero, coeff_longitudinalCoefficientPolynomial]
  by_contra hc
  have hmem :
      (smithTransverseExponent b c d).cons a ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hc
  have hw := hbound ((smithTransverseExponent b c d).cons a) hmem
  rw [weight_topKernelMarkedAxisNatWeight] at hw
  have hcoords :
      ((smithTransverseExponent b c d).cons a) (1 : Fin 4) +
        ((smithTransverseExponent b c d).cons a) (2 : Fin 4) +
        ((smithTransverseExponent b c d).cons a) (3 : Fin 4) =
        b + c + d := by
    simp [Finsupp.cons_succ]
  omega

/-- The REAL quadratic relevel source, rather than just its
first-actual graded quotient, has no transverse coefficient of
degree three or more. -/
theorem AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.TopFaceLinearPowerKernelData.pureLongitudinal_quadratic_sourceTransverseCap
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {kernelCoordinate : Fin 4}
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2)
    (b c d : ℕ)
    (hlarge : 3 ≤ b + c + d) :
    longitudinalCoefficientPolynomial b c d T.topKernelReesSource = 0 := by
  have hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
      T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
  exact transverseCapTwo_longitudinalCoefficient_zero
    T.topKernelReesSource hbound b c d hlarge

end

end HC4.Valuation
