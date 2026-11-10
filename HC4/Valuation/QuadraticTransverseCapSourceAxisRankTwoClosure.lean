import HC4.Valuation.QuadraticTransverseCapSourceAxisJetExtraction
import Mathlib.Tactic

/-!
# Entire actual-source transverse-quadratic singular-axis contradiction

This is the final source adapter for the pivot-free rank-two obstruction.
All three Hessian jets are obtained from differentiating the genuine
source determinant-one identity, not from seven independent section
assumptions. The source Hessian block and the transverse-linear marked
collision are the ones already present in the canonical E3 packet.

An arbitrary determinant-one source with total transverse degree at
most two and a genuine marked-axis collision cannot have singular
transverse 3x3 Hessian determinant as a polynomial in the longitudinal
variable. The E3 specialization then eliminates exactly this
previously unresolved singular transverse branch.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Actual-source rank-two/singular-transverse impossibility with
no abstract source-jet or section hypotheses. -/
theorem quadraticTransverseCap_sourceAxisThreeBlock_singular_impossible
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K)
        (longitudinalCoefficientPolynomialAt (Finsupp.single i 1) F) =
      Polynomial.eval (0 : K)
        (longitudinalCoefficientPolynomialAt (Finsupp.single i 1) F))
    (hthree : (quadraticSourceAxisThreeBlock F).determinantCore = 0) :
    False := by
  let C := quadraticSourceAxisThreeBlock F
  let b : Fin 3 → Polynomial K :=
    fun j => longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F
  let u := quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 0 0
  have haxis :
      quadraticAxisFourBlockCore u
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1 :=
    quadraticSource_axisSchurCore_one F hdet
  have hjet₀' :=
    quadraticSource_rankTwo_axisAdjugateJet_zero
      F hbound hdet hthree (0 : Fin 3)
  have hjet₁' :=
    quadraticSource_rankTwo_axisAdjugateJet_zero
      F hbound hdet hthree (1 : Fin 3)
  have hjet₂' :=
    quadraticSource_rankTwo_axisAdjugateJet_zero
      F hbound hdet hthree (2 : Fin 3)
  have hs₂₁ :
      quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 2 1 =
        quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 1 2 :=
    quadraticSourceSectionHessian_symmetric F (fun _ => 0) 2 1
  have hs₃₁ :
      quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 3 1 =
        quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 1 3 :=
    quadraticSourceSectionHessian_symmetric F (fun _ => 0) 3 1
  have hs₃₂ :
      quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 3 2 =
        quadraticSourceSectionHessian F (fun _ : Fin 3 => 0) 2 3 :=
    quadraticSourceSectionHessian_symmetric F (fun _ => 0) 3 2
  have hjet₀ :
      Polynomial.derivative C.a *
          quadraticTransverseAdjugateVector0 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.b *
          quadraticTransverseAdjugateVector1 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.c *
          quadraticTransverseAdjugateVector2 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) = 0 := by
    simpa [C, b, quadraticSourceAxisThreeBlock] using hjet₀'
  have hjet₁ :
      Polynomial.derivative C.b *
          quadraticTransverseAdjugateVector0 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.d *
          quadraticTransverseAdjugateVector1 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.e *
          quadraticTransverseAdjugateVector2 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) = 0 := by
    rw [hs₂₁] at hjet₁'
    simpa [C, b, quadraticSourceAxisThreeBlock] using hjet₁'
  have hjet₂ :
      Polynomial.derivative C.c *
          quadraticTransverseAdjugateVector0 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.e *
          quadraticTransverseAdjugateVector1 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative C.f *
          quadraticTransverseAdjugateVector2 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) = 0 := by
    rw [hs₃₁, hs₃₂] at hjet₂'
    simpa [C, b, quadraticSourceAxisThreeBlock] using hjet₂'
  exact quadraticTransverseCap_rankTwo_axisJet_impossible
    C b u hthree haxis hjet₀ hjet₁ hjet₂ hcoll

variable [IsAlgClosed K]

/-- The actual canonical E3 quadratic source cannot have singular
transverse Hessian determinant. The only remaining quadratic source
rank branch is therefore the generically invertible 3x3 block. -/
theorem
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.TopFaceLinearPowerKernelData.pureLongitudinal_quadratic_sourceAxisThreeBlock_nonsingular
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
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    (quadraticSourceAxisThreeBlock T.topKernelReesSource).determinantCore ≠ 0 := by
  intro hthree
  have hbound :
      HasReverseWeightBound topKernelMarkedAxisNatWeight 2
        T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
  exact quadraticTransverseCap_sourceAxisThreeBlock_singular_impossible
    T.topKernelReesSource hbound
    T.topKernelReesSource_hessianDeterminant_eq_one
    (fun i => T.topKernelReesSource_transverseLinearMarkedCollision i)
    hthree

end
end HC4.Valuation
