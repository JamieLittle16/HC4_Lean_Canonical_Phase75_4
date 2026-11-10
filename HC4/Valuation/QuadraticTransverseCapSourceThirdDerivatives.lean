import HC4.Valuation.QuadraticTransverseCapSourceSectionSchur
import HC4.Valuation.QuadraticTransverseCapSourceSupport
import Mathlib.Tactic

/-!
# Genuine source transverse quadratic cap: third derivatives vanish

The whole represented source, rather than just a graded first face, has
transverse degree at most two in coordinates 1, 2, 3. This module converts
the actual natural-weight source bound into the exact differential fact

  d_i d_j d_k F = 0 for all i,j,k in the three transverse coordinates.

The proof is coefficientwise and works over any field. The next source
adapter will use these vanishing identities to identify the seven
constant-section transverse blocks and affine mixed rows.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K]

/-- Under the literal source transverse cap two, every monomial with
total transverse degree at least three has zero coefficient. -/
theorem transverseCapTwo_sourceCoeff_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (d : Fin 4 →₀ ℕ)
    (hlarge : 3 ≤ d 1 + d 2 + d 3) :
    MvPolynomial.coeff d F = 0 := by
  by_contra hne
  have hmem : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hne
  have hw := hbound d hmem
  rw [weight_topKernelMarkedAxisNatWeight] at hw
  omega

/-- Three transverse derivatives of a genuine quadratic-cap source
vanish for every choice of directions, including repeated indices.
This is stronger than vanishing only at the longitudinal axis. -/
theorem transverseCapTwo_thirdTransverseDerivative_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j k : Fin 3) :
    MvPolynomial.pderiv i.succ
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv k.succ F)) = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  rw [coeff_pderiv_mixedDegree,
      coeff_pderiv_mixedDegree,
      coeff_pderiv_mixedDegree]
  let d : Fin 4 →₀ ℕ :=
    ((m + Finsupp.single i.succ 1) +
      Finsupp.single j.succ 1) +
      Finsupp.single k.succ 1
  have hlarge : 3 ≤ d 1 + d 2 + d 3 := by
    dsimp [d]
    simp only [Finsupp.add_apply]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [Finsupp.single_apply] <;> omega
  have hz : MvPolynomial.coeff d F = 0 :=
    transverseCapTwo_sourceCoeff_zero F hbound d hlarge
  change MvPolynomial.coeff d F * _ * _ * _ = 0
  rw [hz]
  ring

/-- Every transverse Hessian entry of the actual quadratic source has
zero derivative in every transverse direction. This is the precise
differential statement needed for section-independent transverse blocks. -/
theorem transverseCapTwo_transverseHessian_pderiv_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j k : Fin 3) :
    MvPolynomial.pderiv k.succ
      (HC4.Polynomial.hessian F i.succ j.succ) = 0 := by
  simpa [HC4.Polynomial.hessian_apply] using
    (transverseCapTwo_thirdTransverseDerivative_zero
      F hbound k j i)

variable [CharZero K] [IsAlgClosed K]

/-- Specialization to the ACTUAL represented source of the reachable
pure-longitudinal quadratic E3 branch. -/
theorem
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.TopFaceLinearPowerKernelData.pureLongitudinal_quadratic_sourceThirdTransverseDerivative_zero
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
    (i j k : Fin 3) :
    MvPolynomial.pderiv i.succ
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv k.succ T.topKernelReesSource)) = 0 := by
  have hbound :
      HasReverseWeightBound topKernelMarkedAxisNatWeight 2
        T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
  exact transverseCapTwo_thirdTransverseDerivative_zero
    T.topKernelReesSource hbound i j k

end
end HC4.Valuation
