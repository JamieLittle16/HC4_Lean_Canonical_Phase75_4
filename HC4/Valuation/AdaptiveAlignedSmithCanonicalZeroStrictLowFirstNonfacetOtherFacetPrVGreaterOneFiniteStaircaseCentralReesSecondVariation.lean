import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralClosure
import HC4.Valuation.CoordinateMaxKernelOpeningReverseRees
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Polynomial.RankTwoKernelSecondVariation
import Mathlib.Tactic

/-!
# Central finite-staircase reverse-Rees second variation

The surviving left \`(1,V)\`, \`V>1\` finite-staircase branch has already been
reduced to a unique coordinate-\`0\` maximal source monomial

    c = (p,0,0,r)

whose exact initial face is Hessian-singular but has a nonzero principal
\`(0,3)\` Hessian minor.

This file returns to the *whole* honest carrier.  We form the bounded reverse
Rees family for coordinate \`0\`.  Its zero layer is exactly the retained
central monomial and the complete family remains Hessian-singular.  Since the
locked roof endpoint has coordinate \`0 = 1 < c₀\`, a positive parameter layer
really occurs.

At the least positive actual layer, the parameter-first Hessian therefore has

* a rank-two constant matrix supported on coordinates \`0,3\`;
* no hidden positive coefficient below the selected order; and
* identically zero determinant.

The exact second-variation theorem then forces the \`(1,2)\` Hessian principal
minor of that first source layer to vanish.

This is source-honest: no auxiliary Rees clock is identified with the zero
blocker and no repair transition is manufactured.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetPlanarCarrierPackage C .pr}
variable {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
variable {R : QsOtherFacetContactQuadraticReesPackage C}
variable {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
variable (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- The retained coordinate-\`0\` maximum is exactly the natural reverse-Rees
weight bound for the whole source carrier. -/
theorem hasReverseWeightBound :
    HasReverseWeightBound
      (coordinateMaxNatWeight (0 : Fin 4))
      G.exposure.level P.carrier := by
  intro e he
  rw [weight_coordinateMaxNatWeight]
  exact G.exposure.maximal e he

/-- Honest reverse-Rees family from the whole carrier back to the unique
central coordinate-\`0\` face. -/
noncomputable def reverseReesFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    (coordinateMaxNatWeight (0 : Fin 4))
    G.exposure.level P.carrier G.hasReverseWeightBound

/-- Parameter layer zero is literally the retained central monomial face. -/
theorem reverseReesFamily_layer_zero_eq_exposure :
    familyParameterLayer G.reverseReesFamily 0 = G.exposure.face := by
  rw [← polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
      (coordinateMaxNatWeight (0 : Fin 4))
      G.exposure.level P.carrier G.hasReverseWeightBound]
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  rw [G.exposure.face_eq]
  congr 1
  funext i
  fin_cases i <;>
    simp [coordinateMaxNatWeight, HC4.Newton.coordinateMaxWeight]

/-- The complete coordinate-\`0\` reverse-Rees family remains Hessian-singular. -/
theorem reverseReesFamily_hessianDeterminant_eq_zero :
    HC4.Polynomial.hessianDeterminant G.reverseReesFamily = 0 := by
  rw [reverseReesFamily]
  exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
    (coordinateMaxNatWeight (0 : Fin 4))
    G.exposure.level P.carrier G.hasReverseWeightBound P.hessian_zero

/-- The central longitudinal coordinate is strictly larger than one. -/
theorem central_zero_gt_one
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    1 < G.central 0 := by
  have hwall := F.support_deficit_wall hthree houtThree G.central_mem
  rw [G.central_one_zero, G.central_two_zero] at hwall
  norm_num at hwall
  have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
    exact_mod_cast F.locked.ell_pos
  have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
    exact_mod_cast (show 1 < F.highest.n by omega)
  by_contra hnot
  have hle : G.central 0 ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos (G.central 0) with hzero | hpos
  · rw [hzero] at hwall
    norm_num at hwall
    have hnPos : (0 : ℤ) < (F.highest.n : ℤ) := by omega
    have hprod : (0 : ℤ) <
        (F.locked.ell : ℤ) * (F.highest.n : ℤ) :=
      mul_pos hellZ hnPos
    nlinarith
  · have hone : G.central 0 = 1 := by omega
    rw [hone] at hwall
    norm_num at hwall
    rcases hwall with hellZero | hnOneZero
    · exact (Nat.ne_of_gt F.locked.ell_pos) hellZero
    · have hnOnePos : (0 : ℤ) < (F.highest.n : ℤ) - 1 := by omega
      exact (ne_of_gt hnOnePos) hnOneZero

/-- The honest reverse-Rees family has a genuinely positive actual layer. -/
theorem reverseReesFamily_hasPositiveActualParameterLayer
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HasPositiveActualParameterLayer G.reverseReesFamily := by
  classical
  rcases F.locked_yRoof_mem with
    ⟨hlocked, hlocked0, _hlocked1, _hlocked2, _hlocked3⟩
  let q := G.exposure.level - 1
  have hlevel : 1 < G.exposure.level := by
    rw [G.exposure_level_eq]
    exact G.central_zero_gt_one hthree houtThree
  have hqpos : 0 < q := by
    dsimp [q]
    omega
  have hweight :
      Finsupp.weight (coordinateMaxNatWeight (0 : Fin 4))
          C.ray.outsideExponent = 1 := by
    rw [weight_coordinateMaxNatWeight, hlocked0]
  have hdrop :
      G.exposure.level -
          Finsupp.weight (coordinateMaxNatWeight (0 : Fin 4))
            C.ray.outsideExponent = q := by
    rw [hweight]
    rfl
  have hlayer :
      C.ray.outsideExponent ∈
        (familyParameterLayer G.reverseReesFamily q).support := by
    rw [reverseReesFamily]
    rw [reverseWeightedReesFamily_parameterLayer_mem_iff]
    exact ⟨hlocked, hdrop⟩
  have hcoeff :
      (MvPolynomial.coeff C.ray.outsideExponent
          G.reverseReesFamily).coeff q ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hlayer
    rw [familyParameterLayer_coeff] at h
    exact h
  have hfamily :
      C.ray.outsideExponent ∈ G.reverseReesFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have horder : q ∈ familyParameterLayerOrders G.reverseReesFamily :=
    (mem_familyParameterLayerOrders_iff G.reverseReesFamily q).2
      ⟨C.ray.outsideExponent, hfamily, hcoeff⟩
  exact ⟨q, Finset.mem_filter.mpr ⟨horder, hqpos⟩⟩

/-- **Central second-variation constraint.**  The first positive source layer
of the honest coordinate-\`0\` reverse-Rees family has zero Hessian principal
minor in the two deficit coordinates \`1,2\`. -/
theorem firstPositiveLayer_hessianPrincipalMinor_one_two_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let hpos := G.reverseReesFamily_hasPositiveActualParameterLayer
      hthree houtThree
    let j := firstPositiveActualParameterOrder G.reverseReesFamily hpos
    HC4.Polynomial.hessianPrincipalMinor
      (familyParameterLayer G.reverseReesFamily j)
      (1 : Fin 4) (2 : Fin 4) = 0 := by
  let hpos := G.reverseReesFamily_hasPositiveActualParameterLayer
    hthree houtThree
  let j := firstPositiveActualParameterOrder G.reverseReesFamily hpos
  let M := parameterFirstHessian G.reverseReesFamily
  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a := H0 (0 : Fin 4) 0
  let b := H0 (0 : Fin 4) 3
  let c := H0 (3 : Fin 4) 0
  let d := H0 (3 : Fin 4) 3

  have hj : 0 < j :=
    firstPositiveActualParameterOrder_pos G.reverseReesFamily hpos

  have hgap : ∀ r s,
      HasNoPositiveParameterCoeffBelow j (M r s) := by
    intro r s n hnpos hnlt
    dsimp [M]
    rw [parameterFirstHessian_coeff]
    rw [familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
      G.reverseReesFamily hpos hnpos hnlt]
    simp [HC4.Polynomial.hessian_apply]

  have hbase : ∀ r s,
      (M r s).coeff 0 =
        HC4.Polynomial.rankTwoZeroKernelBase a b c d r s := by
    intro r s
    dsimp [M]
    rw [parameterFirstHessian_coeff]
    rw [G.reverseReesFamily_layer_zero_eq_exposure]
    dsimp [H0, a, b, c, d]
    fin_cases r <;> fin_cases s <;>
      simp [HC4.Polynomial.rankTwoZeroKernelBase,
        G.exposure_face_eq, HC4.Polynomial.hessian_apply,
        MvPolynomial.pderiv_monomial,
        G.central_one_zero, G.central_two_zero]

  have hactive : a * d - b * c ≠ 0 := by
    dsimp [a, b, c, d, H0]
    simpa [HC4.Polynomial.hessianPrincipalMinor] using
      G.exposure_rankTwo_minor

  have hdet : M.det = 0 := by
    dsimp [M]
    rw [parameterFirstHessian_det]
    rw [G.reverseReesFamily_hessianDeterminant_eq_zero]
    simp

  have htwo :
      (2 : MvPolynomial (Fin 4) K) ≠ 0 := by
    norm_num

  have hkernel :=
    HC4.Polynomial.kernelBlock_det_eq_zero_of_polynomialMatrix_gap_domain
      (R := MvPolynomial (Fin 4) K)
      hj M hgap a b c d hbase htwo hactive hdet

  dsimp [M, j] at hkernel
  simp only [parameterFirstHessian_coeff] at hkernel
  simpa [HC4.Polynomial.hessianPrincipalMinor] using hkernel

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
