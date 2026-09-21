import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightSourceDeficits
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.Valuation.ActualParameterLayer
import Mathlib.Tactic

/-!
# Source-honest right total-deficit Rees family at the mirrored central staircase

The surviving right `(V,1)`, `V>1` finite-staircase branch carries a
central source monomial with mirrored transverse deficits

    e₁ = e₃ = 0.

The planar carrier is the same honest positive weighted initial form used by
the left branch.  Lower the retained source weight by one in coordinates
`1` and `3`.  On every carrier monomial the bounded reverse-Rees order is
then exactly

    e₁ + e₃.

Thus layer zero is literally the right central monomial, while the locked
endpoint supplies a positive actual parameter layer.  Exact diagonal
covariance keeps the whole family Hessian-singular.

This is the mirrored source adapter only.  It introduces no repair transition,
no blocker clock, and no contradiction claim.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Mirrored natural exposure weight, lowered in the right deficit
coordinates `1` and `3`. -/
noncomputable def QsOtherFacetPlanarCarrierPackage.rightCentralDeficitWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next) :
    Fin 4 → ℕ := fun i =>
  match i.1 with
  | 0 => (P.finalWeight i).toNat
  | 1 => (P.finalWeight i).toNat - 1
  | 2 => (P.finalWeight i).toNat
  | _ => (P.finalWeight i).toNat - 1

namespace QsOtherFacetPlanarCarrierPackage

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)

private theorem right_finalWeight_toNat_cast
    (i : Fin 4) :
    (((P.finalWeight i).toNat : ℕ) : ℤ) = P.finalWeight i := by
  exact Int.toNat_of_nonneg (le_of_lt (P.finalWeight_pos i))

private theorem right_finalWeight_toNat_pos
    (i : Fin 4) :
    0 < (P.finalWeight i).toNat := by
  have hcast := P.right_finalWeight_toNat_cast i
  have hpos := P.finalWeight_pos i
  omega

private theorem right_finalLevel_toNat_cast :
    (((P.centralDeficitLevel : ℕ) : ℤ)) = P.finalLevel := by
  dsimp [centralDeficitLevel]
  exact Int.toNat_of_nonneg (le_of_lt P.finalLevel_pos)

/-- Exact natural arithmetic for the mirrored total-deficit order. -/
theorem rightCentralDeficitWeight_add_deficits_eq_level
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    Finsupp.weight P.rightCentralDeficitWeight e + e 1 + e 3 =
      P.centralDeficitLevel := by
  have hW0 := P.right_finalWeight_toNat_cast (0 : Fin 4)
  have hW1 := P.right_finalWeight_toNat_cast (1 : Fin 4)
  have hW2 := P.right_finalWeight_toNat_cast (2 : Fin 4)
  have hW3 := P.right_finalWeight_toNat_cast (3 : Fin 4)
  have hL := P.right_finalLevel_toNat_cast
  have h1pos := P.right_finalWeight_toNat_pos (1 : Fin 4)
  have h3pos := P.right_finalWeight_toNat_pos (3 : Fin 4)
  have hlevelZ := P.support_finalWeight_eq_level he
  have hlevelZ' :
      P.finalWeight 0 * (e 0 : ℤ) +
        P.finalWeight 1 * (e 1 : ℤ) +
        P.finalWeight 2 * (e 2 : ℤ) +
        P.finalWeight 3 * (e 3 : ℤ) = P.finalLevel := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype] at hlevelZ
    · simpa [Fin.sum_univ_four, nsmul_eq_mul, mul_comm,
        mul_left_comm, mul_assoc] using hlevelZ
    · intro i
      simp
  rw [← hW0, ← hW1, ← hW2, ← hW3, ← hL] at hlevelZ'
  have hlevelNat :
      (P.finalWeight 0).toNat * e 0 +
        (P.finalWeight 1).toNat * e 1 +
        (P.finalWeight 2).toNat * e 2 +
        (P.finalWeight 3).toNat * e 3 =
          P.centralDeficitLevel := by
    exact_mod_cast hlevelZ'
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp only [nsmul_eq_mul]
    simp only [rightCentralDeficitWeight]
    have h1 :
        (P.finalWeight 1).toNat - 1 + 1 =
          (P.finalWeight 1).toNat :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt h1pos))
    have h3 :
        (P.finalWeight 3).toNat - 1 + 1 =
          (P.finalWeight 3).toNat :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt h3pos))
    calc
      e 0 * (P.finalWeight 0).toNat +
            e 1 * ((P.finalWeight 1).toNat - 1) +
            e 2 * (P.finalWeight 2).toNat +
            e 3 * ((P.finalWeight 3).toNat - 1) + e 1 + e 3 =
          (P.finalWeight 0).toNat * e 0 +
            (((P.finalWeight 1).toNat - 1) + 1) * e 1 +
            (P.finalWeight 2).toNat * e 2 +
            (((P.finalWeight 3).toNat - 1) + 1) * e 3 := by ring
      _ =
          (P.finalWeight 0).toNat * e 0 +
            (P.finalWeight 1).toNat * e 1 +
            (P.finalWeight 2).toNat * e 2 +
            (P.finalWeight 3).toNat * e 3 := by rw [h1, h3]
      _ = P.centralDeficitLevel := hlevelNat
  · intro i
    simp

/-- The right carrier is bounded by the mirrored lowered weight. -/
theorem rightCentralDeficitWeight_bound :
    HasReverseWeightBound P.rightCentralDeficitWeight
      P.centralDeficitLevel P.carrier := by
  intro e he
  have h := P.rightCentralDeficitWeight_add_deficits_eq_level he
  omega

/-- Exact mirrored total-deficit order. -/
theorem rightCentralDeficit_order_eq
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    P.centralDeficitLevel -
        Finsupp.weight P.rightCentralDeficitWeight e =
      e 1 + e 3 := by
  have h := P.rightCentralDeficitWeight_add_deficits_eq_level he
  omega

/-- Honest reverse-Rees family whose parameter is the right total deficit. -/
noncomputable def rightCentralDeficitFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    P.rightCentralDeficitWeight P.centralDeficitLevel P.carrier
    P.rightCentralDeficitWeight_bound

/-- Exact support description of every mirrored total-deficit layer. -/
theorem rightCentralDeficitFamily_layer_mem_iff
    (q : ℕ) (e : Fin 4 →₀ ℕ) :
    e ∈ (familyParameterLayer P.rightCentralDeficitFamily q).support ↔
      e ∈ P.carrier.support ∧ e 1 + e 3 = q := by
  unfold rightCentralDeficitFamily
  rw [reverseWeightedReesFamily_parameterLayer_mem_iff]
  constructor
  · rintro ⟨he, hq⟩
    exact ⟨he, (P.rightCentralDeficit_order_eq he).symm.trans hq⟩
  · rintro ⟨he, hq⟩
    exact ⟨he, (P.rightCentralDeficit_order_eq he).trans hq⟩

/-- The mirrored total-deficit family remains identically Hessian-singular. -/
theorem rightCentralDeficitFamily_hessian_zero :
    HC4.Polynomial.hessianDeterminant P.rightCentralDeficitFamily = 0 := by
  exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
    P.rightCentralDeficitWeight P.centralDeficitLevel P.carrier
    P.rightCentralDeficitWeight_bound P.hessian_zero

end QsOtherFacetPlanarCarrierPackage

namespace QsOtherFacetPrRightVCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrRightVContactFrontierData C P S R}
    (G : QsOtherFacetPrRightVCentralRankTwoGeometry F)

/-- Layer zero of the mirrored total-deficit family is the central monomial. -/
theorem rightCentralDeficitFamily_layer_zero_eq
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterLayer P.rightCentralDeficitFamily 0 =
      MvPolynomial.monomial G.central
        (MvPolynomial.coeff G.central P.carrier) := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e = G.central
  · subst e
    have hmem :
        G.central ∈
          (familyParameterLayer P.rightCentralDeficitFamily 0).support := by
      rw [P.rightCentralDeficitFamily_layer_mem_iff]
      simp [G.central_mem, G.central_one_zero, G.central_three_zero]
    unfold QsOtherFacetPlanarCarrierPackage.rightCentralDeficitFamily
    rw [reverseWeightedReesFamily_parameterLayer_coeff]
    simp [G.central_mem, G.central_one_zero, G.central_three_zero,
      P.rightCentralDeficit_order_eq G.central_mem]
  · have hnot :
        e ∉ (familyParameterLayer P.rightCentralDeficitFamily 0).support := by
      intro hmem
      rw [P.rightCentralDeficitFamily_layer_mem_iff] at hmem
      have h1 : e 1 = 0 := by omega
      have h3 : e 3 = 0 := by omega
      apply he
      exact F.support_eq_of_deficits_eq
        hthree houtThree hmem.1 G.central_mem
        (by simpa [G.central_one_zero] using h1)
        (by simpa [G.central_three_zero] using h3)
    have hz :
        MvPolynomial.coeff e
          (familyParameterLayer P.rightCentralDeficitFamily 0) = 0 :=
      MvPolynomial.notMem_support_iff.mp hnot
    rw [hz]
    have hce : G.central ≠ e := by
      intro h
      exact he h.symm
    simp [hce]

/-- The right locked roof endpoint supplies a positive actual layer. -/
theorem rightCentralDeficitFamily_hasPositiveActualLayer
    (_geometry : QsOtherFacetPrRightVCentralRankTwoGeometry F) :
    HasPositiveActualParameterLayer P.rightCentralDeficitFamily := by
  rcases QsOtherFacetPrRightVContactFrontierData.locked_yRoof_mem F with
    ⟨hmem, _h0, h1, _h2, h3⟩
  have hLayer :
      C.ray.outsideExponent ∈
        (familyParameterLayer P.rightCentralDeficitFamily F.locked.ell).support := by
    rw [P.rightCentralDeficitFamily_layer_mem_iff]
    refine ⟨hmem, ?_⟩
    rw [h1, h3]
    simp
  have hcoeff :
      (MvPolynomial.coeff C.ray.outsideExponent
        P.rightCentralDeficitFamily).coeff F.locked.ell ≠ 0 := by
    rw [← familyParameterLayer_coeff]
    exact MvPolynomial.mem_support_iff.mp hLayer
  have hfamily :
      C.ray.outsideExponent ∈ P.rightCentralDeficitFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hord :
      F.locked.ell ∈ familyParameterLayerOrders
        P.rightCentralDeficitFamily := by
    exact (mem_familyParameterLayerOrders_iff
      P.rightCentralDeficitFamily F.locked.ell).2
      ⟨C.ray.outsideExponent, hfamily, hcoeff⟩
  exact ⟨F.locked.ell,
    Finset.mem_filter.mpr ⟨hord, F.locked.ell_pos⟩⟩

end QsOtherFacetPrRightVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
