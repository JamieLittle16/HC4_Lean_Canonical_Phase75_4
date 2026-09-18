import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseSourceDeficits
import HC4.Valuation.SingularBoundedReverseWeightedRees
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.Valuation.ActualParameterLayer
import Mathlib.Tactic

/-!
# Source-honest total-deficit Rees family at the central staircase point

The surviving left `(1,V)`, `V>1` finite-staircase branch carries a
central source monomial with transverse deficits

    e₁ = e₂ = 0.

The planar carrier itself is already an exact positive weighted initial form.
If `W` is that positive source weight, replace its two transverse entries by

    W₁ - 1,  W₂ - 1.

Positivity of `W` makes this a natural weight.  Since every carrier monomial
lies on the same `W`-level, the bounded reverse-Rees parameter order becomes
exactly

    e₁ + e₂.

Thus layer zero is literally the central monomial and the least positive
actual layer is the canonical first positive total-deficit face.  The family
remains Hessian-singular by exact diagonal covariance.

No blocker clock, repair state, or auxiliary ray order is used.
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

/-- Natural version of the positive planar-carrier exposure weight, lowered
by one in the two central deficit coordinates. -/
noncomputable def QsOtherFacetPlanarCarrierPackage.centralDeficitWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next) :
    Fin 4 → ℕ := fun i =>
  match i.1 with
  | 0 => (P.finalWeight i).toNat
  | 1 => (P.finalWeight i).toNat - 1
  | 2 => (P.finalWeight i).toNat - 1
  | _ => (P.finalWeight i).toNat

/-- Natural common level of the underlying positive exposure. -/
noncomputable def QsOtherFacetPlanarCarrierPackage.centralDeficitLevel
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next) : ℕ :=
  P.finalLevel.toNat

namespace QsOtherFacetPlanarCarrierPackage

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)

/-- Every actual carrier monomial lies on the retained final source weight. -/
theorem support_finalWeight_eq_level
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    Finsupp.weight P.finalWeight e = P.finalLevel := by
  have hc := MvPolynomial.mem_support_iff.mp he
  rw [P.carrier_eq_initialForm, HC4.Polynomial.coeff_initialForm] at hc
  split at hc
  · assumption
  · exact (hc rfl).elim

private theorem finalWeight_toNat_cast
    (i : Fin 4) :
    (((P.finalWeight i).toNat : ℕ) : ℤ) = P.finalWeight i := by
  exact Int.toNat_of_nonneg (le_of_lt (P.finalWeight_pos i))

private theorem finalWeight_toNat_pos
    (i : Fin 4) :
    0 < (P.finalWeight i).toNat := by
  have hcast := P.finalWeight_toNat_cast i
  have hpos := P.finalWeight_pos i
  omega

private theorem finalLevel_toNat_cast :
    (((P.centralDeficitLevel : ℕ) : ℤ)) = P.finalLevel := by
  dsimp [centralDeficitLevel]
  exact Int.toNat_of_nonneg (le_of_lt P.finalLevel_pos)

/-- Exact natural arithmetic behind the total-deficit Rees construction. -/
theorem centralDeficitWeight_add_deficits_eq_level
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    Finsupp.weight P.centralDeficitWeight e + e 1 + e 2 =
      P.centralDeficitLevel := by
  have hW0 := P.finalWeight_toNat_cast (0 : Fin 4)
  have hW1 := P.finalWeight_toNat_cast (1 : Fin 4)
  have hW2 := P.finalWeight_toNat_cast (2 : Fin 4)
  have hW3 := P.finalWeight_toNat_cast (3 : Fin 4)
  have hL := P.finalLevel_toNat_cast
  have h1pos := P.finalWeight_toNat_pos (1 : Fin 4)
  have h2pos := P.finalWeight_toNat_pos (2 : Fin 4)
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
    simp only [centralDeficitWeight]
    have h1 :
        (P.finalWeight 1).toNat - 1 + 1 =
          (P.finalWeight 1).toNat :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt h1pos))
    have h2 :
        (P.finalWeight 2).toNat - 1 + 1 =
          (P.finalWeight 2).toNat :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt h2pos))
    calc
      e 0 * (P.finalWeight 0).toNat +
            e 1 * ((P.finalWeight 1).toNat - 1) +
            e 2 * ((P.finalWeight 2).toNat - 1) +
            e 3 * (P.finalWeight 3).toNat + e 1 + e 2 =
          (P.finalWeight 0).toNat * e 0 +
            (((P.finalWeight 1).toNat - 1) + 1) * e 1 +
            (((P.finalWeight 2).toNat - 1) + 1) * e 2 +
            (P.finalWeight 3).toNat * e 3 := by ring
      _ =
          (P.finalWeight 0).toNat * e 0 +
            (P.finalWeight 1).toNat * e 1 +
            (P.finalWeight 2).toNat * e 2 +
            (P.finalWeight 3).toNat * e 3 := by rw [h1, h2]
      _ = P.centralDeficitLevel := hlevelNat
  · intro i
    simp

/-- The carrier is bounded by the lowered natural weight. -/
theorem centralDeficitWeight_bound :
    HasReverseWeightBound P.centralDeficitWeight
      P.centralDeficitLevel P.carrier := by
  intro e he
  have h := P.centralDeficitWeight_add_deficits_eq_level he
  omega

/-- **Exact total-deficit order.** -/
theorem centralDeficit_order_eq
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    P.centralDeficitLevel -
        Finsupp.weight P.centralDeficitWeight e =
      e 1 + e 2 := by
  have h := P.centralDeficitWeight_add_deficits_eq_level he
  omega

/-- Honest reverse-Rees family whose parameter is total transverse deficit. -/
noncomputable def centralDeficitFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    P.centralDeficitWeight P.centralDeficitLevel P.carrier
    P.centralDeficitWeight_bound

/-- Exact support description of every total-deficit parameter layer. -/
theorem centralDeficitFamily_layer_mem_iff
    (q : ℕ) (e : Fin 4 →₀ ℕ) :
    e ∈ (familyParameterLayer P.centralDeficitFamily q).support ↔
      e ∈ P.carrier.support ∧ e 1 + e 2 = q := by
  unfold centralDeficitFamily
  rw [reverseWeightedReesFamily_parameterLayer_mem_iff]
  constructor
  · rintro ⟨he, hq⟩
    exact ⟨he, (P.centralDeficit_order_eq he).symm.trans hq⟩
  · rintro ⟨he, hq⟩
    exact ⟨he, (P.centralDeficit_order_eq he).trans hq⟩

/-- The total-deficit family remains identically Hessian-singular. -/
theorem centralDeficitFamily_hessian_zero :
    HC4.Polynomial.hessianDeterminant P.centralDeficitFamily = 0 := by
  exact reverseWeightedReesFamily_hessianDeterminant_eq_zero
    P.centralDeficitWeight P.centralDeficitLevel P.carrier
    P.centralDeficitWeight_bound P.hessian_zero

end QsOtherFacetPlanarCarrierPackage

namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- Layer zero of the total-deficit family is literally the central monomial. -/
theorem centralDeficitFamily_layer_zero_eq
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterLayer P.centralDeficitFamily 0 =
      MvPolynomial.monomial G.central
        (MvPolynomial.coeff G.central P.carrier) := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e = G.central
  · subst e
    have hmem :
        G.central ∈
          (familyParameterLayer P.centralDeficitFamily 0).support := by
      rw [P.centralDeficitFamily_layer_mem_iff]
      simp [G.central_mem, G.central_one_zero, G.central_two_zero]
    unfold QsOtherFacetPlanarCarrierPackage.centralDeficitFamily
    rw [reverseWeightedReesFamily_parameterLayer_coeff]
    simp [G.central_mem, G.central_one_zero, G.central_two_zero,
      P.centralDeficit_order_eq G.central_mem]
  · have hnot :
        e ∉ (familyParameterLayer P.centralDeficitFamily 0).support := by
      intro hmem
      rw [P.centralDeficitFamily_layer_mem_iff] at hmem
      have h1 : e 1 = 0 := by omega
      have h2 : e 2 = 0 := by omega
      apply he
      exact F.support_eq_of_deficits_eq
        hthree houtThree hmem.1 G.central_mem
        (by simpa [G.central_one_zero] using h1)
        (by simpa [G.central_two_zero] using h2)
    have hz :
        MvPolynomial.coeff e
          (familyParameterLayer P.centralDeficitFamily 0) = 0 :=
      MvPolynomial.notMem_support_iff.mp hnot
    rw [hz]
    have hce : G.central ≠ e := by
      intro h
      exact he h.symm
    simp [hce]

/-- The actual locked roof endpoint supplies a positive parameter layer. -/
theorem centralDeficitFamily_hasPositiveActualLayer :
    HasPositiveActualParameterLayer P.centralDeficitFamily := by
  rcases F.locked_yRoof_mem with ⟨hmem, _h0, h1, h2, _h3⟩
  have hLayer :
      C.ray.outsideExponent ∈
        (familyParameterLayer P.centralDeficitFamily F.locked.ell).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    refine ⟨hmem, ?_⟩
    rw [h1, h2]
    simp
  have hcoeff :
      (MvPolynomial.coeff C.ray.outsideExponent
        P.centralDeficitFamily).coeff F.locked.ell ≠ 0 := by
    rw [← familyParameterLayer_coeff]
    exact MvPolynomial.mem_support_iff.mp hLayer
  have hfamily :
      C.ray.outsideExponent ∈ P.centralDeficitFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hord :
      F.locked.ell ∈ familyParameterLayerOrders
        P.centralDeficitFamily := by
    exact (mem_familyParameterLayerOrders_iff
      P.centralDeficitFamily F.locked.ell).2
      ⟨C.ray.outsideExponent, hfamily, hcoeff⟩
  exact ⟨F.locked.ell,
    Finset.mem_filter.mpr ⟨hord, F.locked.ell_pos⟩⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
