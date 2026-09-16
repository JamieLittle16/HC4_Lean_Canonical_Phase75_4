import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofTerminalClosure
import HC4.Newton.TerminalCoordinatePermutation
import HC4.Polynomial.RankThreeAffineSupportRealisation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import Mathlib.Tactic

/-!
# Source-honest affine realisation of the exposed cross-roof face

The verified lower-hull package gives one exact singular source face together
with literal points on the two transverse roofs.  This file does only the
remaining interface work:

* rename the face so old coordinate `1` is the affine-line parameter;
* rename it in the reverse orientation so old coordinate `2` is the parameter;
* package both renamed supports as `RankThreeAffineSupportData`;
* prove the two coefficient profiles have the exact endpoint degrees `v` and
  `q`.

No support is reconstructed and no generic planar/JC2 reduction occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open HC4.RationalRigidity

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}

/-- Forward coordinate order `(old 1, old 0, old 2, old 3)`. -/
private def crossRoofHighPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1

/-- Reverse coordinate order `(old 2, old 0, old 1, old 3)`.

This is deliberately the composition of the two required elementary swaps:
first `(0 1)`, then `(0 2)`.  A bare `(0 2)` would order the two retained
rank-three coordinates incorrectly for the already-verified mirror terminal. -/
private def crossRoofLowPerm : Equiv.Perm (Fin 4) :=
  crossRoofHighPerm.trans (Equiv.swap (0 : Fin 4) 2)

@[simp] private theorem crossRoofHighPerm_zero :
    crossRoofHighPerm (0 : Fin 4) = 1 := by decide
@[simp] private theorem crossRoofHighPerm_one :
    crossRoofHighPerm (1 : Fin 4) = 0 := by decide
@[simp] private theorem crossRoofHighPerm_two :
    crossRoofHighPerm (2 : Fin 4) = 2 := by decide
@[simp] private theorem crossRoofHighPerm_three :
    crossRoofHighPerm (3 : Fin 4) = 3 := by decide

@[simp] private theorem crossRoofHighPerm_symm_zero :
    crossRoofHighPerm.symm (0 : Fin 4) = 1 := by decide
@[simp] private theorem crossRoofHighPerm_symm_one :
    crossRoofHighPerm.symm (1 : Fin 4) = 0 := by decide
@[simp] private theorem crossRoofHighPerm_symm_two :
    crossRoofHighPerm.symm (2 : Fin 4) = 2 := by decide
@[simp] private theorem crossRoofHighPerm_symm_three :
    crossRoofHighPerm.symm (3 : Fin 4) = 3 := by decide

@[simp] private theorem crossRoofLowPerm_zero :
    crossRoofLowPerm (0 : Fin 4) = 1 := by decide
@[simp] private theorem crossRoofLowPerm_one :
    crossRoofLowPerm (1 : Fin 4) = 2 := by decide
@[simp] private theorem crossRoofLowPerm_two :
    crossRoofLowPerm (2 : Fin 4) = 0 := by decide
@[simp] private theorem crossRoofLowPerm_three :
    crossRoofLowPerm (3 : Fin 4) = 3 := by decide

@[simp] private theorem crossRoofLowPerm_symm_zero :
    crossRoofLowPerm.symm (0 : Fin 4) = 2 := by decide
@[simp] private theorem crossRoofLowPerm_symm_one :
    crossRoofLowPerm.symm (1 : Fin 4) = 0 := by decide
@[simp] private theorem crossRoofLowPerm_symm_two :
    crossRoofLowPerm.symm (2 : Fin 4) = 1 := by decide
@[simp] private theorem crossRoofLowPerm_symm_three :
    crossRoofLowPerm.symm (3 : Fin 4) = 3 := by decide

/-- Exact source face with old coordinate `1` moved to the omitted coordinate. -/
private noncomputable def highFace
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.rename crossRoofHighPerm E.hull.face

/-- Exact source face with old coordinate `2` moved to the omitted coordinate,
while old coordinates `0,1` occupy rank-three coordinates `1,2`. -/
private noncomputable def lowFace
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.rename crossRoofLowPerm E.hull.face

/-- A small generic degree helper: a support bound plus one supported exponent
at the bound determines the exact degree of the extracted coefficient profile. -/
private theorem coefficientProfile_natDegree_eq_of_bound_endpoint
    {G : MvPolynomial (Fin 4) K}
    {A B C0 : ℕ} {q r s : K}
    (D : HC4.Polynomial.RankThreeAffineSupportData G A B C0 q r s)
    (M : ℕ)
    (hbound : ∀ e ∈ G.support, e 0 ≤ M)
    {eM : Fin 4 →₀ ℕ}
    (heM : eM ∈ G.support)
    (heM0 : eM 0 = M) :
    D.coefficientProfile.natDegree = M := by
  apply Nat.le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_contra hne
    have hnmem : n ∈ D.coefficientProfile.support :=
      Polynomial.mem_support_iff.mpr hne
    rcases D.exists_exponent_of_coefficientProfile_mem hnmem with
      ⟨e, he, he0⟩
    have hle := hbound e he
    omega
  · have hMmem : M ∈ D.coefficientProfile.support := by
      have hm := D.coefficientProfile_mem_of_mem heM
      simpa [heM0] using hm
    exact Polynomial.le_natDegree_of_mem_supp M hMmem

/-- Forward source-honest affine support package. -/
noncomputable def highSupportData
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.RankThreeAffineSupportData
      (highFace E)
      E.kLo E.q (F.V * E.jLo)
      ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
      (-((E.q : K) / (E.v : K)))
      ((F.V : K) * (((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)) := by
  classical
  have hsupp :
      (highFace E).support =
        Finset.image (Finsupp.mapDomain crossRoofHighPerm) E.hull.face.support := by
    dsimp [highFace]
    exact MvPolynomial.support_rename_of_injective crossRoofHighPerm.injective
  refine {
    eq_of_zeroCoordinate_eq := ?_
    affine := ?_
  }
  · intro e f he hf h0
    rw [hsupp] at he hf
    rcases Finset.mem_image.mp he with ⟨e0, he0, heq⟩
    rcases Finset.mem_image.mp hf with ⟨f0, hf0, hfeq⟩
    have h1 : e0 1 = f0 1 := by
      have h := h0
      rw [← heq, ← hfeq] at h
      simpa [crossRoofHighPerm] using h
    have hef := E.face_eq_of_one_eq hthree houtThree he0 hf0 h1
    calc
      e = Finsupp.mapDomain crossRoofHighPerm e0 := heq.symm
      _ = Finsupp.mapDomain crossRoofHighPerm f0 := by rw [hef]
      _ = f := hfeq
  · intro e he
    rw [hsupp] at he
    rcases Finset.mem_image.mp he with ⟨e0, he0, heq⟩
    subst e
    have hvK : (E.v : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt E.v_pos)
    have hkHiPos : 0 < E.kHi := lt_trans E.kLo_pos E.pair_lt
    have hkHiOne : 1 ≤ E.kHi := by omega

    have hzeroZ := E.face_zero_interpolation hthree houtThree he0
    have hzeroK :
        (E.v : K) * ((e0 0 : K) - (E.kLo : K)) =
          (e0 1 : K) *
            (((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) := by
      exact_mod_cast hzeroZ

    have hcrossZ := E.face_cross_relation he0
    have hcrossK :
        (E.v : K) * (e0 2 : K) + (E.q : K) * (e0 1 : K) =
          (E.q : K) * (E.v : K) := by
      exact_mod_cast hcrossZ

    have hthreeZ := E.face_three_interpolation hthree houtThree he0
    rw [E.lo_three, E.hi_three] at hthreeZ
    have hthreeK :
        (E.v : K) *
            ((e0 3 : K) - ((F.V * E.jLo : ℕ) : K)) =
          (e0 1 : K) *
            (((F.V * (E.kHi - 1) : ℕ) : K) -
              ((F.V * E.jLo : ℕ) : K)) := by
      exact_mod_cast hthreeZ
    have hkHiSubK :
        ((E.kHi - 1 : ℕ) : K) = (E.kHi : K) - 1 := by
      rw [Nat.cast_sub hkHiOne]
      norm_num

    funext i
    fin_cases i
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofHighPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofHighPerm_symm_one, crossRoofHighPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      field_simp [hvK]
      linear_combination hzeroK
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofHighPerm_symm_two, crossRoofHighPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      field_simp [hvK]
      linear_combination hcrossK
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofHighPerm_symm_three, crossRoofHighPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      rw [Nat.cast_mul, Nat.cast_mul, hkHiSubK] at hthreeK
      field_simp [hvK]
      linear_combination hthreeK

/-- Reverse source-honest affine support package. -/
noncomputable def lowSupportData
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.RankThreeAffineSupportData
      (lowFace E)
      (E.jHi + 1) E.v (F.V * (E.kHi - 1))
      (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
      (-((E.v : K) / (E.q : K)))
      ((F.V : K) * ((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K)) := by
  classical
  have hsupp :
      (lowFace E).support =
        Finset.image (Finsupp.mapDomain crossRoofLowPerm) E.hull.face.support := by
    dsimp [lowFace]
    exact MvPolynomial.support_rename_of_injective crossRoofLowPerm.injective
  refine {
    eq_of_zeroCoordinate_eq := ?_
    affine := ?_
  }
  · intro e f he hf h0
    rw [hsupp] at he hf
    rcases Finset.mem_image.mp he with ⟨e0, he0, heq⟩
    rcases Finset.mem_image.mp hf with ⟨f0, hf0, hfeq⟩
    have h2 : e0 2 = f0 2 := by
      have h := h0
      rw [← heq, ← hfeq] at h
      simpa only [Finsupp.mapDomain_equiv_apply,
        crossRoofLowPerm_symm_zero] using h
    have hef := E.face_eq_of_two_eq hthree houtThree he0 hf0 h2
    calc
      e = Finsupp.mapDomain crossRoofLowPerm e0 := heq.symm
      _ = Finsupp.mapDomain crossRoofLowPerm f0 := by rw [hef]
      _ = f := hfeq
  · intro e he
    rw [hsupp] at he
    rcases Finset.mem_image.mp he with ⟨e0, he0, heq⟩
    subst e
    have hqK : (E.q : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt E.q_pos)
    have hkHiPos : 0 < E.kHi := lt_trans E.kLo_pos E.pair_lt
    have hkHiOne : 1 ≤ E.kHi := by omega

    have hzeroZ := E.face_zero_interpolation hthree houtThree he0
    have hcrossZ := E.face_cross_relation he0
    have hthreeZ := E.face_three_interpolation hthree houtThree he0
    rw [E.lo_three, E.hi_three] at hthreeZ

    have hvZ : (0 : ℤ) < (E.v : ℤ) := by exact_mod_cast E.v_pos
    have hrevZeroZ :
        (E.q : ℤ) *
            ((e0 0 : ℤ) - (((E.jHi + 1 : ℕ) : ℤ))) =
          (e0 2 : ℤ) *
            ((E.kLo : ℤ) - (((E.jHi + 1 : ℕ) : ℤ))) := by
      nlinarith [hzeroZ, hcrossZ]
    have hrevOneZ :
        (E.q : ℤ) * ((e0 1 : ℤ) - (E.v : ℤ)) =
          (e0 2 : ℤ) * (-(E.v : ℤ)) := by
      nlinarith [hcrossZ]
    have hrevThreeZ :
        (E.q : ℤ) *
            ((e0 3 : ℤ) - ((F.V * (E.kHi - 1) : ℕ) : ℤ)) =
          (e0 2 : ℤ) *
            (((F.V * E.jLo : ℕ) : ℤ) -
              ((F.V * (E.kHi - 1) : ℕ) : ℤ)) := by
      nlinarith [hthreeZ, hcrossZ]

    have hrevZeroK :
        (E.q : K) *
            ((e0 0 : K) - (((E.jHi + 1 : ℕ) : K))) =
          (e0 2 : K) *
            ((E.kLo : K) - (((E.jHi + 1 : ℕ) : K))) := by
      exact_mod_cast hrevZeroZ
    have hrevOneK :
        (E.q : K) * ((e0 1 : K) - (E.v : K)) =
          (e0 2 : K) * (-(E.v : K)) := by
      exact_mod_cast hrevOneZ
    have hrevThreeK :
        (E.q : K) *
            ((e0 3 : K) - ((F.V * (E.kHi - 1) : ℕ) : K)) =
          (e0 2 : K) *
            (((F.V * E.jLo : ℕ) : K) -
              ((F.V * (E.kHi - 1) : ℕ) : K)) := by
      exact_mod_cast hrevThreeZ
    have hkHiSubK :
        ((E.kHi - 1 : ℕ) : K) = (E.kHi : K) - 1 := by
      rw [Nat.cast_sub hkHiOne]
      norm_num

    funext i
    fin_cases i
    · simp [Finsupp.mapDomain_equiv_apply, crossRoofLowPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofLowPerm_symm_one, crossRoofLowPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      field_simp [hqK]
      linear_combination hrevZeroK
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofLowPerm_symm_two, crossRoofLowPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      field_simp [hqK]
      linear_combination hrevOneK
    · simp [Finsupp.mapDomain_equiv_apply,
        crossRoofLowPerm_symm_three, crossRoofLowPerm_symm_zero,
        HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection]
      rw [Nat.cast_mul, Nat.cast_mul, hkHiSubK] at hrevThreeK
      field_simp [hqK]
      linear_combination hrevThreeK

/-- The forward coefficient profile has exactly the high-side residual degree. -/
theorem highProfile_natDegree
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (E.highSupportData hthree houtThree).coefficientProfile.natDegree = E.v := by
  classical
  let D := E.highSupportData hthree houtThree
  have hsupp :
      (highFace E).support =
        Finset.image (Finsupp.mapDomain crossRoofHighPerm) E.hull.face.support := by
    dsimp [highFace]
    exact MvPolynomial.support_rename_of_injective crossRoofHighPerm.injective
  have hbound : ∀ e ∈ (highFace E).support, e 0 ≤ E.v := by
    intro e he
    rw [hsupp] at he
    rcases Finset.mem_image.mp he with ⟨e0, he0, rfl⟩
    simpa [crossRoofHighPerm] using E.face_one_le_v he0
  have hhi : Finsupp.mapDomain crossRoofHighPerm E.hi ∈ (highFace E).support := by
    rw [hsupp]
    exact Finset.mem_image.mpr ⟨E.hi, E.hi_mem_face, rfl⟩
  have hhi0 : (Finsupp.mapDomain crossRoofHighPerm E.hi) 0 = E.v := by
    simpa [crossRoofHighPerm] using E.hi_one
  exact coefficientProfile_natDegree_eq_of_bound_endpoint D E.v hbound hhi hhi0

/-- The reversed coefficient profile has exactly the low-side residual degree. -/
theorem lowProfile_natDegree
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (E.lowSupportData hthree houtThree).coefficientProfile.natDegree = E.q := by
  classical
  let D := E.lowSupportData hthree houtThree
  have hsupp :
      (lowFace E).support =
        Finset.image (Finsupp.mapDomain crossRoofLowPerm) E.hull.face.support := by
    dsimp [lowFace]
    exact MvPolynomial.support_rename_of_injective crossRoofLowPerm.injective
  have hbound : ∀ e ∈ (lowFace E).support, e 0 ≤ E.q := by
    intro e he
    rw [hsupp] at he
    rcases Finset.mem_image.mp he with ⟨e0, he0, rfl⟩
    simpa only [Finsupp.mapDomain_equiv_apply,
      crossRoofLowPerm_symm_zero] using E.face_two_le_q he0
  have hlo :
      Finsupp.mapDomain crossRoofLowPerm E.hull.lo ∈ (lowFace E).support := by
    rw [hsupp]
    exact Finset.mem_image.mpr ⟨E.hull.lo, E.hull.lo_mem_face, rfl⟩
  have hlo0 : (Finsupp.mapDomain crossRoofLowPerm E.hull.lo) 0 = E.q := by
    simpa only [Finsupp.mapDomain_equiv_apply,
      crossRoofLowPerm_symm_zero] using E.lo_two
  exact coefficientProfile_natDegree_eq_of_bound_endpoint D E.q hbound hlo hlo0

end QsOtherFacetPrLeftVExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
