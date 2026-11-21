import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseRightLowerHull
import HC4.Newton.FiniteSupportExposedVertex
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# The mirrored unit source lower hull reaches the opposite roof

The right unit lower-hull wall lives in source deficits `(e₁,e₃)`.  Its exact
singular initial face must meet the opposite `e₃=0` roof.  Otherwise a
coordinate-max refinement isolates a source monomial with all four coordinates
positive, contradicting the characteristic-zero monomial Hessian obstruction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrUnitRightLowerHullData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitRightContactFrontierData C P S R}

def gap (D : QsOtherFacetPrUnitRightLowerHullData F) : ℕ :=
  D.lo 3 - D.edge 3

def weight (D : QsOtherFacetPrUnitRightLowerHullData F) : Fin 4 → ℤ :=
  fun i => if i = (1 : Fin 4) then -(D.gap : ℤ)
    else if i = (3 : Fin 4) then -(D.edge 1 : ℤ) else 0

def level (D : QsOtherFacetPrUnitRightLowerHullData F) : ℤ :=
  -(D.edge 1 : ℤ) * (D.lo 3 : ℤ)

def face (D : QsOtherFacetPrUnitRightLowerHullData F) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm D.weight D.level P.carrier

@[simp] theorem gap_pos (D : QsOtherFacetPrUnitRightLowerHullData F) : 0 < D.gap := by
  exact Nat.sub_pos_of_lt D.edge_three_lt

theorem weight_eq (D : QsOtherFacetPrUnitRightLowerHullData F)
    (e : Fin 4 →₀ ℕ) :
    Finsupp.weight D.weight e =
      -(D.gap : ℤ) * (e 1 : ℤ) - (D.edge 1 : ℤ) * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [weight, Fin.sum_univ_four]
    ring
  · intro i
    simp

theorem weight_bound (D : QsOtherFacetPrUnitRightLowerHullData F) :
    HC4.Polynomial.IsWeightLE D.weight D.level P.carrier := by
  intro e he
  rw [D.weight_eq]
  dsimp [level]
  have h := D.lower_bound e he
  have hle : D.edge 3 ≤ D.lo 3 := Nat.le_of_lt D.edge_three_lt
  have hgapCast : (D.gap : ℤ) = (D.lo 3 : ℤ) - (D.edge 3 : ℤ) := by
    dsimp [gap]
    rw [Nat.cast_sub hle]
  rw [hgapCast]
  nlinarith [h]

theorem lo_weight_eq (D : QsOtherFacetPrUnitRightLowerHullData F) :
    Finsupp.weight D.weight D.lo = D.level := by
  rw [D.weight_eq]
  dsimp [level]
  rw [D.lo_one_zero]
  norm_num

theorem edge_weight_eq (D : QsOtherFacetPrUnitRightLowerHullData F) :
    Finsupp.weight D.weight D.edge = D.level := by
  rw [D.weight_eq]
  dsimp [level]
  have hle : D.edge 3 ≤ D.lo 3 := Nat.le_of_lt D.edge_three_lt
  have hgapCast : (D.gap : ℤ) = (D.lo 3 : ℤ) - (D.edge 3 : ℤ) := by
    dsimp [gap]
    rw [Nat.cast_sub hle]
  rw [hgapCast]
  ring

theorem lo_mem_face (D : QsOtherFacetPrUnitRightLowerHullData F) :
    D.lo ∈ D.face.support := by
  apply MvPolynomial.mem_support_iff.mpr
  dsimp [face]
  rw [HC4.Polynomial.coeff_initialForm, if_pos D.lo_weight_eq]
  exact MvPolynomial.mem_support_iff.mp D.lo_mem

theorem edge_mem_face (D : QsOtherFacetPrUnitRightLowerHullData F) :
    D.edge ∈ D.face.support := by
  apply MvPolynomial.mem_support_iff.mpr
  dsimp [face]
  rw [HC4.Polynomial.coeff_initialForm, if_pos D.edge_weight_eq]
  exact MvPolynomial.mem_support_iff.mp D.edge_mem

theorem face_support_subset (D : QsOtherFacetPrUnitRightLowerHullData F) :
    D.face.support ⊆ P.carrier.support := by
  dsimp [face]
  exact HC4.Polynomial.support_initialForm_subset D.weight D.level P.carrier

theorem cost_eq_of_mem_face
    (D : QsOtherFacetPrUnitRightLowerHullData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ D.face.support) :
    (D.gap : ℤ) * (e 1 : ℤ) + (D.edge 1 : ℤ) * (e 3 : ℤ) =
      (D.edge 1 : ℤ) * (D.lo 3 : ℤ) := by
  have hhom := HC4.Polynomial.initialForm_isWeightedHomogeneous
    D.weight D.level P.carrier
  have hw := hhom (MvPolynomial.mem_support_iff.mp he)
  rw [D.weight_eq] at hw
  dsimp [level] at hw
  nlinarith [hw]

theorem face_hessian_zero (D : QsOtherFacetPrUnitRightLowerHullData F) :
    HC4.Polynomial.hessianDeterminant D.face = 0 := by
  dsimp [face]
  exact HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
    D.weight D.level P.carrier D.weight_bound P.hessian_zero

/-- The exact mirrored unit lower-hull face meets `e₃=0`. -/
theorem exists_wRoof_on_face
    (D : QsOtherFacetPrUnitRightLowerHullData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ e ∈ D.face.support, e 3 = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfaceNe : D.face ≠ 0 :=
    MvPolynomial.support_nonempty.mp ⟨D.edge, D.edge_mem_face⟩
  let E := HC4.Newton.coordinateMaxInitialData D.face hfaceNe (1 : Fin 4)
  let d := E.witness
  have hdFace : d ∈ D.face.support := E.witness_mem
  have hdP : d ∈ P.carrier.support := D.face_support_subset hdFace
  have hlevelPos : 0 < E.level := by
    have hle := E.maximal D.edge D.edge_mem_face
    exact lt_of_lt_of_le D.edge_one_pos hle
  have hd1pos : 0 < d 1 := by
    dsimp [d]
    rw [E.witness_coordinate]
    exact hlevelPos
  have hd3pos : 0 < d 3 := Nat.pos_of_ne_zero (hnone d hdFace)

  have hd0pos : 0 < d 0 := by
    by_contra hnot
    have hd0 : d 0 = 0 := Nat.eq_zero_of_not_pos hnot
    have hwall := F.support_deficit_wall hthree houtThree hdP
    rw [hd0] at hwall
    norm_num at hwall
    rcases F.locked_yRoof_mem with ⟨hLmem, _hL0, hL1, _hL2, hL3⟩
    rcases F.highest_wRoof_mem with ⟨hHmem, _hH0, hH1, _hH2, hH3⟩
    have hcost := D.cost_eq_of_mem_face hdFace
    have hlockedRaw := D.lower_bound C.ray.outsideExponent hLmem
    rw [hL1, hL3] at hlockedRaw
    norm_num at hlockedRaw
    have hhighestRaw := D.lower_bound F.highest.e1 hHmem
    rw [hH1, hH3] at hhighestRaw
    norm_num at hhighestRaw
    have hle : D.edge 3 ≤ D.lo 3 := Nat.le_of_lt D.edge_three_lt
    have hgapCast : (D.gap : ℤ) = (D.lo 3 : ℤ) - (D.edge 3 : ℤ) := by
      dsimp [gap]
      rw [Nat.cast_sub hle]
    have hlocked :
        (D.gap : ℤ) * (d 1 : ℤ) + (D.edge 1 : ℤ) * (d 3 : ℤ) ≤
          (D.edge 1 : ℤ) * (F.locked.ell : ℤ) := by
      rw [hgapCast] at hcost ⊢
      calc
        ((D.lo 3 : ℤ) - (D.edge 3 : ℤ)) * (d 1 : ℤ) +
            (D.edge 1 : ℤ) * (d 3 : ℤ) =
          (D.edge 1 : ℤ) * (D.lo 3 : ℤ) := hcost
        _ ≤ (D.edge 1 : ℤ) * (F.locked.ell : ℤ) := hlockedRaw
    have hhighest :
        (D.gap : ℤ) * (d 1 : ℤ) + (D.edge 1 : ℤ) * (d 3 : ℤ) ≤
          (D.gap : ℤ) * ((F.highest.n : ℤ) - 1) := by
      rw [hgapCast] at hcost ⊢
      have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
      have hn1 : 1 ≤ F.highest.n := by omega
      have hcast : ((F.highest.n - 1 : ℕ) : ℤ) = (F.highest.n : ℤ) - 1 := by
        rw [Nat.cast_sub hn1]
        norm_num
      rw [hcast] at hhighestRaw
      calc
        ((D.lo 3 : ℤ) - (D.edge 3 : ℤ)) * (d 1 : ℤ) +
            (D.edge 1 : ℤ) * (d 3 : ℤ) =
          (D.edge 1 : ℤ) * (D.lo 3 : ℤ) := hcost
        _ ≤ ((D.lo 3 : ℤ) - (D.edge 3 : ℤ)) *
            ((F.highest.n : ℤ) - 1) := hhighestRaw
    exact HC4.Polynomial.zeroLongitudinal_not_positive_lowerHull
      (n := F.highest.n) (ell := F.locked.ell)
      (a := d 1) (b := d 3) (A := D.gap) (B := D.edge 1)
      F.highest.n_two_le F.locked.ell_pos hd1pos hd3pos
      D.gap_pos D.edge_one_pos hwall hlocked hhighest

  have hd2pos : 0 < d 2 := by
    have hcurve := (F.support_staircase_equations hthree houtThree hdP).2
    simp only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      HC4.Polynomial.rankThreeQuotientCoordinate_pair,
      HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      one_mul] at hcurve
    push_cast at hcurve
    by_contra hnot
    have hd2 : d 2 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hd2] at hcurve
    norm_num at hcurve
    have hd0Z : (0 : ℤ) < (d 0 : ℤ) := by exact_mod_cast hd0pos
    have hd1Z : (0 : ℤ) < (d 1 : ℤ) := by exact_mod_cast hd1pos
    have hd3Z : (0 : ℤ) < (d 3 : ℤ) := by exact_mod_cast hd3pos
    nlinarith only [hcurve, hd0Z, hd1Z, hd3Z]

  have hpos : ∀ i : Fin 4, 0 < d i := by
    intro i
    fin_cases i
    · exact hd0pos
    · exact hd1pos
    · exact hd2pos
    · exact hd3pos
  have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
    simp [HC4.Polynomial.ordinaryDegree4]
    omega
  have hdParent : d ∈ D.face.support := E.witness_mem
  have hdCost := D.cost_eq_of_mem_face hdParent
  have hunique : ∀ q ∈ E.face.support, q = d := by
    intro q hq
    have hqParent : q ∈ D.face.support := E.support_subset hq
    have hqP : q ∈ P.carrier.support := D.face_support_subset hqParent
    have hq1 : q 1 = d 1 := by
      have hqeq := E.coordinate_eq q hq
      have hdeq : d 1 = E.level := by simpa [d] using E.witness_coordinate
      exact hqeq.trans hdeq.symm
    have hqCost := D.cost_eq_of_mem_face hqParent
    have hBne : (D.edge 1 : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt D.edge_one_pos)
    have hfactor : (D.edge 1 : ℤ) * ((q 3 : ℤ) - (d 3 : ℤ)) = 0 := by
      have hq1Z : (q 1 : ℤ) = (d 1 : ℤ) := by exact_mod_cast hq1
      nlinarith only [hqCost, hdCost, hq1Z]
    have hq3Z : (q 3 : ℤ) = (d 3 : ℤ) := by
      have hz := (mul_eq_zero.mp hfactor).resolve_left hBne
      linarith
    have hq3 : q 3 = d 3 := by exact_mod_cast hq3Z
    exact F.support_eq_of_deficits_eq hthree houtThree hqP hdP hq1 hq3

  let c : K := MvPolynomial.coeff d E.face
  have hc : c ≠ 0 := by
    dsimp [c]
    have hcoeff : MvPolynomial.coeff d E.face = MvPolynomial.coeff d D.face := by
      rw [E.face_eq, HC4.Polynomial.coeff_initialForm,
        HC4.Newton.weight_coordinateMaxWeight]
      have hd1 : d 1 = E.level := by simpa [d] using E.witness_coordinate
      simp [hd1]
    rw [hcoeff]
    exact MvPolynomial.mem_support_iff.mp E.witness_mem
  have hmono : E.face = MvPolynomial.monomial d c := by
    apply MvPolynomial.ext
    intro q
    by_cases hqd : q = d
    · subst q
      simp [c]
    · have hq0 : MvPolynomial.coeff q E.face = 0 := by
        by_contra hne
        have hqs : q ∈ E.face.support := MvPolynomial.mem_support_iff.mpr hne
        exact hqd (hunique q hqs)
      have hdq : d ≠ q := by intro hdq; exact hqd hdq.symm
      rw [hq0]
      simp [hdq]
  have hEzero : HC4.Polynomial.hessianDeterminant E.face = 0 :=
    E.hessian_zero D.face_hessian_zero
  have hnonzero := HC4.Polynomial.hessianDeterminant_monomial_ne_zero
    (K := K) hc hpos hdeg
  apply hnonzero
  rw [← hmono]
  exact hEzero

/-- Source-facing opposite-roof point on the exact mirrored face. -/
theorem exists_source_wRoof_on_face
    (D : QsOtherFacetPrUnitRightLowerHullData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ e ∈ P.carrier.support,
      e 3 = 0 ∧
      (D.gap : ℤ) * (e 1 : ℤ) = (D.edge 1 : ℤ) * (D.lo 3 : ℤ) := by
  rcases D.exists_wRoof_on_face hthree houtThree with ⟨e, heFace, he3⟩
  have heP := D.face_support_subset heFace
  have hcost := D.cost_eq_of_mem_face heFace
  rw [he3] at hcost
  norm_num at hcost
  exact ⟨e, heP, he3, hcost⟩

end QsOtherFacetPrUnitRightLowerHullData
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end
end HC4.Valuation