import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactDropDecomposition
import Mathlib.Tactic

/-!
# A19.100d: primitive direction of the locked transverse contact drop

This file contains only Euclidean arithmetic.  Two positive proportional
endpoint pairs with a strict positive drop lie on one primitive positive ray.
The integral contact gap is the number of primitive steps times the ordinary
degree of that primitive direction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

/-- Positive proportional pairs, together with positive coordinate drops,
factor through one primitive positive direction. -/
theorem positiveProportionalDrop_primitiveDirection
    {B C V W p q r : ℕ}
    (hV : 0 < V) (hW : 0 < W)
    (hp : 0 < p) (hq : 0 < q)
    (hVp : V + p = B) (hWq : W + q = C)
    (hr : r = p + q) (hcross : B * W = C * V) :
    ∃ a b h k : ℕ,
      0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      B = (h + k) * a ∧ C = (h + k) * b ∧
      V = h * a ∧ W = h * b ∧ r = k * (a + b) := by
  let h := Nat.gcd V W
  let a := V / h
  let b := W / h
  have hh : 0 < h := by
    dsimp [h]
    exact Nat.gcd_pos_of_pos_left W hV
  have hVa : V = h * a := by
    dsimp [h, a]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left V W)).symm
  have hWb : W = h * b := by
    dsimp [h, b]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right V W)).symm
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha
    · rw [ha0, mul_zero] at hVa
      omega
    · exact ha
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb
    · rw [hb0, mul_zero] at hWb
      omega
    · exact hb
  have hab : Nat.Coprime a b := by
    exact Nat.coprime_div_gcd_div_gcd hh
  have habCross : B * b = C * a := by
    rw [hWb, hVa] at hcross
    apply Nat.mul_right_cancel hh
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  have haB : a ∣ B := by
    apply hab.dvd_mul_right.mp
    rw [habCross]
    exact dvd_mul_left a C
  let ell := B / a
  have hBell : B = ell * a := by
    dsimp [ell]
    rw [Nat.div_mul_cancel haB]
  have hCell : C = ell * b := by
    apply Nat.mul_right_cancel ha
    calc
      C * a = B * b := habCross.symm
      _ = (ell * b) * a := by rw [hBell]; ac_rfl
  have hhell : h < ell := by
    have hVB : V < B := by omega
    rw [hVa, hBell] at hVB
    exact (Nat.mul_lt_mul_right ha).mp (by simpa [mul_comm] using hVB)
  let k := ell - h
  have hell : h + k = ell := by
    dsimp [k]
    omega
  have hpEq : p = k * a := by
    have hVp' : h * a + p = (h + k) * a := by
      rw [← hVa, hell, ← hBell]
      exact hVp
    rw [Nat.add_mul] at hVp'
    exact Nat.add_left_cancel hVp'
  have hqEq : q = k * b := by
    have hWq' : h * b + q = (h + k) * b := by
      rw [← hWb, hell, ← hCell]
      exact hWq
    rw [Nat.add_mul] at hWq'
    exact Nat.add_left_cancel hWq'
  have hk : 0 < k := by
    rw [hqEq] at hq
    exact Nat.pos_of_mul_pos_right hq
  refine ⟨a, b, h, k, ha, hb, hh, hk, hab, ?_, ?_, hVa, hWb, ?_⟩
  · rw [hell]
    exact hBell
  · rw [hell]
    exact hCell
  · rw [hr, hpEq, hqEq]
    exact (Nat.mul_add k a b).symm

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- `.pr`: primitive direction in transverse coordinates `(2,3)`. -/
theorem qs_ray_pr_integral_contactGap_primitiveDirection
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ r a b h k : ℕ,
      2 ≤ r ∧ 0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.bump = C.scale * r ∧
      C.ray.facetExponent 2 = (h + k) * a ∧
      C.ray.facetExponent 3 = (h + k) * b ∧
      C.ray.outsideExponent 2 = h * a ∧
      C.ray.outsideExponent 3 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_pr_integral_contactGap_positiveDropDecomposition
      hthree houtThree with
    ⟨r, p, q, hr, hp, hq, hbump, h2p, h3q, hrpq, hcross⟩
  have hV : 0 < C.ray.outsideExponent 2 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).2.2.1
  have hW : 0 < C.ray.outsideExponent 3 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).2.2.2
  rcases positiveProportionalDrop_primitiveDirection hV hW hp hq h2p h3q hrpq hcross with
    ⟨a, b, h, k, ha, hb, hh, hk, hab, hB, hC, hV', hW', hr'⟩
  exact ⟨r, a, b, h, k, hr, ha, hb, hh, hk, hab, hbump,
    hB, hC, hV', hW', hr', by omega⟩

/-- `.sp`: primitive direction in transverse coordinates `(1,3)`. -/
theorem qs_ray_sp_integral_contactGap_primitiveDirection
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    ∃ r a b h k : ℕ,
      2 ≤ r ∧ 0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.bump = C.scale * r ∧
      C.ray.facetExponent 1 = (h + k) * a ∧
      C.ray.facetExponent 3 = (h + k) * b ∧
      C.ray.outsideExponent 1 = h * a ∧
      C.ray.outsideExponent 3 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_sp_integral_contactGap_positiveDropDecomposition
      hthree houtThree with
    ⟨r, p, q, hr, hp, hq, hbump, h1p, h3q, hrpq, hcross⟩
  have hV : 0 < C.ray.outsideExponent 1 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree).2.2.1
  have hW : 0 < C.ray.outsideExponent 3 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree).2.2.2
  rcases positiveProportionalDrop_primitiveDirection hV hW hp hq h1p h3q hrpq hcross with
    ⟨a, b, h, k, ha, hb, hh, hk, hab, hB, hC, hV', hW', hr'⟩
  exact ⟨r, a, b, h, k, hr, ha, hb, hh, hk, hab, hbump,
    hB, hC, hV', hW', hr', by omega⟩

/-- `.rq`: primitive direction in transverse coordinates `(1,2)`. -/
theorem qs_ray_rq_integral_contactGap_primitiveDirection
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    ∃ r a b h k : ℕ,
      2 ≤ r ∧ 0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.bump = C.scale * r ∧
      C.ray.facetExponent 1 = (h + k) * a ∧
      C.ray.facetExponent 2 = (h + k) * b ∧
      C.ray.outsideExponent 1 = h * a ∧
      C.ray.outsideExponent 2 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_rq_integral_contactGap_positiveDropDecomposition
      hthree houtThree with
    ⟨r, p, q, hr, hp, hq, hbump, h1p, h2q, hrpq, hcross⟩
  have hV : 0 < C.ray.outsideExponent 1 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree).2.2.1
  have hW : 0 < C.ray.outsideExponent 2 :=
    ((HC4.Newton.mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree).2.2.2
  rcases positiveProportionalDrop_primitiveDirection hV hW hp hq h1p h2q hrpq hcross with
    ⟨a, b, h, k, ha, hb, hh, hk, hab, hB, hC, hV', hW', hr'⟩
  exact ⟨r, a, b, h, k, hr, ha, hb, hh, hk, hab, hbump,
    hB, hC, hV', hW', hr', by omega⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
