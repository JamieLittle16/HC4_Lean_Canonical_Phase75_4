import HC4.Newton.ExposedFaces
import HC4.Newton.FiniteSupportCrossFacetExposure
import HC4.Polynomial.WeightBounds
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# Finite-support exposed-face refinement adapters

The abstract exposed-face calculus already proves that a sufficiently dominant
primary weight can absorb a secondary exposure.  The finite Newton carriers in
HC4, however, are represented by exact `MvPolynomial.initialForm`s.  This file
supplies the two missing state-free adapters:

* an exact initial form with a global upper weight bound is literally an
  `IsExposedFace` on polynomial support;
* on a finite support there is always a positive natural primary scale large
  enough for `refine_exposed_face`.

The latter uses only finiteness: choose a point maximizing the possible
secondary gain and then a natural integer strictly above that maximum.  The
scale may moreover be required to exceed any caller-supplied natural lower
bound, which is what later lets one preserve source-weight nonnegativity and a
positive Hessian clock while collapsing nested Newton faces.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open MvPolynomial

/-- The support of an exact weighted initial form is precisely the abstract
upper exposed face of the source support, provided the source is globally
bounded above by the selected level. -/
theorem initialForm_support_isExposedFace
    {σ K : Type*} [CommSemiring K]
    (w : σ → ℤ) (level : ℤ) (P : MvPolynomial σ K)
    (hLE : HC4.Polynomial.IsWeightLE w level P) :
    IsExposedFace
      (↑P.support : Set (σ →₀ ℕ))
      (↑(HC4.Polynomial.initialForm w level P).support : Set (σ →₀ ℕ))
      (fun d => Finsupp.weight w d) level := by
  classical
  constructor
  · ext d
    change d ∈ (HC4.Polynomial.initialForm w level P).support ↔
      d ∈ P.support ∧ Finsupp.weight w d = level
    constructor
    · intro hd
      have hcoeff := MvPolynomial.mem_support_iff.mp hd
      rw [HC4.Polynomial.coeff_initialForm] at hcoeff
      by_cases hw : Finsupp.weight w d = level
      · rw [if_pos hw] at hcoeff
        exact ⟨MvPolynomial.mem_support_iff.mpr hcoeff, hw⟩
      · rw [if_neg hw] at hcoeff
        exact (hcoeff rfl).elim
    · rintro ⟨hd, hw⟩
      apply MvPolynomial.mem_support_iff.mpr
      rw [HC4.Polynomial.coeff_initialForm, if_pos hw]
      exact MvPolynomial.mem_support_iff.mp hd
  · intro d hd
    change d ∈ P.support at hd
    exact hLE hd

/-- A finite family of integer secondary gains has a positive natural strict
upper bound. -/
theorem exists_positive_nat_strict_upper_bound_on_finset
    {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    (gain : α → ℤ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ S, gain x < (M : ℤ) := by
  rcases Finset.exists_max_image S gain hS with ⟨x, hx, hmax⟩
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (gain x)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  intro y hy
  have hyN : gain y < (N : ℤ) := lt_of_le_of_lt (hmax y hy) hN
  have hNs : (N : ℤ) < ((N + 1 : ℕ) : ℤ) := by omega
  exact lt_trans hyN hNs

/-- **Finite lexicographic exposed-face collapse.**

If `F` is exposed in a finite support `S` and `G` is exposed inside `F`, then
some positive natural scale `M` makes the single weight `M*w+v` expose `G`
directly in `S`. -/
theorem exists_nat_refine_exposed_face
    {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    {F G : Set α} {w v : α → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set α) F w c)
    (hG : IsExposedFace F G v d) :
    ∃ M : ℕ, 0 < M ∧
      IsExposedFace (↑S : Set α) G
        (fun x => (M : ℤ) * w x + v x)
        ((M : ℤ) * c + d) := by
  rcases exists_positive_nat_strict_upper_bound_on_finset
      S hS (fun x => v x - d) with ⟨M, hM, hsecondary⟩
  refine ⟨M, hM, refine_exposed_face hF hG ?_⟩
  intro x hxS hxNotF
  have hxSfin : x ∈ S := by simpa using hxS
  have hwle : w x ≤ c := hF.weight_le hxS
  have hwne : w x ≠ c := by
    intro hw
    exact hxNotF (hF.mem_iff.mpr ⟨hxS, hw⟩)
  have hprimary : 1 ≤ c - w x := by omega
  have hsecondary' : v x - d < (M : ℤ) := hsecondary x hxSfin
  have hMnonneg : (0 : ℤ) ≤ (M : ℤ) := by positivity
  have hdom : (M : ℤ) ≤ (M : ℤ) * (c - w x) := by
    nlinarith
  exact lt_of_lt_of_le hsecondary' hdom

/-- The refinement scale can be taken beyond any prescribed natural lower
bound.  This strengthened form is the one used when later covariance requires
all combined source weights and the resulting determinant clock to stay
nonnegative. -/
theorem exists_nat_refine_exposed_face_ge
    {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    {F G : Set α} {w v : α → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set α) F w c)
    (hG : IsExposedFace F G v d)
    (B : ℕ) :
    ∃ M : ℕ, B ≤ M ∧ 0 < M ∧
      IsExposedFace (↑S : Set α) G
        (fun x => (M : ℤ) * w x + v x)
        ((M : ℤ) * c + d) := by
  rcases exists_positive_nat_strict_upper_bound_on_finset
      S hS (fun x => v x - d) with ⟨M₀, hM₀, hsecondary⟩
  let M := M₀ + B
  have hBM : B ≤ M := by
    dsimp [M]
    omega
  have hM : 0 < M := by
    dsimp [M]
    omega
  refine ⟨M, hBM, hM, refine_exposed_face hF hG ?_⟩
  intro x hxS hxNotF
  have hxSfin : x ∈ S := by simpa using hxS
  have hwle : w x ≤ c := hF.weight_le hxS
  have hwne : w x ≠ c := by
    intro hw
    exact hxNotF (hF.mem_iff.mpr ⟨hxS, hw⟩)
  have hprimary : 1 ≤ c - w x := by omega
  have hsecondary₀ : v x - d < (M₀ : ℤ) := hsecondary x hxSfin
  have hM₀M : (M₀ : ℤ) ≤ (M : ℤ) := by
    dsimp [M]
    omega
  have hsecondary' : v x - d < (M : ℤ) :=
    lt_of_lt_of_le hsecondary₀ hM₀M
  have hMnonneg : (0 : ℤ) ≤ (M : ℤ) := by positivity
  have hdom : (M : ℤ) ≤ (M : ℤ) * (c - w x) := by
    nlinarith
  exact lt_of_lt_of_le hsecondary' hdom

/-- Every finite cross-facet exposure is an exposed face in the abstract
calculus, with exactly the stored signed secondary weight and level. -/
theorem CrossFacetInitialData.support_isExposedFace
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j) :
    IsExposedFace
      (↑F.support : Set (Fin 4 →₀ ℕ))
      (↑D.face.support : Set (Fin 4 →₀ ℕ))
      (fun e => Finsupp.weight (crossFacetWeight i j D.scale D.bump) e)
      D.level := by
  rw [D.face_eq]
  exact initialForm_support_isExposedFace
    (crossFacetWeight i j D.scale D.bump) D.level F D.weight_bound

end

end HC4.Newton
