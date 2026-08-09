import HC4.Polynomial.FourExponent
import HC4.MongeAmpere.FirstContactMaximal

/-!
# Denominator-cleared first-contact weights

The manuscript exposes the first support outside a chosen top facet using
`(1,1,1,1) + λ e_j`.  For rational `λ = bump / scale`, this module works
entirely with natural/integer arithmetic after clearing denominators.
-/

namespace HC4.Newton

open HC4.Polynomial
open scoped BigOperators

/-- Cleared first-contact weight: base weight `scale`, with an extra `bump` in coordinate `j`. -/
def scaledContactWeight (j : Fin 4) (scale bump : ℕ) : Fin 4 → ℤ :=
  fun i => (scale : ℤ) + if i = j then (bump : ℤ) else 0

/-- The four variable weights have the denominator-cleared sum `4*scale+bump`. -/
theorem sum_scaledContactWeight (j : Fin 4) (scale bump : ℕ) :
    ∑ i : Fin 4, scaledContactWeight j scale bump i =
      ((4 * scale + bump : ℕ) : ℤ) := by
  fin_cases j <;> simp [scaledContactWeight, Fin.sum_univ_four] <;> push_cast <;> ring

/-- The Phase-50 first-contact singularity theorem specialised to the canonical cleared weight. -/
theorem scaledContact_hessianDeterminant_eq_zero_of_isWeightLE
    {K : Type*} [CommRing K] [Nontrivial K]
    {j : Fin 4} {level scale bump : ℕ} {ψ : MvPolynomial (Fin 4) K}
    (hscale : 0 < scale) (hcontact : bump + 3 * scale ≤ level)
    (hbound : HC4.Polynomial.IsWeightLE
      (scaledContactWeight j scale bump) (level : ℤ) ψ)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere ψ) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm (scaledContactWeight j scale bump) (level : ℤ) ψ) = 0 := by
  exact HC4.MongeAmpere.first_contact_scaled_hessianDeterminant_eq_zero_of_isWeightLE
    hscale hcontact hbound (sum_scaledContactWeight j scale bump) hMA

/-- Cleared first-contact weight of a monomial exponent. -/
def scaledContactExponentWeight (j : Fin 4) (scale bump : ℕ)
    (d : Fin 4 →₀ ℕ) : ℤ :=
  (scale : ℤ) * ordinaryDegree4 d + (bump : ℤ) * (d j : ℤ)


/-- The abstract `Finsupp.weight` of the cleared contact weight is the explicit
ordinary-degree-plus-bump formula used in the manuscript. -/
theorem weight_scaledContactWeight
    (j : Fin 4) (scale bump : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (scaledContactWeight j scale bump) d =
      scaledContactExponentWeight j scale bump d := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · fin_cases j <;>
      simp [scaledContactWeight, scaledContactExponentWeight, ordinaryDegree4,
        Fin.sum_univ_four] <;> ring
  · intro i
    simp

/-- A support-level cleared contact inequality can therefore be stated using
`scaledContactExponentWeight` without changing the `IsWeightLE` predicate. -/
theorem isWeightLE_scaledContactWeight_iff
    {K : Type*} [CommRing K]
    (j : Fin 4) (scale bump level : ℕ) (p : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.IsWeightLE (scaledContactWeight j scale bump) (level : ℤ) p ↔
      ∀ d ∈ p.support, scaledContactExponentWeight j scale bump d ≤ (level : ℤ) := by
  constructor <;> intro h d hd
  · simpa [weight_scaledContactWeight] using h hd
  · simpa [weight_scaledContactWeight] using h d hd

/-- Any monomial of ordinary degree at most two with at most one copy of the
bumped coordinate lies strictly below a genuine nonlinear contact. -/
theorem lowDegree_below_scaled_contact
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hscale : 0 < scale) (hdeg : ordinaryDegree4 d ≤ 2) (hj : d j ≤ 1)
    (hbump : bump ≤ scale * (m - 3)) (hm : 3 ≤ m) :
    scaledContactExponentWeight j scale bump d < (scale * m : ℕ) := by
  unfold scaledContactExponentWeight
  have hdegZ : (ordinaryDegree4 d : ℤ) ≤ 2 := by exact_mod_cast hdeg
  have hjZ : (d j : ℤ) ≤ 1 := by exact_mod_cast hj
  have hbumpZ : (bump : ℤ) ≤ scale * (m - 3) := by exact_mod_cast hbump
  have hscaleZ : (0 : ℤ) < scale := by exact_mod_cast hscale
  have hmZ : (3 : ℤ) ≤ m := by exact_mod_cast hm
  push_cast
  nlinarith

/-- A top-facet monomial of ordinary degree `m` has contact weight `scale*m`. -/
theorem scaledContact_top_facet
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hj : d j = 0) (hdeg : ordinaryDegree4 d = m) :
    scaledContactExponentWeight j scale bump d = (scale * m : ℕ) := by
  simp [scaledContactExponentWeight, hj, hdeg]

/-- A contact exponent satisfies the denominator-cleared contact equation. -/
theorem contact_equation
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hcontact : scaledContactExponentWeight j scale bump d = (scale * m : ℕ)) :
    (bump : ℤ) * (d j : ℤ) = (scale : ℤ) * ((m : ℤ) - ordinaryDegree4 d) := by
  unfold scaledContactExponentWeight at hcontact
  push_cast at hcontact ⊢
  linarith

/-- For a genuine outside-facet contact, ordinary degree is strictly below the top degree. -/
theorem contact_degree_lt
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hscale : 0 < scale) (hbump : 0 < bump) (hj : 0 < d j)
    (hcontact : scaledContactExponentWeight j scale bump d = (scale * m : ℕ)) :
    ordinaryDegree4 d < m := by
  have heq := contact_equation hcontact
  have hpos : (0 : ℤ) < (bump : ℤ) * (d j : ℤ) := by
    positivity
  have hscaleZ : (0 : ℤ) < (scale : ℤ) := by exact_mod_cast hscale
  have hdiff : (0 : ℤ) < (m : ℤ) - ordinaryDegree4 d := by
    nlinarith
  exact_mod_cast (show (ordinaryDegree4 d : ℤ) < m by linarith)

/-- The manuscript bound `λ ≤ m-3`, after denominator clearing. -/
theorem bump_le_scale_mul_m_sub_three
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hscale : 0 < scale) (hj : 0 < d j)
    (hdeg : 3 ≤ ordinaryDegree4 d)
    (hcontact : scaledContactExponentWeight j scale bump d = (scale * m : ℕ)) :
    bump ≤ scale * (m - 3) := by
  have heq := contact_equation hcontact
  have hmdeg : ordinaryDegree4 d ≤ m := by
    by_contra hnot
    have : m < ordinaryDegree4 d := by omega
    have hscaleZ : (0 : ℤ) < (scale : ℤ) := by exact_mod_cast hscale
    have hjZ : (0 : ℤ) < (d j : ℤ) := by exact_mod_cast hj
    have hbumpNonneg : (0 : ℤ) ≤ bump := by positivity
    nlinarith
  have hj1 : 1 ≤ d j := hj
  have heqNat : bump * d j = scale * (m - ordinaryDegree4 d) := by
    exact_mod_cast heq
  have hbump : bump ≤ bump * d j := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left bump hj1
  have hsub : m - ordinaryDegree4 d ≤ m - 3 := Nat.sub_le_sub_left hdeg m
  calc
    bump ≤ bump * d j := hbump
    _ = scale * (m - ordinaryDegree4 d) := heqNat
    _ ≤ scale * (m - 3) := Nat.mul_le_mul_left scale hsub

/-- Quadratic monomials with at most one copy of the bumped coordinate lie strictly below contact. -/
theorem quadratic_below_scaled_contact
    {j : Fin 4} {scale bump m : ℕ} {d : Fin 4 →₀ ℕ}
    (hscale : 0 < scale) (hdeg : ordinaryDegree4 d = 2) (hj : d j ≤ 1)
    (hbump : bump ≤ scale * (m - 3)) (hm : 3 ≤ m) :
    scaledContactExponentWeight j scale bump d < (scale * m : ℕ) := by
  unfold scaledContactExponentWeight
  have hjZ : (d j : ℤ) ≤ 1 := by exact_mod_cast hj
  have hbumpZ : (bump : ℤ) ≤ scale * (m - 3) := by exact_mod_cast hbump
  have hscaleZ : (0 : ℤ) < scale := by exact_mod_cast hscale
  rw [hdeg]
  push_cast
  have hmZ : (3 : ℤ) ≤ m := by exact_mod_cast hm
  nlinarith

end HC4.Newton
