import HC4.Newton.ScaledContact
import Mathlib.Data.Finset.Max

/-!
# Constructing the first nonlinear contact from finite support

This module removes the remaining existential choice hidden in the manuscript's
formula

  λ = min_{u_j>0} (m - |u|) / u_j.

The minimum is taken on the actual finite `MvPolynomial` support.  The selected
exponent itself supplies a denominator-cleared weight

  scale = u_j,  bump = m - |u|.

The resulting weight has every supported monomial weakly below the contact
level, provided the nonlinear degree-`m` part lies in the chosen facet and the
fixed low-degree terms use the bumped coordinate at most once.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

/-- Nonlinear supported exponents lying outside the coordinate facet `x_j=0`. -/
def nonlinearOutsideSupport {K : Type*} [CommSemiring K]
    (j : Fin 4) (p : MvPolynomial (Fin 4) K) : Finset (Fin 4 →₀ ℕ) :=
  p.support.filter fun d => 3 ≤ ordinaryDegree4 d ∧ 0 < d j

@[simp] theorem mem_nonlinearOutsideSupport {K : Type*} [CommSemiring K]
    {j : Fin 4} {p : MvPolynomial (Fin 4) K} {d : Fin 4 →₀ ℕ} :
    d ∈ nonlinearOutsideSupport j p ↔
      d ∈ p.support ∧ 3 ≤ ordinaryDegree4 d ∧ 0 < d j := by
  simp [nonlinearOutsideSupport, and_assoc]

/-- The rational contact slope attached to an outside nonlinear exponent. -/
def contactSlope (m : ℕ) (j : Fin 4) (d : Fin 4 →₀ ℕ) : ℚ :=
  ((m - ordinaryDegree4 d : ℕ) : ℚ) / (d j : ℚ)

/-- Finite support contains an exponent with minimal contact slope. -/
theorem exists_minimal_contactExponent
    {K : Type*} [CommSemiring K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    (hne : (nonlinearOutsideSupport j p).Nonempty) :
    ∃ d₀ ∈ nonlinearOutsideSupport j p,
      ∀ d ∈ nonlinearOutsideSupport j p,
        contactSlope m j d₀ ≤ contactSlope m j d := by
  exact Finset.exists_min_image _ _ hne

/-- Comparing positive-denominator contact slopes is exactly the cleared
cross-multiplication inequality. -/
theorem contactSlope_le_iff_cross
    {m : ℕ} {j : Fin 4} {d₀ d : Fin 4 →₀ ℕ}
    (hd₀ : 0 < d₀ j) (hd : 0 < d j) :
    contactSlope m j d₀ ≤ contactSlope m j d ↔
      (m - ordinaryDegree4 d₀) * d j ≤
        (m - ordinaryDegree4 d) * d₀ j := by
  have hd₀Q : (0 : ℚ) < (d₀ j : ℚ) := by exact_mod_cast hd₀
  have hdQ : (0 : ℚ) < (d j : ℚ) := by exact_mod_cast hd
  rw [contactSlope, contactSlope]
  rw [div_le_div_iff₀ hd₀Q hdQ]
  norm_cast

/-- The selected outside exponent has strictly smaller ordinary degree than
`m` when all degree-`m` nonlinear terms lie in the coordinate facet. -/
theorem selected_contact_degree_lt
    {K : Type*} [CommSemiring K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    {d₀ : Fin 4 →₀ ℕ}
    (hd₀ : d₀ ∈ nonlinearOutsideSupport j p)
    (hdeg : ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m)
    (htop : ∀ d ∈ p.support, ordinaryDegree4 d = m → d j = 0) :
    ordinaryDegree4 d₀ < m := by
  have hsupp : d₀ ∈ p.support := (mem_nonlinearOutsideSupport.mp hd₀).1
  have hnonlin : 3 ≤ ordinaryDegree4 d₀ := (mem_nonlinearOutsideSupport.mp hd₀).2.1
  have hj : 0 < d₀ j := (mem_nonlinearOutsideSupport.mp hd₀).2.2
  have hle := hdeg d₀ hsupp hnonlin
  apply lt_of_le_of_ne hle
  intro heq
  have hz := htop d₀ hsupp heq
  omega

/-- The exponent chosen by the minimum itself gives a genuine cleared contact
at level `scale*m`, with positive scale and bump. -/
theorem selected_contact_level
    {K : Type*} [CommSemiring K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    {d₀ : Fin 4 →₀ ℕ}
    (hd₀ : d₀ ∈ nonlinearOutsideSupport j p)
    (hdeg : ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m)
    (htop : ∀ d ∈ p.support, ordinaryDegree4 d = m → d j = 0) :
    let scale := d₀ j
    let bump := m - ordinaryDegree4 d₀
    0 < scale ∧ 0 < bump ∧
      scaledContactExponentWeight j scale bump d₀ = (scale * m : ℕ) := by
  intro scale bump
  have hj : 0 < d₀ j := (mem_nonlinearOutsideSupport.mp hd₀).2.2
  have hlt := selected_contact_degree_lt hd₀ hdeg htop
  have hle : ordinaryDegree4 d₀ ≤ m := Nat.le_of_lt hlt
  refine ⟨hj, Nat.sub_pos_of_lt hlt, ?_⟩
  unfold scaledContactExponentWeight
  simp only [scale, bump]
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- Minimality of the rational contact slope gives the exact cleared support
inequality for every nonlinear exponent outside the chosen facet. -/
theorem selected_contact_outside_le
    {K : Type*} [CommSemiring K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    {d₀ : Fin 4 →₀ ℕ}
    (hd₀ : d₀ ∈ nonlinearOutsideSupport j p)
    (hmin : ∀ d ∈ nonlinearOutsideSupport j p,
      contactSlope m j d₀ ≤ contactSlope m j d)
    (hdeg : ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ nonlinearOutsideSupport j p) :
    let scale := d₀ j
    let bump := m - ordinaryDegree4 d₀
    scaledContactExponentWeight j scale bump d ≤ (scale * m : ℕ) := by
  intro scale bump
  have hd₀j : 0 < d₀ j := (mem_nonlinearOutsideSupport.mp hd₀).2.2
  have hdj : 0 < d j := (mem_nonlinearOutsideSupport.mp hd).2.2
  have hcross :
      (m - ordinaryDegree4 d₀) * d j ≤
        (m - ordinaryDegree4 d) * d₀ j :=
    (contactSlope_le_iff_cross hd₀j hdj).mp (hmin d hd)
  have hdegdm : ordinaryDegree4 d ≤ m :=
    hdeg d (mem_nonlinearOutsideSupport.mp hd).1
      (mem_nonlinearOutsideSupport.mp hd).2.1
  have hNat :
      d₀ j * ordinaryDegree4 d + (m - ordinaryDegree4 d₀) * d j ≤
        d₀ j * m := by
    calc
      d₀ j * ordinaryDegree4 d + (m - ordinaryDegree4 d₀) * d j
          ≤ d₀ j * ordinaryDegree4 d + (m - ordinaryDegree4 d) * d₀ j :=
            Nat.add_le_add_left hcross _
      _ = d₀ j * (ordinaryDegree4 d + (m - ordinaryDegree4 d)) := by ring
      _ = d₀ j * m := by rw [Nat.add_comm, Nat.sub_add_cancel hdegdm]
  unfold scaledContactExponentWeight
  simp only [scale, bump]
  exact_mod_cast hNat

/-- The manuscript's first-contact minimum produces a genuine global
`IsWeightLE` bound on the whole polynomial support.  Low-degree terms are
handled separately, matching the fixed quadratic part of the HC4 potential. -/
theorem selected_contact_isWeightLE
    {K : Type*} [CommRing K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    {d₀ : Fin 4 →₀ ℕ}
    (hd₀ : d₀ ∈ nonlinearOutsideSupport j p)
    (hmin : ∀ d ∈ nonlinearOutsideSupport j p,
      contactSlope m j d₀ ≤ contactSlope m j d)
    (hdeg : ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m)
    (htop : ∀ d ∈ p.support, ordinaryDegree4 d = m → d j = 0)
    (hlow : ∀ d ∈ p.support, ordinaryDegree4 d < 3 → d j ≤ 1) :
    let scale := d₀ j
    let bump := m - ordinaryDegree4 d₀
    HC4.Polynomial.IsWeightLE
      (scaledContactWeight j scale bump) (scale * m : ℕ) p := by
  intro scale bump
  rw [isWeightLE_scaledContactWeight_iff]
  intro d hd
  have hlevel := selected_contact_level hd₀ hdeg htop
  dsimp only at hlevel
  have hscale : 0 < d₀ j := hlevel.1
  have hcontact₀ := hlevel.2.2
  have hbumpBound : m - ordinaryDegree4 d₀ ≤ d₀ j * (m - 3) :=
    bump_le_scale_mul_m_sub_three hscale
      (mem_nonlinearOutsideSupport.mp hd₀).2.2
      (mem_nonlinearOutsideSupport.mp hd₀).2.1 hcontact₀
  by_cases hnonlin : 3 ≤ ordinaryDegree4 d
  · have hdegdm := hdeg d hd hnonlin
    by_cases hj0 : d j = 0
    · unfold scaledContactExponentWeight
      simp [hj0]
      exact_mod_cast Nat.mul_le_mul_left (d₀ j) hdegdm
    · have hjpos : 0 < d j := Nat.pos_of_ne_zero hj0
      have hdOut : d ∈ nonlinearOutsideSupport j p := by
        exact mem_nonlinearOutsideSupport.mpr ⟨hd, hnonlin, hjpos⟩
      exact selected_contact_outside_le hd₀ hmin hdeg hdOut
  · have hdeg2 : ordinaryDegree4 d ≤ 2 := by omega
    have hj1 := hlow d hd (by omega)
    exact (lowDegree_below_scaled_contact hscale hdeg2 hj1 hbumpBound hm).le

/-- A first-contact witness is constructible from every nonempty outside
nonlinear support. -/
theorem exists_selected_contact_isWeightLE
    {K : Type*} [CommRing K]
    {m : ℕ} {j : Fin 4} {p : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hout : (nonlinearOutsideSupport j p).Nonempty)
    (hdeg : ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m)
    (htop : ∀ d ∈ p.support, ordinaryDegree4 d = m → d j = 0)
    (hlow : ∀ d ∈ p.support, ordinaryDegree4 d < 3 → d j ≤ 1) :
    ∃ d₀ ∈ nonlinearOutsideSupport j p,
      let scale := d₀ j
      let bump := m - ordinaryDegree4 d₀
      0 < scale ∧ 0 < bump ∧
      HC4.Polynomial.IsWeightLE
        (scaledContactWeight j scale bump) (scale * m : ℕ) p := by
  rcases exists_minimal_contactExponent (m := m) hout with ⟨d₀, hd₀, hmin⟩
  refine ⟨d₀, hd₀, ?_⟩
  dsimp only
  have hlevel := selected_contact_level hd₀ hdeg htop
  dsimp only at hlevel
  exact ⟨hlevel.1, hlevel.2.1,
    selected_contact_isWeightLE hm hd₀ hmin hdeg htop hlow⟩

end

end HC4.Newton
