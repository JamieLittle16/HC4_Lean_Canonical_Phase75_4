import HC4.Newton.FirstNonfacetContact
import Mathlib.Tactic

/-!
# A18.5.32: first-contact support is genuinely nonlinear

The first-contact construction already proves that every low-degree HC4
monomial lies strictly below the selected contact level.  This file records
the exact support consequence needed by the terminal convex step: no monomial
of ordinary degree at most two survives in the contact initial form.

Thus every supported monomial of the genuine first-contact polynomial has
ordinary degree at least three.  In particular any subsequently exposed
singleton automatically satisfies the nonlinear hypothesis of
`InteriorVertex` / `ExposedBalancedBoundaryStratum`.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

/-- **Every monomial on a genuine HC4 contact face is nonlinear.** -/
theorem firstContact_initialForm_support_degree_ge_three
    {K : Type*} [CommRing K]
    {j : Fin 4} {scale bump m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hscale : 0 < scale)
    (hbump : bump ≤ scale * (m - 3))
    (hlow : ∀ d ∈ psi.support, ordinaryDegree4 d < 3 → d j ≤ 1) :
    ∀ d ∈
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi).support,
      3 ≤ ordinaryDegree4 d := by
  intro d hd
  have hdPsi : d ∈ psi.support :=
    support_initialForm_subset
      (scaledContactWeight j scale bump) (scale * m : ℕ) psi hd
  have hcoeff :
      MvPolynomial.coeff d
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hweight :
      Finsupp.weight (scaledContactWeight j scale bump) d =
        ((scale * m : ℕ) : ℤ) := by
    exact
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump) (scale * m : ℕ) psi) hcoeff
  by_contra hnot
  have hdeg2 : ordinaryDegree4 d ≤ 2 := by omega
  have hj : d j ≤ 1 := hlow d hdPsi (by omega)
  have hstrict :=
    lowDegree_below_scaled_contact
      hscale hdeg2 hj hbump hm
  rw [← weight_scaledContactWeight] at hstrict
  omega

end

end HC4.Newton
