import HC4.Newton.FirstNonfacetContact
import Mathlib.Tactic

/-!
# A19.65: failure of low-degree tameness is exactly a quadratic square

The only source hypothesis not already exported by A19.59/A19.60 for the
generic first-nonfacet selector is `LowDegreeTameAtFacet`.  Its negation is
completely rigid in four variables.  A supported exponent of ordinary degree
strictly below three whose omitted coordinate is greater than one must have
ordinary degree exactly two and omitted-coordinate exponent exactly two.

Thus the first-nonfacet splice has an exhaustive finite alternative:

* the low-degree part is tame, so the generic contact selector applies; or
* the source contains a literal quadratic square in the omitted coordinate.

This is only finite-support arithmetic; it makes no geometric conclusion from
the square by itself.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

variable {K : Type*} [CommSemiring K]

/-- A low-degree-tameness failure is a genuine supported quadratic square in
the omitted coordinate. -/
theorem lowDegreeTame_or_exists_omittedQuadraticSquare
    (F : ToricFacet) (p : MvPolynomial (Fin 4) K) :
    LowDegreeTameAtFacet F p ∨
      ∃ d ∈ p.support,
        ordinaryDegree4 d = 2 ∧
        d (facetOmittedCoordinate F) = 2 ∧
        ∀ i : Fin 4, i ≠ facetOmittedCoordinate F → d i = 0 := by
  classical
  by_cases htame : LowDegreeTameAtFacet F p
  · exact Or.inl htame
  · right
    unfold LowDegreeTameAtFacet at htame
    push_neg at htame
    rcases htame with ⟨d, hd, hdeg, hj⟩
    have hj2 : 2 ≤ d (facetOmittedCoordinate F) := by omega
    have hsum : ordinaryDegree4 d = d 0 + d 1 + d 2 + d 3 := rfl
    have hdeg2 : ordinaryDegree4 d = 2 := by
      cases F <;> simp [facetOmittedCoordinate, ordinaryDegree4] at hj2 ⊢ <;> omega
    have hjEq : d (facetOmittedCoordinate F) = 2 := by
      cases F <;> simp [facetOmittedCoordinate, ordinaryDegree4] at hdeg2 hj2 ⊢ <;> omega
    refine ⟨d, hd, hdeg2, hjEq, ?_⟩
    intro i hi
    cases F <;> fin_cases i <;>
      simp [facetOmittedCoordinate, ordinaryDegree4] at hi hdeg2 hjEq ⊢ <;> omega

end

end HC4.Newton
