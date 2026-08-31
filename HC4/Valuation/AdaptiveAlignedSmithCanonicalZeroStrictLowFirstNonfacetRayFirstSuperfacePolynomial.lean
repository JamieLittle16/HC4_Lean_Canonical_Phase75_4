import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFirstSuperface
import HC4.Newton.FiniteSupportExposedFaceRefinement
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A19.122: the first strict ray superface as an exact source polynomial

A19.117 deliberately stopped at the support-level statement.  For the Schur
adapter we need an honest polynomial carrier, not merely a set of exponents.

The two exposing functionals in A19.117 are linear exponent weights, so their
integer combination is again induced by one coordinate weight.  We take the
corresponding exact initial form of the represented source and prove that its
support is literally the stored first strict superface.  Consequently:

* every monomial of the locked degree-one ray is retained;
* at least one genuinely new source monomial is retained;
* every retained coefficient is exactly the original represented-source
  coefficient; and
* the honest first-superface polynomial still has zero Hessian determinant.

No planarity, Hessian-rank strengthening, or weighted-homogeneity shortcut is
added.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- Coordinate weight inducing the support functional of A19.117's first
strict superface. -/
def QsOtherFacetRayFirstSuperfacePackage.combinedWeight
    (S : QsOtherFacetRayFirstSuperfacePackage C R) (i : Fin 4) : ℤ :=
  S.A * (R.weight i : ℤ) - S.B * S.secondaryWeight i

/-- Exact level of the combined first-superface exposure. -/
def QsOtherFacetRayFirstSuperfacePackage.combinedLevel
    (S : QsOtherFacetRayFirstSuperfacePackage C R) : ℤ :=
  S.A * (R.level : ℤ) - S.B * S.secondaryLevel

/-- The combined coordinate weight has exactly the exponent functional stored
by A19.117. -/
theorem QsOtherFacetRayFirstSuperfacePackage.weight_combinedWeight
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (e : Fin 4 →₀ ℕ) :
    Finsupp.weight S.combinedWeight e =
      S.A * Finsupp.weight (fun i : Fin 4 => (R.weight i : ℤ)) e -
        S.B * Finsupp.weight S.secondaryWeight e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype, Finsupp.sum_fintype]
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [QsOtherFacetRayFirstSuperfacePackage.combinedWeight]
  ring
  all_goals
    intro i
    simp

/-- A19.117's support exposure rewritten as an ordinary exact coordinate
weight exposure. -/
theorem QsOtherFacetRayFirstSuperfacePackage.superface_exposed_coordinate
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Newton.IsExposedFace
      (↑(polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
      S.superface
      (fun e => Finsupp.weight S.combinedWeight e) S.combinedLevel := by
  simpa [QsOtherFacetRayFirstSuperfacePackage.combinedLevel,
    S.weight_combinedWeight] using S.superface_exposed

/-- The represented source is globally bounded by the first-superface weight. -/
theorem QsOtherFacetRayFirstSuperfacePackage.combinedWeight_bound
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Polynomial.IsWeightLE S.combinedWeight S.combinedLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro e he
  exact S.superface_exposed_coordinate.weight_le (by simpa using he)

/-- Honest polynomial carried by the first strict superface. -/
noncomputable def QsOtherFacetRayFirstSuperfacePackage.polynomial
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm S.combinedWeight S.combinedLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)

/-- The honest initial form has exactly the support selected in A19.117. -/
theorem QsOtherFacetRayFirstSuperfacePackage.polynomial_support
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    (↑S.polynomial.support : Set (Fin 4 →₀ ℕ)) = S.superface := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  have hinit := HC4.Newton.initialForm_support_isExposedFace
    S.combinedWeight S.combinedLevel F S.combinedWeight_bound
  ext e
  change e ∈ (↑(HC4.Polynomial.initialForm
    S.combinedWeight S.combinedLevel F).support : Set (Fin 4 →₀ ℕ)) ↔
      e ∈ S.superface
  rw [hinit.mem_iff, S.superface_exposed_coordinate.mem_iff]

/-- Every locked-ray source monomial remains in the honest first-superface
polynomial. -/
theorem QsOtherFacetRayFirstSuperfacePackage.ray_support_subset
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    C.ray.face.support ⊆ S.polynomial.support := by
  intro e he
  have heSet : e ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) := by simpa using he
  have hsuper : e ∈ S.superface := S.ray_subset_superface heSet
  rw [← S.polynomial_support] at hsuper
  simpa using hsuper

/-- The honest first-superface polynomial is strictly larger than the locked
ray support. -/
theorem QsOtherFacetRayFirstSuperfacePackage.exists_support_not_ray
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    ∃ e ∈ S.polynomial.support, e ∉ C.ray.face.support := by
  rcases S.strict with ⟨e, heSuper, heRay⟩
  refine ⟨e, ?_, ?_⟩
  · have hePolySet : e ∈ (↑S.polynomial.support : Set (Fin 4 →₀ ℕ)) := by
      rw [S.polynomial_support]
      exact heSuper
    simpa using hePolySet
  · simpa using heRay

/-- Every coefficient retained by the first-superface polynomial is literally
its represented-source coefficient. -/
theorem QsOtherFacetRayFirstSuperfacePackage.coeff_polynomial_eq_source_of_mem
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    {e : Fin 4 →₀ ℕ} (he : e ∈ S.polynomial.support) :
    MvPolynomial.coeff e S.polynomial =
      MvPolynomial.coeff e
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  exact HC4.Newton.initialForm_coeff_eq_source_of_mem
    S.combinedWeight S.combinedLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) he

/-- Hessian singularity survives the exact first-superface exposure. -/
set_option maxHeartbeats 400000 in
theorem QsOtherFacetRayFirstSuperfacePackage.hessianDeterminant_polynomial_eq_zero
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Polynomial.hessianDeterminant S.polynomial = 0 := by
  change HC4.Polynomial.hessianDeterminant
    (HC4.Polynomial.initialForm S.combinedWeight S.combinedLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) = 0
  apply HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
  · exact S.combinedWeight_bound
  · exact C.hessian_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
