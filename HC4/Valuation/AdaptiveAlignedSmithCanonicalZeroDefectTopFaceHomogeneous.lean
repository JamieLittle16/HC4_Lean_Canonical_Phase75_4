import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceSelection
import Mathlib.Tactic

/-!
# A18.5.78/80: the zero-defect singular carrier is an honest homogeneous face

A18.5.12 selects the genuine maximal ordinary initial form of a determinant-one
collision state and proves that it is nonzero, nonlinear and Hessian-singular.
The construction already forces every surviving exponent to have exactly the
selected ordinary degree, but that fact was not exposed as a reusable theorem.

This file packages the missing homogeneous-carrier interface.  It introduces
no new geometric assumption: the equal-degree statement follows directly from
the coefficient formula for the ordinary initial form.  It also records the
support-functorial fact needed by the final toric consumer: whenever the
source special fibre already carries a certified symmetric torus grading, the
selected top face retains that grading because it is an exact initial form.
No grading is manufactured here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData

/-- Every supported exponent of the selected zero-defect face has exactly the
selected maximal ordinary degree. -/
theorem face_support_ordinaryDegree_eq
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ D.face.support) :
    HC4.Polynomial.ordinaryDegree4 d = D.degree := by
  have hcoeff : MvPolynomial.coeff d D.face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [D.face_eq, HC4.Polynomial.coeff_initialForm] at hcoeff
  split at hcoeff
  · rename_i hweight
    have hweight' :
        Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d = (D.degree : ℤ) := by
      change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d = (D.degree : ℤ) at hweight
      exact hweight
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4] at hweight'
    exact_mod_cast hweight'
  · exact (hcoeff rfl).elim

/-- The selected singular top face is genuinely ordinary homogeneous, at its
actual attained degree. -/
theorem face_isHomogeneous
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s) :
    D.face.IsHomogeneous D.degree := by
  intro d hd
  have hmem : d ∈ D.face.support :=
    MvPolynomial.mem_support_iff.mpr hd
  have hdegree := D.face_support_ordinaryDegree_eq hmem
  have hw : Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  exact hw.trans
    ((HC4.Valuation.finsuppDegree_eq_ordinaryDegree4 d).trans hdegree)

/-- Every monomial of the selected face is nonlinear.  This is the support
form most convenient for the exposed-boundary and first-contact constructors. -/
theorem face_support_degree_ge_three
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s) :
    ∀ d ∈ D.face.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
  intro d hd
  rw [D.face_support_ordinaryDegree_eq hd]
  exact D.degree_ge_three

/-- Exact initial-form extraction does not lose a toric balance certificate.
This theorem is deliberately conditional: the final HC4 entry must supply the
balance from genuine preceding geometry rather than obtaining it from ordinary
homogeneity. -/
theorem face_balanced_of_specialFiber_balanced
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s)
    {a b : ℕ}
    (hBal : HC4.Polynomial.HasBalancedMvSupport a b
      (polynomialFamilySpecialFiber s.family)) :
    HC4.Polynomial.HasBalancedMvSupport a b D.face := by
  rw [D.face_eq]
  exact hBal.initialForm _ _

end AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData

end

end HC4.Valuation
