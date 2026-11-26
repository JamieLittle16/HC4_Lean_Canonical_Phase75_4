module

public import HC4.RationalInverseAudit
meta import Lean.Util.CollectAxioms

/-!
# Final polynomial-inverse equivalence

Over any algebraically closed characteristic-zero field, the planar
Jacobian conjecture and the four-variable Hessian conjecture are equivalent
in the two-sided polynomial inverse formulation.

The planar predicate is the dimension-two specialization of the
polynomial-map conventions in Google DeepMind's Formal Conjectures,
expanded in StatementAudit. The Hessian predicate applies the same
unit-Jacobian and inverse conventions to formal gradients.

The equivalence uses the verified core implication, planar doubling,
and the separately proved generic polynomial inverse theorem.
Neither conjecture is assumed as a global axiom.
-/

@[expose] public section

namespace HC4.StatementAudit

open MvPolynomial

noncomputable section

/-- Four-variable Hessian conjecture in the polynomial inverse formulation,
with the formal Hessian determinant written directly using partial derivatives. -/
def ReferenceHC4 (K : Type*) [Field K] : Prop :=
  ∀ P : MvPolynomial (Fin 4) K,
    IsUnit (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det →
    ∃ G : Fin 4 → MvPolynomial (Fin 4) K,
      (∀ i, bind₁ G (pderiv i P) = X i) ∧
      (∀ i, bind₁ (fun j => pderiv j P) (G i) = X i)

/-- The explicit Hessian determinant agrees with the reference gradient
Jacobian determinant, despite the transpose convention. -/
theorem explicit_hessian_det_eq_reference {K : Type*} [Field K]
    (P : MvPolynomial (Fin 4) K) :
    (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det =
      (referenceJacobian (fun i => pderiv i P)).det := by
  exact (reference_gradient_det P).symm

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The planar injectivity interface is equivalent to the external
two-sided polynomial inverse conjecture. -/
theorem referenceJC2_iff_planarJC2 :
    ReferenceJC K 2 ↔ HC4.PlanarJC2Injectivity K := by
  constructor
  · exact planar_of_reference
  · intro h F hu
    obtain ⟨c, hc, he⟩ := (reference_unit_iff F).mp hu
    rw [reference_planar_det] at he
    exact HC4.PolynomialInverseAudit.polynomial_inverse_of_injective_eval F
      (h F ⟨c, hc, he⟩)

/-- The explicit determinant-unit Hessian polynomial-inverse conjecture
is equivalent to the original determinant-one injectivity interface. -/
theorem referenceHC4_iff_hessianFour_injective :
    ReferenceHC4 K ↔
      (∀ P : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant P = 1 →
          Function.Injective (HC4.Newton.mvGradientMap P)) := by
  constructor
  · intro h P hd
    have hu : IsUnit (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det := by
      change IsUnit (HC4.Polynomial.hessianDeterminant P)
      rw [hd]
      exact isUnit_one
    obtain ⟨G, _, hG⟩ := h P hu
    exact injective_of_reference_left_inverse (fun i => pderiv i P) G hG
  · intro h P hu
    have hJC := HC4.planarJC2_of_hessianFour_gradient_injective h
    have hu' : IsUnit (referenceJacobian (fun i => pderiv i P)).det := by
      rw [← explicit_hessian_det_eq_reference P]
      exact hu
    have hi := ((planarJC2_iff_hessianFour_unit_bijective (K := K)).mp hJC P hu').1
    exact HC4.PolynomialInverseAudit.polynomial_inverse_of_injective_eval
      (fun i => pderiv i P) hi

/-- The full conditional equivalence in the two-sided polynomial inverse
formulation, without determinant normalization. -/
theorem referenceJC2_iff_referenceHC4 :
    ReferenceJC K 2 ↔ ReferenceHC4 K :=
  referenceJC2_iff_planarJC2.trans
    (planarJC2_iff_hessianFour_injective.trans
      referenceHC4_iff_hessianFour_injective.symm)

/-- Fully expanded public theorem: neither conjecture is hidden behind
a project-specific predicate. -/
theorem jc2_iff_hc4_explicit :
    (∀ F : Fin 2 → MvPolynomial (Fin 2) K,
      IsUnit (Matrix.of (fun i j : Fin 2 => pderiv i (F j))).det →
      ∃ G : Fin 2 → MvPolynomial (Fin 2) K,
        (∀ i, bind₁ G (F i) = X i) ∧
        (∀ i, bind₁ F (G i) = X i)) ↔
    (∀ P : MvPolynomial (Fin 4) K,
      IsUnit (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det →
      ∃ G : Fin 4 → MvPolynomial (Fin 4) K,
        (∀ i, bind₁ G (pderiv i P) = X i) ∧
        (∀ i, bind₁ (fun j => pderiv j P) (G i) = X i)) :=
  referenceJC2_iff_referenceHC4

end
end HC4.StatementAudit

#print axioms HC4.StatementAudit.explicit_hessian_det_eq_reference
#print axioms HC4.StatementAudit.referenceJC2_iff_planarJC2
#print axioms HC4.StatementAudit.referenceHC4_iff_hessianFour_injective
#print axioms HC4.StatementAudit.referenceJC2_iff_referenceHC4
#print axioms HC4.StatementAudit.jc2_iff_hc4_explicit

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``HC4.StatementAudit.explicit_hessian_det_eq_reference,
      ``HC4.StatementAudit.referenceJC2_iff_planarJC2,
      ``HC4.StatementAudit.referenceHC4_iff_hessianFour_injective,
      ``HC4.StatementAudit.referenceJC2_iff_referenceHC4,
      ``HC4.StatementAudit.jc2_iff_hc4_explicit] do
    for dep in (← Lean.collectAxioms decl) do
      unless allowed.contains dep do
        throwError "Unexpected logical dependency {dep} in {decl}"
