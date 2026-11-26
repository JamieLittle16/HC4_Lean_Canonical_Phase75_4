import HC4.Polynomial.RankThreeOneVariableKernel
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AxGrothendieck
import Lean.Util.CollectAxioms

/-!
# External statement comparison

Independent restatement using the polynomial-map conventions in
Google DeepMind's Formal Conjectures (Apache-2.0), snapshot
a88aee564684360292318c61b9b8e27febef2ae0:

* FormalConjectures/Wikipedia/JacobianConjecture.lean
* FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean

This file does not import the open conjecture or any proof placeholder.
Its assumption is the explicitly quantified polynomial inverse property.
The reference Jacobian has input indices as rows, unlike the ordinary
output-row convention; the determinant is unaffected by transposition.
-/

namespace HC4.StatementAudit

open MvPolynomial
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- Independently stated polynomial map determinant, using the external
input-row convention. -/
def referenceJacobian {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun i j => pderiv i (F j)

/-- Dimension-specific polynomial inverse formulation, as in Formal
Conjectures, with both composition equations written out. -/
def ReferenceJC (K : Type*) [Field K] (n : ℕ) : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) K,
    IsUnit (referenceJacobian F).det →
    ∃ G : Fin n → MvPolynomial (Fin n) K,
      (∀ i, bind₁ G (F i) = X i) ∧
      (∀ i, bind₁ F (G i) = X i)

/-- The project's planar determinant is exactly the reference determinant. -/
theorem reference_planar_det (F : Fin 2 → MvPolynomial (Fin 2) K) :
    (referenceJacobian F).det = HC4.planarJacobianDetPolynomial F := by
  rw [Matrix.det_fin_two]
  change pderiv 0 (F 0) * pderiv 1 (F 1) -
      pderiv 0 (F 1) * pderiv 1 (F 0) =
    pderiv 0 (F 0) * pderiv 1 (F 1) -
      pderiv 1 (F 0) * pderiv 0 (F 1)
  ring

/-- The Hessian is the transpose of the reference Jacobian of the gradient. -/
theorem reference_gradient_jacobian (P : MvPolynomial (Fin 4) K) :
    referenceJacobian (fun i => pderiv i P) =
      (HC4.Polynomial.hessian P).transpose := by
  rfl

theorem reference_gradient_det (P : MvPolynomial (Fin 4) K) :
    (referenceJacobian (fun i => pderiv i P)).det =
      HC4.Polynomial.hessianDeterminant P := by
  rw [reference_gradient_jacobian, Matrix.det_transpose]
  rfl

/-- The external unit condition and the nonzero scalar determinant
condition are exactly equivalent over a field, as in the external
project's own sanity check. -/
theorem reference_unit_iff {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) K) :
    IsUnit (referenceJacobian F).det ↔
      ∃ c : K, c ≠ 0 ∧ (referenceJacobian F).det = C c := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  simp only [isUnit_iff_ne_zero]

/-- A two-sided polynomial inverse implies pointwise injectivity. This
does not assume surjectivity, any conjecture, or an analytic inverse. -/
theorem injective_of_reference_left_inverse {n : ℕ}
    (F G : Fin n → MvPolynomial (Fin n) K)
    (h : ∀ i, bind₁ F (G i) = X i) :
    Function.Injective (fun x : Fin n → K => fun i => eval x (F i)) := by
  have hl (x : Fin n → K) :
      (fun i => eval (fun j => eval x (F j)) (G i)) = x := by
    funext i
    change aeval (fun j => aeval x (F j)) (G i) = x i
    rw [← aeval_bind₁ x F (G i), h i, aeval_X]
  intro x y he
  calc
    x = (fun i => eval (fun j => eval x (F j)) (G i)) := (hl x).symm
    _ = (fun i => eval (fun j => eval y (F j)) (G i)) := by rw [he]
    _ = y := hl y

/-- The external planar polynomial inverse conjecture is sufficient
for our exact planar hypothesis. -/
theorem planar_of_reference (h : ReferenceJC K 2) :
    HC4.PlanarJC2Injectivity K := by
  intro F hdet
  obtain ⟨c,hc,he⟩ := hdet
  have hu : IsUnit (referenceJacobian F).det := by
    rw [reference_planar_det, he]
    exact (isUnit_iff_ne_zero.mpr hc).map (C : K →+* MvPolynomial (Fin 2) K)
  obtain ⟨G,_,hleft⟩ := h F hu
  exact injective_of_reference_left_inverse F G hleft

variable [CharZero K]

/-- Scalar multiplication of a four-variable potential multiplies
its formal Hessian determinant by the fourth power of that scalar. -/
theorem hessianDeterminant_C_mul (a : K) (P : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant (C a * P) =
      C (a ^ 4) * HC4.Polynomial.hessianDeterminant P := by
  have hm : HC4.Polynomial.hessian (C a * P) =
      (C a : MvPolynomial (Fin 4) K) • HC4.Polynomial.hessian P := by
    ext i j
    change pderiv j (pderiv i (C a * P)) = C a * pderiv j (pderiv i P)
    rw [pderiv_C_mul, pderiv_C_mul]
  unfold HC4.Polynomial.hessianDeterminant
  rw [hm, Matrix.det_smul]
  simp only [Fintype.card_fin, map_pow]

/-- Over an algebraically closed characteristic-zero field, the
determinant-one restriction can be removed by scaling the potential.
The explicit conclusion is the evaluated gradient on all K-points. -/
theorem hc4_nonzero_constant_injective [IsAlgClosed K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (c : K) (hc : c ≠ 0)
    (hdet : (referenceJacobian (fun i => pderiv i P)).det = C c) :
    Function.Injective (fun x : Fin 4 → K => fun i => eval x (pderiv i P)) := by
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (show 0 < (4 : ℕ) by decide)
  have hscaled : HC4.Polynomial.hessianDeterminant (C a * P) = 1 := by
    rw [hessianDeterminant_C_mul, ← reference_gradient_det P, hdet,
      ha, ← map_mul, inv_mul_cancel₀ hc, map_one]
  have hi := HC4.Polynomial.hc4_of_planarJC2 hJC2 (C a * P) hscaled
  intro x y hxy
  apply hi
  funext i
  change eval x (pderiv i (C a * P)) = eval y (pderiv i (C a * P))
  rw [pderiv_C_mul, map_mul, map_mul, eval_C, eval_C, congrFun hxy i]

/-- External-style JC2 implies bijectivity of the gradient of every
four-variable potential of nonzero constant Hessian determinant over
an algebraically closed characteristic-zero field. The surjectivity
step is mathlib's proved Ax-Grothendieck theorem. -/
theorem hc4_reference_JC2_bijective [IsAlgClosed K]
    (hJC2 : ReferenceJC K 2)
    (P : MvPolynomial (Fin 4) K) (c : K) (hc : c ≠ 0)
    (hdet : (referenceJacobian (fun i => pderiv i P)).det = C c) :
    Function.Bijective (fun x : Fin 4 → K => fun i => eval x (pderiv i P)) := by
  have hi := hc4_nonzero_constant_injective (planar_of_reference hJC2) P c hc hdet
  exact ⟨hi, ax_grothendieck_univ (fun i : Fin 4 => pderiv i P) hi⟩


/-- The exact external determinant-unit formulation of the conditional
Hessian bijectivity statement. No determinant normalization hypothesis. -/
theorem hc4_reference_JC2_unit_bijective [IsAlgClosed K]
    (hJC2 : ReferenceJC K 2)
    (P : MvPolynomial (Fin 4) K)
    (hdet : IsUnit (referenceJacobian (fun i => pderiv i P)).det) :
    Function.Bijective (fun x : Fin 4 → K => fun i => eval x (pderiv i P)) := by
  obtain ⟨c,hc,he⟩ := (reference_unit_iff (fun i : Fin 4 => pderiv i P)).mp hdet
  exact hc4_reference_JC2_bijective hJC2 P c hc he

end
end HC4.StatementAudit

#print axioms HC4.StatementAudit.reference_unit_iff
#print axioms HC4.StatementAudit.reference_planar_det
#print axioms HC4.StatementAudit.reference_gradient_det
#print axioms HC4.StatementAudit.planar_of_reference
#print axioms HC4.StatementAudit.hc4_nonzero_constant_injective
#print axioms HC4.StatementAudit.hc4_reference_JC2_bijective
#print axioms HC4.StatementAudit.hc4_reference_JC2_unit_bijective

run_cmd do
  let permitted : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``HC4.StatementAudit.reference_unit_iff,
      ``HC4.StatementAudit.reference_planar_det,
      ``HC4.StatementAudit.reference_gradient_det,
      ``HC4.StatementAudit.planar_of_reference,
      ``HC4.StatementAudit.hc4_nonzero_constant_injective,
      ``HC4.StatementAudit.hc4_reference_JC2_bijective,
      ``HC4.StatementAudit.hc4_reference_JC2_unit_bijective] do
    for dep in (← Lean.collectAxioms decl) do
      unless permitted.contains dep do
        throwError "Unexpected logical dependency {dep} in {decl}"
