module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Four-variable Hessian and planar Jacobian conjectures

The first theorem states their equivalence over any algebraically closed
field of characteristic zero, using two-sided polynomial inverses.
The second states their equivalence in injectivity form over any
characteristic-zero field, with determinant-one normalization on the
Hessian side. No degree bound is imposed. Neither conjecture is
asserted unconditionally.

All mathematical objects in the statements are from Mathlib.
The source of the known complex equivalence is Qiyue Tang,
*Equivalence of the Four-Variable Hessian and Planar Jacobian Conjectures*,
Hexagon 2611.00156v2 (2026), Theorem 1.1.
-/

public section

namespace HC4.Palomar

open MvPolynomial

/-- Over an algebraically closed characteristic-zero field, planar
polynomial maps with unit Jacobian determinant all have polynomial inverses
if and only if four-variable polynomial gradients with unit Hessian
determinant all have polynomial inverses. -/
theorem jc2_iff_hc4
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    (∀ F : Fin 2 → MvPolynomial (Fin 2) K,
      IsUnit (Matrix.of (fun i j : Fin 2 => pderiv i (F j))).det →
      ∃ G : Fin 2 → MvPolynomial (Fin 2) K,
        (∀ i, bind₁ G (F i) = X i) ∧
        (∀ i, bind₁ F (G i) = X i)) ↔
    (∀ P : MvPolynomial (Fin 4) K,
      IsUnit (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det →
      ∃ G : Fin 4 → MvPolynomial (Fin 4) K,
        (∀ i, bind₁ G (pderiv i P) = X i) ∧
        (∀ i, bind₁ (fun j => pderiv j P) (G i) = X i)) := by
  sorry

/-- Over any characteristic-zero field, injectivity of all planar Keller
maps is equivalent to injectivity of all determinant-one four-variable
polynomial gradients. This statement does not require algebraic closure. -/
theorem jc2_iff_hc4_injective
    {K : Type*} [Field K] [CharZero K] :
    (∀ F : Fin 2 → MvPolynomial (Fin 2) K,
      (∃ c : K, c ≠ 0 ∧
        pderiv 0 (F 0) * pderiv 1 (F 1) -
        pderiv 1 (F 0) * pderiv 0 (F 1) = C c) →
      Function.Injective (fun x : Fin 2 → K => fun i => eval x (F i))) ↔
    (∀ P : MvPolynomial (Fin 4) K,
      (Matrix.of (fun i j : Fin 4 => pderiv j (pderiv i P))).det = 1 →
      Function.Injective (fun x : Fin 4 → K => fun i => eval x (pderiv i P))) := by
  sorry

end HC4.Palomar
