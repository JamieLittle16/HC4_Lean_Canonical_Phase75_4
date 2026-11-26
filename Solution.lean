module

public import HC4.FinalEquivalence

/-! The two advertised statements are proved by the existing HC4 development.
This module does not import Challenge. -/

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
  exact HC4.StatementAudit.jc2_iff_hc4_explicit (K := K)

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
  change HC4.PlanarJC2Injectivity K ↔
    (∀ P : MvPolynomial (Fin 4) K,
      HC4.Polynomial.hessianDeterminant P = 1 →
      Function.Injective (HC4.Newton.mvGradientMap P))
  exact HC4.StatementAudit.planarJC2_iff_hessianFour_injective (K := K)

end HC4.Palomar
