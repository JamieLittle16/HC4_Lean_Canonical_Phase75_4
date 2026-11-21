import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry
import HC4.Valuation.MovingCollisionRecentering
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.84: recenter an arbitrary determinant-one gradient collision

The final HC4 entry must not assume that one colliding point is already the
origin.  This file removes that affine-normalisation assumption without making
any linear-coordinate choice.

Given an ordinary polynomial `F` with `det Hess(F) = 1` and an exact distinct
gradient collision at `p,q`, embed `F` as a constant parameter family and
translate the source by the constant section `p`.  The existing translation
calculus proves, exactly:

* the pure Hessian clock remains `tau^0 = 1`;
* the collision becomes `0 ~ (q-p)`;
* the displacement `q-p` is nonzero; and
* every nonlinear source-degree ceiling is preserved.

Thus the only remaining coordinate normalisation before the canonical A18
entry is the purely linear problem of sending a nonzero displacement vector to
`e_0` by determinant-one source changes.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Coordinatewise displacement of two source points. -/
def collisionDisplacement
    (p q : Fin 4 → K) : Fin 4 → K :=
  fun i => q i - p i

/-- Constant-family translation which recentres the left colliding point. -/
noncomputable def recenteredZeroDefectFamily
    (F : MvPolynomial (Fin 4) K)
    (p : Fin 4 → K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  polynomialFamilyTranslationHom (K := K)
    (polynomialConstantSection p)
    (zeroDefectConstantParameterFamily F)

/-- Ordinary special fibre of the recentered constant family. -/
noncomputable def recenteredZeroDefectPolynomial
    (F : MvPolynomial (Fin 4) K)
    (p : Fin 4 → K) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber (recenteredZeroDefectFamily F p)

/-- The exact data obtained after translating an arbitrary distinct
zero-defect collision to the origin. -/
structure AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry where
  degreeCap : ℕ
  polynomial : MvPolynomial (Fin 4) K
  endpoint : Fin 4 → K
  endpoint_ne_zero : endpoint ≠ fun _ => 0
  nonlinearDegreeBound : NonlinearDegreeBound degreeCap polynomial
  hessian_one : HC4.Polynomial.hessianDeterminant polynomial = 1
  exactCollision :
    HasExactGradientCollision polynomial (fun _ => 0) endpoint

namespace AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry

/-- **Arbitrary distinct determinant-one collision -> pointed collision.**

This is the affine half of the final HC4 collision normalisation.  No toric,
Smith, rank or JC2 hypothesis occurs. -/
noncomputable def ofExactCollision
    (degreeCap : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (p q : Fin 4 → K)
    (hdegree : NonlinearDegreeBound degreeCap F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry (K := K) := by
  let P0 := zeroDefectConstantParameterFamily F
  let a := polynomialConstantSection p
  let b := polynomialConstantSection q
  let Q := polynomialFamilyTranslationHom (K := K) a P0
  let G := polynomialFamilySpecialFiber Q
  let v := collisionDisplacement p q

  have hdef0 : HasPolynomialFamilyHessianDefect (K := K) P0 0 := by
    simpa [P0] using zeroDefectConstantParameterFamily_hessianDefect F hdet
  have hdefQ : HasPolynomialFamilyHessianDefect (K := K) Q 0 := by
    simpa [Q, a] using
      polynomialFamilyTranslationHom_preservesHessianDefect
        (K := K) a P0 hdef0
  have hGdet : HC4.Polynomial.hessianDeterminant G = 1 := by
    rw [show G = polynomialFamilySpecialFiber Q by rfl]
    rw [hessianDeterminant_polynomialFamilySpecialFiber]
    unfold HasPolynomialFamilyHessianDefect at hdefQ
    rw [hdefQ]
    simp

  have hP0degree : NonlinearDegreeBound degreeCap P0 := by
    simpa [P0] using
      zeroDefectConstantParameterFamily_nonlinearDegreeBound
        F degreeCap hdegree
  have hQdegree : NonlinearDegreeBound degreeCap Q := by
    simpa [Q, a] using
      nonlinearDegreeBound_polynomialFamilyTranslationHom
        degreeCap a P0 hP0degree
  have hGdegree : NonlinearDegreeBound degreeCap G := by
    simpa [G] using
      nonlinearDegreeBound_polynomialFamilySpecialFiber
        degreeCap Q hQdegree

  have hfamilyCollision :
      HasPolynomialFamilyExactGradientCollision P0 a b := by
    simpa [P0, a, b] using
      zeroDefectConstantParameterFamily_exactCollision F p q hcoll
  have hrecentered :
      HasExactGradientCollision G
        (fun _ : Fin 4 => (0 : K))
        (polynomialSectionSpecialPoint
          (polynomialSectionDifference a b)) := by
    simpa [G, Q] using
      recenteredPolynomialFamily_specialFiber_exactCollision
        (K := K) P0 a b hfamilyCollision
  have hspecialDifference :
      polynomialSectionSpecialPoint
          (polynomialSectionDifference a b) = v := by
    funext i
    simp [a, b, v, collisionDisplacement,
      polynomialConstantSection, polynomialSectionSpecialPoint,
      polynomialSectionDifference]
  have hGcoll : HasExactGradientCollision G (fun _ => 0) v := by
    rw [← hspecialDifference]
    exact hrecentered

  have hv : v ≠ fun _ => 0 := by
    intro hv0
    apply hpq
    funext i
    have hi : q i - p i = 0 := by
      simpa [v, collisionDisplacement] using congrFun hv0 i
    exact (sub_eq_zero.mp hi).symm

  exact {
    degreeCap := degreeCap
    polynomial := G
    endpoint := v
    endpoint_ne_zero := hv
    nonlinearDegreeBound := hGdegree
    hessian_one := hGdet
    exactCollision := hGcoll
  }

end AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry

end

end HC4.Valuation
