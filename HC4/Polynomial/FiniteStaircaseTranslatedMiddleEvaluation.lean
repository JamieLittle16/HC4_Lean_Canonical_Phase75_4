import HC4.Polynomial.FiniteStaircaseMiddleDoubleRootVariation
import HC4.Polynomial.FiniteStaircaseTranslatedPureModeEvaluation
import Mathlib.Tactic

/-!
# Evaluation of the translated middle two-mode staircase profile

If the middle profile translates to

    u X^(k-1) + v X^k,

linearity of the affine moment Hessian and the pure-mode evaluation theorem
identify its value at `2 alpha` with the corresponding linear combination of
the two normalized middle moment cores.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The polynomial affine moment Hessian is additive in its coefficient
profile. -/
theorem rankThreeAffinePolynomialMomentHessian_add
    (A B C u1 : ℕ) (q r s0 : K) (phi psi : Polynomial K) :
    rankThreeAffinePolynomialMomentHessian A B C u1 q r s0 (phi + psi) =
      rankThreeAffinePolynomialMomentHessian A B C u1 q r s0 phi +
        rankThreeAffinePolynomialMomentHessian A B C u1 q r s0 psi := by
  apply Matrix.ext
  intro i j
  simp [rankThreeAffinePolynomialMomentHessian_apply, eulerDerivative]
  ring

/-- Translation is inverted by translation through the opposite scalar. -/
theorem translatePolynomial_neg_left_inverse
    (alpha : K) (p : Polynomial K) :
    translatePolynomial (-alpha) (translatePolynomial alpha p) = p := by
  simp [translatePolynomial, Polynomial.comp_assoc]

/-- **Middle two-mode evaluation.** -/
theorem eval_two_mul_parallelStaircaseMoment_of_translate_eq_middleTwoMode
    (V k : ℕ) (alpha u0 v0 : K) (phi : Polynomial K)
    (hk : 3 ≤ k)
    (htrans :
      translatePolynomial alpha phi =
        Polynomial.monomial (k - 1) u0 + Polynomial.monomial k v0) :
    (fun i j => Polynomial.eval (2 * alpha)
      (parallelStaircaseMomentHessian V k (k - 1) phi i j)) =
      (alpha ^ (k - 1) * u0) •
          middleLowerDoubleRootMomentCore (V : K) (k : K) +
        (alpha ^ k * v0) •
          middleUpperDoubleRootMomentCore (V : K) (k : K) := by
  let phiLo : Polynomial K :=
    translatePolynomial (-alpha) (Polynomial.monomial (k - 1) u0)
  let phiHi : Polynomial K :=
    translatePolynomial (-alpha) (Polynomial.monomial k v0)
  have hphi : phi = phiLo + phiHi := by
    calc
      phi = translatePolynomial (-alpha) (translatePolynomial alpha phi) := by
        symm
        exact translatePolynomial_neg_left_inverse alpha phi
      _ = translatePolynomial (-alpha)
          (Polynomial.monomial (k - 1) u0 + Polynomial.monomial k v0) := by
        rw [htrans]
      _ = phiLo + phiHi := by
        simp [phiLo, phiHi, translatePolynomial]
  have hLoTrans :
      translatePolynomial alpha phiLo = Polynomial.monomial (k - 1) u0 := by
    dsimp [phiLo]
    simp [translatePolynomial, Polynomial.comp_assoc]
  have hHiTrans :
      translatePolynomial alpha phiHi = Polynomial.monomial k v0 := by
    dsimp [phiHi]
    simp [translatePolynomial, Polynomial.comp_assoc]
  have hLo := eval_two_mul_rankThreeAffineMoment_of_translate_eq_monomial
    (K := K) k k (V * (2 * k - 1)) 1 (k - 1)
      (-1 : K) (-1 : K) (-(V : K)) alpha u0 (by omega) phiLo hLoTrans
  have hHi := eval_two_mul_rankThreeAffineMoment_of_translate_eq_monomial
    (K := K) k k (V * (2 * k - 1)) 1 k
      (-1 : K) (-1 : K) (-(V : K)) alpha v0 (by omega) phiHi hHiTrans
  rw [hphi, rankThreeAffinePolynomialMomentHessian_add]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  have hLij := congrFun (congrFun hLo i) j
  have hHij := congrFun (congrFun hHi i) j
  rw [map_add, hLij, hHij]
  simp [middleLowerDoubleRootMomentCore, middleUpperDoubleRootMomentCore,
    parallelStaircaseMomentHessian, staircaseLogDirection]

end

end HC4.Polynomial
