import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticQuadraticCore
import HC4.Valuation.AdaptiveAlignedSmithHomogeneousCoefficientRigidity
import Mathlib.Tactic

/-!
# G24: antipodal parity equation for the quartic final seam

The quartic homogeneous core is

    F = q2 + h3 + h4

with degrees 2, 3 and 4 and an exact gradient collision at the antipodal
points +/- (1/2)e0.

On the marked axis, a homogeneous polynomial of degree D restricts either to
zero or to one monomial of degree D.  Hence the gradient of a degree-D
homogeneous form changes by the sign (-1)^(D-1) between antipodal axis
points.

Therefore:

* grad q2 is odd;
* grad h3 is even;
* grad h4 is odd.

The even cubic contribution cancels from the exact collision, leaving the
quartic-specific relation

    grad q2(v) + grad h4(v) = 0,

at v = (1/2)e0.

Together with G23, this pins the quartic odd part against an invertible
quadratic Hessian.  No JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero marked-axis restriction of an ordinary homogeneous
four-variable polynomial is exactly a monomial of the homogeneous degree. -/
theorem homogeneous_axisRestriction_eq_monomial_degree
    (P : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hhom : P.IsHomogeneous D)
    (hne : longitudinalAxisRestriction P ≠ 0) :
    ∃ a : K, a ≠ 0 ∧
      longitudinalAxisRestriction P = Polynomial.monomial D a := by
  have hcoefNe :
      longitudinalCoefficientPolynomial 0 0 0 P ≠ 0 := by
    simpa [longitudinalCoefficientPolynomial_zero_eq_axisRestriction] using hne
  rcases
      homogeneous_longitudinalCoefficient_eq_monomial
        P D 0 0 0 hhom hcoefNe with
    ⟨n, a, ha, hmono⟩
  have hncoeff :
      (longitudinalCoefficientPolynomial 0 0 0 P).coeff n ≠ 0 := by
    rw [hmono]
    simp [ha]
  have hnP :
      MvPolynomial.coeff
          ((smithTransverseExponent 0 0 0).cons n) P ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hncoeff
  have hweight :
      Finsupp.weight (1 : Fin 4 → ℕ)
          ((smithTransverseExponent 0 0 0).cons n) = D :=
    hhom hnP
  have hsum :
      n + 0 + 0 + 0 = D :=
    (weight_one_cons_smithTransverseExponent 0 0 0 n).symm.trans hweight
  have hnD : n = D := by
    omega
  subst n
  refine ⟨a, ha, ?_⟩
  rw [← longitudinalCoefficientPolynomial_zero_eq_axisRestriction]
  exact hmono

/-- Evaluation of a homogeneous polynomial on opposite points of the marked
axis differs by the expected parity sign. -/
theorem homogeneous_axis_eval_neg_eq_negOnePow_eval
    (P : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hhom : P.IsHomogeneous D)
    (x : K) :
    MvPolynomial.eval
        (Fin.cons (-x) (fun _ : Fin 3 => (0 : K))) P =
      (-1 : K) ^ D *
        MvPolynomial.eval
          (Fin.cons x (fun _ : Fin 3 => (0 : K))) P := by
  rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
    eval_finCons_zero_eq_longitudinalAxisRestriction]
  by_cases haxis : longitudinalAxisRestriction P = 0
  · simp [haxis]
  · rcases
      homogeneous_axisRestriction_eq_monomial_degree
        (K := K) P D hhom haxis with
      ⟨a, ha, hmono⟩
    rw [hmono]
    simp [Polynomial.eval_monomial, neg_pow]
    ring

/-- Gradient parity of an ordinary homogeneous form along the marked axis. -/
theorem homogeneous_gradient_axis_eval_neg_eq_negOnePow_eval
    (H : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hhom : H.IsHomogeneous D)
    (i : Fin 4)
    (x : K) :
    MvPolynomial.eval
        (Fin.cons (-x) (fun _ : Fin 3 => (0 : K)))
        (MvPolynomial.pderiv i H) =
      (-1 : K) ^ (D - 1) *
        MvPolynomial.eval
          (Fin.cons x (fun _ : Fin 3 => (0 : K)))
          (MvPolynomial.pderiv i H) := by
  have hfirst :
      (MvPolynomial.pderiv i H).IsHomogeneous (D - 1) := by
    exact hhom.pderiv
  exact homogeneous_axis_eval_neg_eq_negOnePow_eval
    (K := K) (MvPolynomial.pderiv i H) (D - 1) hfirst x

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- At the positive midpoint point, the odd homogeneous gradient pieces q2
and h4 cancel componentwise. -/
theorem FinalSeamQuarticCoreCollisionData.q2_add_h4_gradient_eval_right_eq_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticCoreCollisionData)
    (i : Fin 4) :
    MvPolynomial.eval (finalSeamMidpointRight (K := K))
        (MvPolynomial.pderiv i C.homogeneousCore.q2) +
      MvPolynomial.eval (finalSeamMidpointRight (K := K))
        (MvPolynomial.pderiv i C.homogeneousCore.h4) = 0 := by
  let Q := C.homogeneousCore
  let x : K := finalSeamHalf (K := K)

  have hq2raw :=
    homogeneous_gradient_axis_eval_neg_eq_negOnePow_eval
      (K := K) Q.q2 2 Q.q2_homogeneous i x
  have hq2 :
      MvPolynomial.eval (finalSeamMidpointLeft (K := K))
          (MvPolynomial.pderiv i Q.q2) =
        - MvPolynomial.eval (finalSeamMidpointRight (K := K))
          (MvPolynomial.pderiv i Q.q2) := by
    simpa [finalSeamMidpointLeft, finalSeamMidpointRight, x] using hq2raw

  have hh3raw :=
    homogeneous_gradient_axis_eval_neg_eq_negOnePow_eval
      (K := K) Q.h3 3 Q.h3_homogeneous i x
  have hh3 :
      MvPolynomial.eval (finalSeamMidpointLeft (K := K))
          (MvPolynomial.pderiv i Q.h3) =
        MvPolynomial.eval (finalSeamMidpointRight (K := K))
          (MvPolynomial.pderiv i Q.h3) := by
    simpa [finalSeamMidpointLeft, finalSeamMidpointRight, x] using hh3raw

  have hh4raw :=
    homogeneous_gradient_axis_eval_neg_eq_negOnePow_eval
      (K := K) Q.h4 4 Q.h4_homogeneous i x
  have hh4 :
      MvPolynomial.eval (finalSeamMidpointLeft (K := K))
          (MvPolynomial.pderiv i Q.h4) =
        - MvPolynomial.eval (finalSeamMidpointRight (K := K))
          (MvPolynomial.pderiv i Q.h4) := by
    simpa [finalSeamMidpointLeft, finalSeamMidpointRight, x] using hh4raw

  have hcoll := C.exactCollision i
  unfold mvGradientComponentAt at hcoll
  rw [Q.core_eq] at hcoll
  simp only [map_add] at hcoll
  rw [hq2, hh3, hh4] at hcoll

  have htwo :
      (2 : K) *
        (MvPolynomial.eval (finalSeamMidpointRight (K := K))
            (MvPolynomial.pderiv i Q.q2) +
          MvPolynomial.eval (finalSeamMidpointRight (K := K))
            (MvPolynomial.pderiv i Q.h4)) = 0 := by
    linear_combination -hcoll
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
