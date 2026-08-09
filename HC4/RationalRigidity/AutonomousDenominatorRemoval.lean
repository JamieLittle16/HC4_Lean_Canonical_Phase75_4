import HC4.RationalRigidity.FinitePreimage
import Mathlib.Tactic

/-!
# Denominator removal for autonomous rational identities

This file packages the finite/infinity surjectivity argument needed in the
rank-three autonomous logarithmic ODE.

Let `N / D` be a reduced source rational function over an algebraically closed
field, with `D` nonzero of positive degree.  Phase 81 proves that every scalar
except `rationalInfinityValue N D` has a finite preimage under this fraction.

Let `A / B` be a second reduced fraction and suppose a cleared autonomous
identity

    A(rho) = eta * B(rho)

holds at every finite source point, with an analogous cleared identity at the
single infinity value.  If `B` vanished at any scalar, the finite/infinity
cover would force `A` to vanish there too, contradicting coprimality of `A`
and `B`.  Thus `B` has no roots, and algebraic closure forces `B` to be a
nonzero constant polynomial.

This is the denominator-removal part of the manuscript sentence: a finite pole
of the autonomous right-hand side would have a preimage at which the left-hand
side is regular.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

section Field

variable {K : Type*} [Field K]

/-- Coprime polynomials cannot both vanish at the same scalar.  This orientation
is convenient for denominator-removal arguments: if `B(y)=0`, then `A(y)` is
nonzero. -/
theorem eval_left_ne_zero_of_isCoprime_right_eval_zero
    {A B : K[X]} (hCoprime : IsCoprime A B)
    {y : K} (hB : B.eval y = 0) :
    A.eval y ≠ 0 := by
  intro hA
  change ∃ U V : K[X], U * A + V * B = 1 at hCoprime
  rcases hCoprime with ⟨U, V, hBezout⟩
  have hEval := congrArg (Polynomial.eval y) hBezout
  simp [hA, hB] at hEval

end Field

section AlgebraicallyClosedField

variable {K : Type*} [Field K] [IsAlgClosed K]

/--
A reduced target denominator is constant once its cleared autonomous identity
holds on every finite source point and at the source's single infinity value.

The source fraction `N / D` is assumed reduced, with nonzero positive-degree
`D`.  The finite chart is supplied by Phase 81.  No projective geometry is
used: the infinity chart is represented by the scalar
`rationalInfinityValue N D` together with one cleared identity there.
-/
theorem constant_target_denominator_of_reduced_source_cover
    {N D A B : K[X]}
    (hSourceCoprime : IsCoprime N D)
    (hD : D ≠ 0)
    (hDdegree : 0 < D.natDegree)
    (hTargetCoprime : IsCoprime A B)
    (eta : K → K) (etaInfinity : K)
    (hFiniteClear :
      ∀ x : K, D.eval x ≠ 0 →
        A.eval (N.eval x / D.eval x) =
          eta x * B.eval (N.eval x / D.eval x))
    (hInfinityClear :
      A.eval (rationalInfinityValue N D) =
        etaInfinity * B.eval (rationalInfinityValue N D)) :
    ∃ b : K, b ≠ 0 ∧ B = C b := by
  have hBglobal : ∀ y : K, B.eval y ≠ 0 := by
    intro y hBy
    by_cases hy : y = rationalInfinityValue N D
    · subst y
      have hAzero : A.eval (rationalInfinityValue N D) = 0 := by
        rw [hInfinityClear, hBy, mul_zero]
      exact
        (eval_left_ne_zero_of_isCoprime_right_eval_zero
          hTargetCoprime hBy) hAzero
    · obtain ⟨x, hDx, hrho⟩ :=
        exists_finite_preimage_away_from_rationalInfinityValue
          hSourceCoprime hD hDdegree hy
      have hClear := hFiniteClear x hDx
      have hAzero : A.eval y = 0 := by
        rw [hrho, hBy, mul_zero] at hClear
        exact hClear
      exact
        (eval_left_ne_zero_of_isCoprime_right_eval_zero
          hTargetCoprime hBy) hAzero
  exact constant_polynomial_of_eval_ne_zero B hBglobal


end AlgebraicallyClosedField

end

end HC4.RationalRigidity
