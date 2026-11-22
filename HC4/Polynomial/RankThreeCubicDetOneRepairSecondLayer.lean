import HC4.Polynomial.RankThreeCubicDetOneRepairBlockDegree
import Mathlib.Tactic

/-!
# Exact quadratic layer of the source Hessian correction

For a source of transverse weight at most three, first remove
its true cubic layer L3 and then the true weight-two component L2
of the remaining polynomial. The final remainder has transverse
weight strictly below two.

Consequently its transverse-transverse Hessian is identically
zero, so the ENTIRE transverse-transverse Hessian correction
comes from the exact quadratic source layer, not from an
independent matrix or an assumed normal form.

This small algebraic layer extraction prepares the weight-five
Hessian determinant calculation, but does not assert that that
determinant coefficient has already been computed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
noncomputable section

variable {K : Type*} [Field K]
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The remainder after removing the weight-three initial form
has transverse weight at most two, by integrality of the weight. -/
theorem sourceCubic_belowThree_weightLE_two
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F) :
    IsWeightLE transverseCubicWeight 2
      (F - initialForm transverseCubicWeight 3 F) := by
  intro d hd
  have hlt := (sub_initialForm_isWeightLT hcap) hd
  omega

/-- Removing the ACTUAL weight-two layer from the cubic remainder
leaves strictly lower transverse weight. -/
theorem sourceCubic_belowTwo_strictWeight
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F) :
    IsWeightLT transverseCubicWeight 2
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2
          (F - initialForm transverseCubicWeight 3 F)) := by
  exact sub_initialForm_isWeightLT
    (sourceCubic_belowThree_weightLE_two F hcap)

/-- The transverse-transverse Hessian of the actual subquadratic
remainder vanishes. This is an identity in the original source
polynomial ring, BEFORE any longitudinal slice. -/
theorem sourceCubic_belowTwo_transverseHessian_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j : Fin 3) :
    hessian
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2
          (F - initialForm transverseCubicWeight 3 F))
      (.inr i) (.inr j) = 0 := by
  let R : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2
        (F - initialForm transverseCubicWeight 3 F)
  have hR : IsWeightLT transverseCubicWeight 2 R :=
    sourceCubic_belowTwo_strictWeight F hcap
  have hw :
      (2 : ℤ) - transverseCubicWeight (.inr i) -
        transverseCubicWeight (.inr j) = 0 := by
    simp [transverseCubicWeight]
  have hH : IsWeightLT transverseCubicWeight 0
      (hessian R (.inr i) (.inr j)) := by
    have h := hR.hessian_entry (.inr i) (.inr j)
    rw [hw] at h
    exact h
  exact transverseCubicWeight_lt_zero_eq_zero _ hH

/-- The transverse Hessian correction is EXACTLY the Hessian of
the source's weight-two layer. No lower transverse layer can
contribute to this matrix block. -/
theorem sourceCubic_repair_transverseHessian_eq_secondLayer
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j : Fin 3) :
    hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j) =
      hessian (initialForm transverseCubicWeight 2
        (F - initialForm transverseCubicWeight 3 F))
        (.inr i) (.inr j) := by
  have hz :=
    sourceCubic_belowTwo_transverseHessian_zero F hcap i j
  have heq :
      hessian
        ((F - initialForm transverseCubicWeight 3 F) -
          initialForm transverseCubicWeight 2
            (F - initialForm transverseCubicWeight 3 F))
        (.inr i) (.inr j) =
      hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j) -
      hessian (initialForm transverseCubicWeight 2
        (F - initialForm transverseCubicWeight 3 F))
        (.inr i) (.inr j) := by
    simp [hessian_apply]
  rw [heq] at hz
  exact sub_eq_zero.mp hz

/-- The weight-two Hessian is the EXACT weight-shifted component
of the source remainder's Hessian. This will identify the first
determinant correction without introducing a formal fake layer. -/
theorem sourceCubic_secondLayer_hessian_entry
    (F : SB K) (i j : Unit ⊕ Fin 3) :
    hessian
      (initialForm transverseCubicWeight 2
        (F - initialForm transverseCubicWeight 3 F)) i j =
      initialForm transverseCubicWeight
        (2 - transverseCubicWeight i - transverseCubicWeight j)
        (hessian (F - initialForm transverseCubicWeight 3 F) i j) := by
  exact hessian_initialForm_entry transverseCubicWeight 2
    (F - initialForm transverseCubicWeight 3 F) i j

/-- The weight-two component of the cubic remainder is just
the actual weight-two component of the original source F.
The already-extracted weight-three component cannot interfere. -/
theorem sourceCubic_remainder_secondLayer_eq_sourceSecondLayer
    (F : SB K) :
    initialForm transverseCubicWeight 2
        (F - initialForm transverseCubicWeight 3 F) =
      initialForm transverseCubicWeight 2 F := by
  have hzero :
      initialForm transverseCubicWeight 2
        (initialForm transverseCubicWeight 3 F) = 0 :=
    initialForm_eq_zero_of_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous transverseCubicWeight 3 F)
      2 (by norm_num)
  rw [map_sub, hzero, sub_zero]

/-- The complete source-derived transverse Hessian repair is
precisely the Hessian of the original quadratic transverse layer. -/
theorem sourceCubic_repair_transverseHessian_eq_sourceSecondLayer
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j : Fin 3) :
    hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j) =
      hessian (initialForm transverseCubicWeight 2 F)
        (.inr i) (.inr j) := by
  rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
  exact sourceCubic_repair_transverseHessian_eq_secondLayer F hcap i j

end
end HC4.Polynomial.RankThreeCubic
