import HC4.Polynomial.RankThreeCubicDetOnePoleRepairDichotomySource
import Mathlib.Tactic

/-!
# The remaining longitudinal mixed repair has exactly weight zero

For the actual source F of transverse cubic weight at most three,
remove its *actual* weight-three and weight-two components.
The remainder R has strictly less than two transverse weight.

Its Hessian entries mixing the longitudinal and transverse
variables consequently have transverse weight strictly below one.
Since transverse weights of monomials are nonnegative integers,
these entries are entirely their own exact weight-zero initial forms.

This strengthens derivative-vanishing to an exact source equality.
It does not assert that such a weight-zero correction vanishes.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
noncomputable section

variable {K : Type*} [Field K]
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The strictly subquadratic actual source remainder cannot
contain any positive-transverse-weight longitudinal mixed
Hessian contribution. -/
theorem sourceCubic_subTwo_mixedHessian_eq_weightZero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i : Fin 3) :
    let R : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    initialForm transverseCubicWeight 0
      (hessian R (.inl ()) (.inr i)) =
        hessian R (.inl ()) (.inr i) := by
  let R : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  have hR : IsWeightLT transverseCubicWeight 2 R := by
    change IsWeightLT transverseCubicWeight 2
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F)
    rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
    exact sourceCubic_belowTwo_strictWeight F hcap
  let P : SB K := hessian R (.inl ()) (.inr i)
  have hP : IsWeightLT transverseCubicWeight 1 P := by
    have h := hR.hessian_entry (.inl ()) (.inr i)
    have hw :
        (2 : ℤ) - transverseCubicWeight (.inl ()) -
          transverseCubicWeight (.inr i) = 1 := by
      simp [transverseCubicWeight]
    rw [hw] at h
    exact h
  have hP0 : IsWeightLE transverseCubicWeight 0 P := by
    intro d hd
    have h := hP hd
    omega
  have hbelow : IsWeightLT transverseCubicWeight 0
      (P - initialForm transverseCubicWeight 0 P) :=
    sub_initialForm_isWeightLT hP0
  have hzero :
      P - initialForm transverseCubicWeight 0 P = 0 :=
    transverseCubicWeight_lt_zero_eq_zero _ hbelow
  change initialForm transverseCubicWeight 0 P = P
  exact (sub_eq_zero.mp hzero).symm

end
end HC4.Polynomial.RankThreeCubic
