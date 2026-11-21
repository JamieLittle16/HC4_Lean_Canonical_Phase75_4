import HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
import Mathlib.Tactic

/-!
# A18.5.40: undo the terminal translation

A18.5.38--39 identify the translated coefficient polynomial with a pure
power.  For the terminal pencil calculation it is more convenient to return
to the original affine-line coordinate.  Translation is an automorphism, so

    translate alpha phi = C c * X^D

is equivalent to

    phi = C c * (X - C alpha)^D.

This file records the inverse-translation identity and exposes that literal
binomial form at the rank-three terminal interface.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Scalar translation is inverted by translation through the negative
scalar. -/
theorem translatePolynomial_neg_left_inverse
    (alpha : K) (p : Polynomial K) :
    translatePolynomial (-alpha) (translatePolynomial alpha p) = p := by
  simp [translatePolynomial, Polynomial.comp_assoc]

/-- A translated pure power is the corresponding unshifted binomial power. -/
theorem eq_binomial_power_of_translate_eq_pure_power
    {alpha c : K} {p : Polynomial K} {D : ℕ}
    (hpure : translatePolynomial alpha p =
      Polynomial.C c * Polynomial.X ^ D) :
    p = Polynomial.C c *
      (Polynomial.X - Polynomial.C alpha) ^ D := by
  have h := congrArg (translatePolynomial (-alpha)) hpure
  rw [translatePolynomial_neg_left_inverse] at h
  simpa [translatePolynomial, Polynomial.comp_assoc, sub_eq_add_neg] using h

/-- **Unshifted terminal binomial form.**

The coefficient polynomial of every genuine singular affine rank-three
terminal is literally a nonzero scalar times a power of one nontrivial
binomial. -/
theorem rankThreeTerminal_eq_binomial_power
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    ∃ alpha c : K,
      alpha ≠ 0 ∧ c ≠ 0 ∧
      phi = Polynomial.C c *
        (Polynomial.X - Polynomial.C alpha) ^ phi.natDegree := by
  let N := rankThreeTerminal_binomialNormalForm
    L hA hB hC hu1 hphiDeg hphi0 hdet
  refine ⟨N.root, N.scalar, N.root_ne_zero, N.scalar_ne_zero, ?_⟩
  exact eq_binomial_power_of_translate_eq_pure_power
    N.translated_eq_pure_power

end

end HC4.RationalRigidity
