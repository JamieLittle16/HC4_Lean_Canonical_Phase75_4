import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Determinant coefficients for a fixed kernel of the top transverse cubic

These identities are over an arbitrary commutative ring. They apply to
the two possible fibre charts once a fixed transverse kernel direction
has been extracted from a rank-two cubic face.
-/

namespace HC4.Polynomial.RankTwoCubic

open scoped Matrix

variable {R : Type*} [CommRing R]

/-- The first determinant jet on a rank-two ternary block sees only the
entry in its kernel direction. This detects the affine direction in
the elementary cone proof for ternary cubics. -/
theorem ternary_kernelDiagonal_firstJet (a b c : R) (E : Matrix (Fin 3) (Fin 3) R) :
    TrivSqZeroExt.snd
      (Matrix.of (fun i j => ((!![a, b, 0; b, c, 0; 0, 0, 0] :
        Matrix (Fin 3) (Fin 3) R) i j, E i j)) :
          Matrix (Fin 3) (Fin 3) (DualNumber R)).det =
        (a * c - b ^ 2) * E 2 2 := by
  simp [Matrix.det_fin_three]
  ring

/-- If a ternary cubic is affine in its last variable, the linear
determinant coefficient in that variable factors through the
determinant of the quadratic coefficient's binary Hessian. -/
theorem ternary_affineCubic_firstDifference (a b c A B C x y : R) :
    (!![a + A, b + B, A * x + B * y;
        b + B, c + C, B * x + C * y;
        A * x + B * y, B * x + C * y, 0] : Matrix (Fin 3) (Fin 3) R).det -
      (!![a, b, A * x + B * y;
          b, c, B * x + C * y;
          A * x + B * y, B * x + C * y, 0] : Matrix (Fin 3) (Fin 3) R).det =
        -((A * C - B ^ 2) * (A * x ^ 2 + 2 * B * x * y + C * y ^ 2)) := by
  simp [Matrix.det_fin_three]
  ring

/-- The Hessian pencil in a fibre variable that enters affinely. The
first row is indexed by the fibre, and the second by the longitudinal
variable. -/
def affineFibrePencil
    (h p q c d r k e f A B D t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, k, e, f;
     k, h + t * A, p + t * B, q + t * D;
     e, p + t * B, c, d;
     f, q + t * D, d, r]

private theorem det_affineFibrePencil
    (h p q c d r k e f A B D t : R) :
    (affineFibrePencil h p q c d r k e f A B D t).det =
      -(k ^ 2 * (c * r - d ^ 2)
        + e ^ 2 * ((h + t * A) * r - (q + t * D) ^ 2)
        + f ^ 2 * ((h + t * A) * c - (p + t * B) ^ 2)
        + 2 * k * e * ((q + t * D) * d - (p + t * B) * r)
        + 2 * k * f * ((p + t * B) * d - (q + t * D) * c)
        + 2 * e * f * ((p + t * B) * (q + t * D) - (h + t * A) * d)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, affineFibrePencil, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Central second difference in the affine fibre is twice the square
of the wedge between its transverse row and its longitudinal derivative.
With a constant determinant this forces the transverse row to have
constant projective direction. -/
theorem affineFibre_secondDifference
    (h p q c d r k e f A B D : R) :
    (affineFibrePencil h p q c d r k e f A B D 1).det +
      (affineFibrePencil h p q c d r k e f A B D (-1)).det -
      2 * (affineFibrePencil h p q c d r k e f A B D 0).det =
        2 * (e * D - f * B) ^ 2 := by
  simp only [det_affineFibrePencil]
  ring

/-- After straightening the transverse row to `(e,0)`, the remaining
linear coefficient factors through the last transverse Hessian entry. -/
theorem straightenedFibre_firstDifference
    (h p q c d r k e A B : R) :
    (affineFibrePencil h p q c d r k e 0 A B 0 1).det -
      (affineFibrePencil h p q c d r k e 0 A B 0 0).det =
        -(r * (e ^ 2 * A - 2 * e * k * B)) := by
  simp only [det_affineFibrePencil]
  ring

/-- The determinant with a border supported only on the longitudinal row.
This is also the determinant formula for the pure-longitudinal affine
fibre branch. -/
theorem longitudinalBorder_det
    (h p q c d r k : R) :
    (affineFibrePencil h p q c d r k 0 0 0 0 0 0).det =
      -(k ^ 2 * (c * r - d ^ 2)) := by
  simp [det_affineFibrePencil]

/-- A three-variable Hessian pencil after the one-coordinate partial
Legendre transform. Only the longitudinal entry can be quadratic in the
fixed fibre output. -/
def partialLegendrePencil
    (a b h p q u v c d e t : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a + t * b + t ^ 2 * h, p + t * u, q + t * v;
     p + t * u, c, d;
     q + t * v, d, e]

/-- The second coefficient splits into the longitudinal second derivative
times the transverse determinant, and a mixed correction of strictly
smaller transverse degree in the rank-two cubic chart. -/
theorem partialLegendre_secondDifference
    (a b h p q u v c d e : R) :
    (partialLegendrePencil a b h p q u v c d e 1).det +
      (partialLegendrePencil a b h p q u v c d e (-1)).det -
      2 * (partialLegendrePencil a b h p q u v c d e 0).det =
        2 * (h * (c * e - d ^ 2) - (u ^ 2 * e - 2 * u * v * d + v ^ 2 * c)) := by
  simp [partialLegendrePencil, Matrix.det_fin_three]
  ring

section PolynomialRigidity

variable {K : Type*} [Field K] [CharZero K]

private theorem leadingCoeff_derivative (p : Polynomial K) (hp : 0 < p.natDegree) :
    p.derivative.leadingCoeff = p.leadingCoeff * (p.natDegree : K) := by
  have hdeg : p.derivative.natDegree = p.natDegree - 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative_eq p hp)
  have hnat : p.natDegree - 1 + 1 = p.natDegree := by omega
  have hcast : ((p.natDegree - 1 : ℕ) : K) + 1 = (p.natDegree : K) := by
    exact_mod_cast hnat
  change p.derivative.coeff p.derivative.natDegree =
    p.leadingCoeff * (p.natDegree : K)
  rw [hdeg, Polynomial.coeff_derivative, hnat, Polynomial.coeff_natDegree, hcast]

/-- The polynomial identity obtained after clearing denominators from
`(1 / p)'' = 0` forces a polynomial pivot to be constant. The same
identity comes from the linear determinant term in the affine-fibre
branch. -/
theorem derivative_eq_zero_of_reciprocalSecondIdentity (p : Polynomial K)
    (h : p * p.derivative.derivative = 2 * p.derivative ^ 2) :
    p.derivative = 0 := by
  by_contra hn
  have hp : 0 < p.natDegree := by
    by_contra! hdeg
    exact hn (Polynomial.derivative_of_natDegree_zero (by omega))
  have hpn : p ≠ 0 := by
    intro hp0
    apply hn
    simp [hp0]
  have hp' : 0 < p.derivative.natDegree := by
    by_contra! hdeg
    have hd : p.derivative.derivative = 0 :=
      Polynomial.derivative_of_natDegree_zero (by omega)
    rw [hd, mul_zero] at h
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hn) h.symm
  have hpdeg : p.derivative.natDegree = p.natDegree - 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative_eq p hp)
  have hncast : (p.derivative.natDegree : K) = (p.natDegree : K) - 1 := by
    apply eq_sub_of_add_eq
    exact_mod_cast (show p.derivative.natDegree + 1 = p.natDegree by omega)
  have h2 : (2 : Polynomial K).leadingCoeff = (2 : K) := by
    have hC : Polynomial.C (2 : K) = (2 : Polynomial K) := by
      rw [show (2 : K) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    rw [← hC, Polynomial.leadingCoeff_C]
  have hc := congrArg Polynomial.leadingCoeff h
  rw [Polynomial.leadingCoeff_mul, leadingCoeff_derivative p.derivative hp',
    leadingCoeff_derivative p hp, hncast, Polynomial.leadingCoeff_mul,
    h2, Polynomial.leadingCoeff_pow, leadingCoeff_derivative p hp] at hc
  have hnz : (p.natDegree : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hplus : (p.natDegree : K) + 1 ≠ 0 := by
    exact_mod_cast (show p.natDegree + 1 ≠ 0 by omega)
  apply mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (Polynomial.leadingCoeff_ne_zero.mpr hpn)) hnz) hplus
  linear_combination -hc

end PolynomialRigidity

end HC4.Polynomial.RankTwoCubic
