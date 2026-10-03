import HC4.Newton.GeneralFourBlockSchur
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Binary Schur projective motion

State-free algebra for the final source-honest HC4 ray closure.

For a rank-one symmetric binary Schur block

    S = [[A,B],[B,C]],    A*C = B^2,

the projective wedge in source direction `k` is

    A * d_k B - B * d_k A.

Two facts are isolated here.

1. If `B` is related to `A` by a genuinely moving monomial factor,
   `beta * B = alpha * m * A`, then differentiating this relation shows the
   projective wedge is nonzero as soon as `A`, `alpha`, and `d_k m` are
   nonzero.
2. Differentiating `A*C = B^2` gives the negative-square identity

       A^2 det(d_k S) = -(A d_k B - B d_k A)^2.

Consequently moving projective Schur geometry supplies a literal rank-two
source.  No Rees clock, blocker defect, or HC4 state occurs in this file.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Denominator-free projective wedge of a binary polynomial Schur line. -/
def binarySchurProjectiveWedge
    (A B : MvPolynomial (Fin 4) K) (k : Fin 4) :
    MvPolynomial (Fin 4) K :=
  A * MvPolynomial.pderiv k B -
    B * MvPolynomial.pderiv k A

/-- Determinant of the source derivative of a symmetric binary Schur block. -/
def binarySchurDerivativeDet
    (A B C : MvPolynomial (Fin 4) K) (k : Fin 4) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv k A * MvPolynomial.pderiv k C -
    MvPolynomial.pderiv k B * MvPolynomial.pderiv k B

/-- Differentiating a scaled moving-line relation exposes the projective
wedge exactly.  This is the division-free identity used by the terminal ray
closure. -/
theorem binarySchurProjectiveWedge_scaledRelation
    (A B m : MvPolynomial (Fin 4) K)
    (alpha beta : K) (k : Fin 4)
    (hrel : MvPolynomial.C beta * B = MvPolynomial.C alpha * m * A) :
    MvPolynomial.C beta * binarySchurProjectiveWedge A B k =
      MvPolynomial.C alpha * A ^ 2 * MvPolynomial.pderiv k m := by
  have hdiff := congrArg (MvPolynomial.pderiv k) hrel
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    zero_mul, zero_add] at hdiff
  unfold binarySchurProjectiveWedge
  calc
    MvPolynomial.C beta *
        (A * MvPolynomial.pderiv k B -
          B * MvPolynomial.pderiv k A) =
        A * (MvPolynomial.C beta * MvPolynomial.pderiv k B) -
          (MvPolynomial.C beta * B) * MvPolynomial.pderiv k A := by ring
    _ = A *
          (MvPolynomial.C alpha *
              (MvPolynomial.pderiv k m * A +
                m * MvPolynomial.pderiv k A)) -
          (MvPolynomial.C alpha * m * A) *
            MvPolynomial.pderiv k A := by
      rw [hrel, hdiff]
      ring
    _ = MvPolynomial.C alpha * A ^ 2 * MvPolynomial.pderiv k m := by
      ring

/-- A genuinely moving monomial factor forces a nonconstant raw binary Schur
kernel line.  Notice that no nonvanishing assumption on `beta` is needed: if
the wedge vanished, the left side of the exact scaled identity would vanish
regardless. -/
theorem binarySchurProjectiveWedge_ne_zero_of_scaledRelation
    (A B m : MvPolynomial (Fin 4) K)
    (alpha beta : K) (k : Fin 4)
    (hrel : MvPolynomial.C beta * B = MvPolynomial.C alpha * m * A)
    (halpha : alpha ≠ 0)
    (hA : A ≠ 0)
    (hdm : MvPolynomial.pderiv k m ≠ 0) :
    binarySchurProjectiveWedge A B k ≠ 0 := by
  intro hwedge
  have hid := binarySchurProjectiveWedge_scaledRelation
    A B m alpha beta k hrel
  have hrhs :
      MvPolynomial.C alpha * A ^ 2 * MvPolynomial.pderiv k m ≠ 0 := by
    have hCalpha :
        (MvPolynomial.C alpha : MvPolynomial (Fin 4) K) ≠ 0 :=
      MvPolynomial.C_ne_zero.mpr halpha
    exact mul_ne_zero (mul_ne_zero hCalpha (pow_ne_zero 2 hA)) hdm
  apply hrhs
  rw [← hid, hwedge]
  ring

/-- State-free B38 negative-square identity.  The existing closing-source
version is a specialization of this algebraic statement. -/
theorem binarySchurDerivativeDet_negativeSquare
    (A B C : MvPolynomial (Fin 4) K)
    (k : Fin 4)
    (hrankOne : A * C = B * B) :
    A ^ 2 * binarySchurDerivativeDet A B C k =
      -(binarySchurProjectiveWedge A B k) ^ 2 := by
  let Ap : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k A
  let Bp : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k B
  let Cp : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k C

  have hdiff := congrArg (MvPolynomial.pderiv k) hrankOne
  have hdiffRaw : A * Cp + C * Ap = B * Bp + B * Bp := by
    simpa [Ap, Bp, Cp, MvPolynomial.pderiv_mul] using hdiff
  have hdiff' : Ap * C + A * Cp = Bp * B + B * Bp := by
    calc
      Ap * C + A * Cp = A * Cp + C * Ap := by ring
      _ = B * Bp + B * Bp := hdiffRaw
      _ = Bp * B + B * Bp := by ring

  have hzero :
      A ^ 2 * (Ap * Cp - Bp * Bp) +
        (A * Bp - B * Ap) ^ 2 = 0 := by
    calc
      A ^ 2 * (Ap * Cp - Bp * Bp) +
          (A * Bp - B * Ap) ^ 2 =
          A * Ap *
              ((Ap * C + A * Cp) - (Bp * B + B * Bp)) -
            Ap ^ 2 * (A * C - B * B) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr hdiff', sub_eq_zero.mpr hrankOne]
        ring

  unfold binarySchurDerivativeDet binarySchurProjectiveWedge
  change A ^ 2 * (Ap * Cp - Bp * Bp) =
    -(A * Bp - B * Ap) ^ 2
  calc
    A ^ 2 * (Ap * Cp - Bp * Bp) =
        (A ^ 2 * (Ap * Cp - Bp * Bp) +
          (A * Bp - B * Ap) ^ 2) -
          (A * Bp - B * Ap) ^ 2 := by ring
    _ = -(A * Bp - B * Ap) ^ 2 := by rw [hzero]; ring

/-- A nonzero projective wedge in a rank-one binary Schur block forces the
source derivative block to have nonzero determinant. -/
theorem binarySchurDerivativeDet_ne_zero_of_wedge
    (A B C : MvPolynomial (Fin 4) K)
    (k : Fin 4)
    (hrankOne : A * C = B * B)
    (hwedge : binarySchurProjectiveWedge A B k ≠ 0) :
    binarySchurDerivativeDet A B C k ≠ 0 := by
  intro hdet
  have hneg : -(binarySchurProjectiveWedge A B k) ^ 2 = 0 := by
    calc
      -(binarySchurProjectiveWedge A B k) ^ 2 =
          A ^ 2 * binarySchurDerivativeDet A B C k :=
        (binarySchurDerivativeDet_negativeSquare A B C k hrankOne).symm
      _ = 0 := by rw [hdet]; ring
  have hsq : (binarySchurProjectiveWedge A B k) ^ 2 = 0 :=
    neg_eq_zero.mp hneg
  exact (pow_ne_zero 2 hwedge) hsq

/-- Combined source-honest rank-two certificate: a scaled moving-line relation
plus rank-one Schur singularity already gives a nonzero derivative determinant. -/
theorem binarySchurDerivativeDet_ne_zero_of_scaledMotion
    (A B C m : MvPolynomial (Fin 4) K)
    (alpha beta : K) (k : Fin 4)
    (hrankOne : A * C = B * B)
    (hrel : MvPolynomial.C beta * B = MvPolynomial.C alpha * m * A)
    (halpha : alpha ≠ 0)
    (hA : A ≠ 0)
    (hdm : MvPolynomial.pderiv k m ≠ 0) :
    binarySchurDerivativeDet A B C k ≠ 0 := by
  have hwedge := binarySchurProjectiveWedge_ne_zero_of_scaledRelation
    A B m alpha beta k hrel halpha hA hdm
  exact binarySchurDerivativeDet_ne_zero_of_wedge A B C k hrankOne hwedge

end

end HC4.Polynomial
