import HC4.Valuation.QuadraticTransverseCapRankThreeDrift
import Mathlib.Tactic

/-!
# Unimodular affine reciprocal has cubic nilpotent slope

Suppose the rank-three reciprocal matrix has affine form
M(x) = A + xB, with det M(x)=det A ≠ 0. If B=A N,
then M(x)=A(I+xN) and exact determinant preservation gives
det(I+xN)=1. The already-proved cubic coefficient/Cayley–Hamilton
identity forces N³=0.

This is an explicit, denominator-free matrix-polynomial identity:
it does not assume nilpotence as a geometric endpoint input.
The reciprocal affine and determinant-constancy steps must still
be supplied from the real represented source.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Exact constant-matrix left factorisation of an affine
polynomial matrix when B=A N. No commutation between A and
N is assumed. -/
theorem quadraticTransverse_affineMatrix_factor
    (A B N : Matrix (Fin 3) (Fin 3) K)
    (hB : B = A * N) :
    A.map Polynomial.C +
      (Polynomial.X : Polynomial K) • B.map Polynomial.C =
    A.map Polynomial.C *
      (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C) := by
  rw [hB]
  simp only [Matrix.map_mul, mul_add, mul_one, Matrix.mul_smul]

/-- A genuinely unimodular affine 3x3 reciprocal has cubic-nilpotent
normalised slope N=A⁻¹B. Here the algebraic factorisation B=A N
is explicit; no inverse is silently chosen from a rank witness. -/
theorem quadraticTransverse_affineMatrix_nilpotentSlope
    (A B N : Matrix (Fin 3) (Fin 3) K)
    (hA : A.det ≠ 0)
    (hB : B = A * N)
    (hdet :
      (A.map Polynomial.C +
        (Polynomial.X : Polynomial K) • B.map Polynomial.C).det =
          Polynomial.C A.det) :
    N ^ 3 = 0 := by
  have hfactor :=
    quadraticTransverse_affineMatrix_factor A B N hB
  have hAmap :
      (A.map Polynomial.C).det = Polynomial.C A.det := by
    exact (Polynomial.C.map_det A).symm
  have hprod :
      Polynomial.C A.det *
        (1 + (Polynomial.X : Polynomial K) •
          N.map Polynomial.C).det = Polynomial.C A.det := by
    have h := congrArg Matrix.det hfactor
    rw [Matrix.det_mul, hAmap, hdet] at h
    exact h.symm
  have hdetunit :
      (1 + (Polynomial.X : Polynomial K) •
        N.map Polynomial.C).det = 1 := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hA)
    simpa using hprod
  exact quadraticTransverse_cubicNilpotent_of_affineDet_one N hdetunit

end

end HC4.Valuation
