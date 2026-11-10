import HC4.Valuation.QuadraticTransverseCapSourceOriginPivot
import Mathlib.Tactic

/-!
# Singular symmetric transverse three-blocks need no shear pivot

For a symmetric 3x3 matrix C over an integral domain with det C = 0,
any nonzero 2x2 minor implies one of the THREE original principal
2x2 minors is nonzero. This is stronger than a six-way shear pivot
when working in the generic-rank-two Schur branch.

The essential identities are

  (bf-ce)^2 = (af-c²)(df-e²) - f det C
  (be-cd)^2 = (ad-b²)(df-e²) - d det C
  (ae-bc)^2 = (ad-b²)(af-c²) - a det C.

If all principal minors vanish and det C=0, the three mixed minors
have square zero and hence vanish over a domain. This permits a
principal Schur chart without changing source coordinates.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The six-way transverse minor witness automatically gives one of
three principal 2x2 pivots when the symmetric 3x3 block is singular.
The proof is denominator-free over any integral domain. -/
theorem symmetricThreeBlock_singular_minor_implies_principalPivot
    (C : GeneralThreeBlock R)
    (hdet : C.determinantCore = 0)
    (hminor :
      C.d * C.f - C.e * C.e ≠ 0 ∨
      C.b * C.f - C.c * C.e ≠ 0 ∨
      C.b * C.e - C.c * C.d ≠ 0 ∨
      C.a * C.f - C.c * C.c ≠ 0 ∨
      C.a * C.e - C.b * C.c ≠ 0 ∨
      C.a * C.d - C.b * C.b ≠ 0) :
    C.d * C.f - C.e * C.e ≠ 0 ∨
    C.a * C.f - C.c * C.c ≠ 0 ∨
    C.a * C.d - C.b * C.b ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨hdf, haf, had⟩
  have hbfSq :
      (C.b * C.f - C.c * C.e) *
        (C.b * C.f - C.c * C.e) = 0 := by
    calc
      (C.b * C.f - C.c * C.e) *
          (C.b * C.f - C.c * C.e) =
        (C.a * C.f - C.c * C.c) *
          (C.d * C.f - C.e * C.e) -
          C.f * C.determinantCore := by
            unfold GeneralThreeBlock.determinantCore
            ring
      _ = 0 := by rw [haf, hdf, hdet]; ring
  have hbeSq :
      (C.b * C.e - C.c * C.d) *
        (C.b * C.e - C.c * C.d) = 0 := by
    calc
      (C.b * C.e - C.c * C.d) *
          (C.b * C.e - C.c * C.d) =
        (C.a * C.d - C.b * C.b) *
          (C.d * C.f - C.e * C.e) -
          C.d * C.determinantCore := by
            unfold GeneralThreeBlock.determinantCore
            ring
      _ = 0 := by rw [had, hdf, hdet]; ring
  have haeSq :
      (C.a * C.e - C.b * C.c) *
        (C.a * C.e - C.b * C.c) = 0 := by
    calc
      (C.a * C.e - C.b * C.c) *
          (C.a * C.e - C.b * C.c) =
        (C.a * C.d - C.b * C.b) *
          (C.a * C.f - C.c * C.c) -
          C.a * C.determinantCore := by
            unfold GeneralThreeBlock.determinantCore
            ring
      _ = 0 := by rw [had, haf, hdet]; ring
  have hbf : C.b * C.f - C.c * C.e = 0 := by
    rcases mul_eq_zero.mp hbfSq with h | h <;> exact h
  have hbe : C.b * C.e - C.c * C.d = 0 := by
    rcases mul_eq_zero.mp hbeSq with h | h <;> exact h
  have hae : C.a * C.e - C.b * C.c = 0 := by
    rcases mul_eq_zero.mp haeSq with h | h <;> exact h
  rcases hminor with h | h | h | h | h | h
  · exact h hdf
  · exact h hbf
  · exact h hbe
  · exact h haf
  · exact h hae
  · exact h had

/-- Source-honest singular branch: the represented source's polynomial
transverse block has an actual principal 2x2 Schur pivot, in ORIGINAL
coordinates, with no additional source shear or fictitious rank state. -/
theorem quadraticTransverseCapSource_singular_principalPivot
    {K : Type*} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hsingular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore = 0) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    C.d * C.f - C.e * C.e ≠ 0 ∨
    C.a * C.f - C.c * C.c ≠ 0 ∨
    C.a * C.d - C.b * C.b ≠ 0 := by
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  exact symmetricThreeBlock_singular_minor_implies_principalPivot C
    hsingular
    (quadraticTransverseCapSource_axisThreeBlock_polynomialRankTwo
      F hbound hdet)

end

end HC4.Valuation
