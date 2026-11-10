import HC4.Valuation.QuadraticTransverseCapRankThreeFieldDerivation
import HC4.Valuation.QuadraticTransverseCapRankThreeLongitudinalDrift
import Mathlib.Tactic

/-!
# Exact affine-rational inverse descent to a polynomial inverse

Generic rank three initially gives an inverse only in the rational-function
field. The hard part is showing that this inverse has zero second derivative
and hence has affine entries over the ground field.

Once AFFINE RATIONAL ENTRIES have been proved, however, all further
integrality follows formally, without valuations or root arguments:

* each entry a + b x is the image of C(a)+C(b)*X under the polynomial embedding;
* injectivity of this embedding descends the two matrix-inverse equations
  from the rational field to the polynomial ring;
* the polynomial inverse makes det C a nonzero constant.

This lemma works for any injective polynomial embedding into any field,
not only for RatFunc. It does NOT assume that generic invertibility
already implies polynomial invertibility.
-/

namespace HC4.Valuation

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Entrywise affine elements over the ground field can be lifted
to a polynomial matrix, provided x is the embedded polynomial X. -/
theorem quadraticTransverse_affineFieldMatrix_polynomialLift
    (f : Polynomial K →+* L)
    (hC : ∀ c : K, f (Polynomial.C c) = algebraMap K L c)
    (x : L)
    (hX : f Polynomial.X = x)
    (M : Matrix (Fin 3) (Fin 3) L)
    (A B : Matrix (Fin 3) (Fin 3) K)
    (hM : ∀ i j : Fin 3,
      M i j = algebraMap K L (A i j) +
        algebraMap K L (B i j) * x) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      P.map f = M := by
  let P : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.C (A i j) +
      Polynomial.C (B i j) * Polynomial.X
  refine ⟨P, ?_⟩
  ext i j
  change f (Polynomial.C (A i j) +
    Polynomial.C (B i j) * Polynomial.X) = M i j
  rw [map_add, map_mul, hC, hC, hX]
  exact (hM i j).symm

/-- Two-sided inverses descend along any injective polynomial
ring homomorphism when the field inverse entries lie in the
polynomial image. -/
theorem quadraticTransverse_polynomialMatrix_inverse_descends
    (f : Polynomial K →+* L)
    (hf : Function.Injective f)
    (C P : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCP : C.map f * P.map f = 1)
    (hPC : P.map f * C.map f = 1) :
    C * P = 1 ∧ P * C = 1 := by
  have hleft : (C * P).map f = 1 := by
    rw [Matrix.map_mul]
    exact hCP
  have hright : (P * C).map f = 1 := by
    rw [Matrix.map_mul]
    exact hPC
  constructor
  · ext i j
    apply hf
    have h := congrArg
      (fun H : Matrix (Fin 3) (Fin 3) L => H i j) hleft
    simpa [Matrix.map_apply, Matrix.one_apply] using h
  · ext i j
    apply hf
    have h := congrArg
      (fun H : Matrix (Fin 3) (Fin 3) L => H i j) hright
    simpa [Matrix.map_apply, Matrix.one_apply] using h

/-- **Integral descent of the generically invertible quadratic
transverse block from affine rational reciprocal normal form.**

The assumptions describe only the actual rational inverse C⁻¹
and the AFFINE consequence of its Riccati ODE. The resulting
polynomial inverse and constant nonzero determinant are
CONCLUSIONS, not assumptions. -/
theorem quadraticTransverse_affineFieldInverse_polynomialAndConstantDet
    (f : Polynomial K →+* L)
    (hf : Function.Injective f)
    (hC : ∀ c : K, f (Polynomial.C c) = algebraMap K L c)
    (x : L)
    (hX : f Polynomial.X = x)
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) L)
    (hCM : C.map f * M = 1)
    (hMC : M * C.map f = 1)
    (A B : Matrix (Fin 3) (Fin 3) K)
    (hM : ∀ i j : Fin 3,
      M i j = algebraMap K L (A i j) +
        algebraMap K L (B i j) * x) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      C * P = 1 ∧ P * C = 1 ∧
        ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  obtain ⟨P, hPM⟩ :=
    quadraticTransverse_affineFieldMatrix_polynomialLift
      f hC x hX M A B hM
  have hCP : C.map f * P.map f = 1 := by
    rw [hPM]
    exact hCM
  have hPC : P.map f * C.map f = 1 := by
    rw [hPM]
    exact hMC
  obtain ⟨hleft, hright⟩ :=
    quadraticTransverse_polynomialMatrix_inverse_descends
      f hf C P hCP hPC
  obtain ⟨d, hd, hconst⟩ :=
    quadraticTransverse_polynomialMatrixInverse_det_constant
      C P hleft
  exact ⟨P, hleft, hright, d, hd, hconst⟩

end

end HC4.Valuation
