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
  · apply Matrix.ext
    intro i j
    apply hf
    have h := congrArg
      (fun H : Matrix (Fin 3) (Fin 3) L => H i j) hleft
    simpa [Matrix.map_apply, Matrix.one_apply] using h
  · apply Matrix.ext
    intro i j
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

/-- **Riccati-to-polynomial-inverse bridge over a differential field.**

The hypotheses are exactly:
  * a field of rational coefficients L carrying an honest K-derivation;
  * an indeterminate x with D x = 1 and constants exactly K;
  * the injected polynomial transverse Hessian C with a two-sided
    inverse M over L;
  * the genuine matrix Riccati equation D²C = 2 (DC) M (DC).

The output is a two-sided inverse already in K[x] and a CONSTANT
nonzero polynomial determinant for C. Neither integrality nor
constancy is assumed. This is the reusable algebraic core of the
generic-rank-three quadratic case.

The remaining work is to establish the differential-field facts
for L=RatFunc K and to obtain the Riccati equation from the
actual source's y² Hessian determinant coefficient. -/
theorem quadraticTransverse_fieldRiccati_polynomialInverse_constantDet
    (f : Polynomial K →+* L)
    (hf : Function.Injective f)
    (hC : ∀ c : K, f (Polynomial.C c) = algebraMap K L c)
    (x : L)
    (hX : f Polynomial.X = x)
    (D : Derivation K L L)
    (hx : D x = 1)
    (hconstants :
      ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) L)
    (hCM : C.map f * M = 1)
    (hMC : M * C.map f = 1)
    (hRiccati :
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D (C.map f)) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D (C.map f) * M) *
          quadraticTransverse_fieldMatrixDerivative D (C.map f))) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      C * P = 1 ∧ P * C = 1 ∧
        ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  have hsecond :=
    quadraticTransverse_fieldReciprocal_secondDerivative_zero
      D (C.map f) M hCM hMC hRiccati
  obtain ⟨A, B, hM⟩ :=
    quadraticTransverse_fieldMatrix_secondDerivative_zero_affine
      D x hx hconstants M hsecond
  exact quadraticTransverse_affineFieldInverse_polynomialAndConstantDet
    f hf hC x hX C M hCM hMC A B hM

/-- **Polynomial inverse descent directly from compatible rational
differentiation and polynomial-valued constants.**

This version does not require identifying the ground-field scalar
embedding with an abstract Algebra map. It is ideal for RatFunc K,
where both the derivative compatibility and the constants result
can be expressed in terms of the same polynomial ring embedding.

Once the Riccati equation and these ordinary differential-field
facts are supplied, polynomial invertibility and constant
determinant follow as THEOREMS. -/
theorem quadraticTransverse_compatibleDerivation_integralInverse
    (f : Polynomial K →+* L)
    (hf : Function.Injective f)
    (D : Derivation K L L)
    (hpoly : ∀ p : Polynomial K,
      D (f p) = f (Polynomial.derivative p))
    (hconstants :
      ∀ z : L, D z = 0 → ∃ c : K, z = f (Polynomial.C c))
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) L)
    (hCM : C.map f * M = 1)
    (hMC : M * C.map f = 1)
    (hRiccati :
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D (C.map f)) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D (C.map f) * M) *
          quadraticTransverse_fieldMatrixDerivative D (C.map f))) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      C * P = 1 ∧ P * C = 1 ∧
        ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  have hsecond :=
    quadraticTransverse_fieldReciprocal_secondDerivative_zero
      D (C.map f) M hCM hMC hRiccati
  have hX : D (f Polynomial.X) = 1 := by
    rw [hpoly]
    simp
  have hderC (c : K) : D (f (Polynomial.C c)) = 0 := by
    rw [hpoly]
    simp
  have hex : ∀ i j : Fin 3, ∃ a b : K,
      M i j = f (Polynomial.C a +
        Polynomial.C b * Polynomial.X) := by
    intro i j
    have hsecondij : D (D (M i j)) = 0 :=
      congrArg (fun N : Matrix (Fin 3) (Fin 3) L => N i j) hsecond
    obtain ⟨b, hb⟩ := hconstants (D (M i j)) hsecondij
    have hzero :
        D (M i j - f (Polynomial.C b) * f Polynomial.X) = 0 := by
      rw [map_sub, D.leibniz]
      simp [hderC, hX, hb, smul_eq_mul]
    obtain ⟨a, ha⟩ := hconstants
      (M i j - f (Polynomial.C b) * f Polynomial.X) hzero
    refine ⟨a, b, ?_⟩
    have haff :
        M i j = f (Polynomial.C a) +
          f (Polynomial.C b) * f Polynomial.X :=
      sub_eq_iff_eq_add.mp ha
    simpa only [map_add, map_mul] using haff
  classical
  choose a b hab using hex
  let P : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.C (a i j) +
      Polynomial.C (b i j) * Polynomial.X
  have hPM : P.map f = M := by
    ext i j
    change f (Polynomial.C (a i j) +
      Polynomial.C (b i j) * Polynomial.X) = M i j
    exact (hab i j).symm
  have hCP : C.map f * P.map f = 1 := by rw [hPM]; exact hCM
  have hPC : P.map f * C.map f = 1 := by rw [hPM]; exact hMC
  obtain ⟨hleft, hright⟩ :=
    quadraticTransverse_polynomialMatrix_inverse_descends
      f hf C P hCP hPC
  obtain ⟨d, hd, hdet⟩ :=
    quadraticTransverse_polynomialMatrixInverse_det_constant
      C P hleft
  exact ⟨P, hleft, hright, d, hd, hdet⟩

end

end HC4.Valuation
