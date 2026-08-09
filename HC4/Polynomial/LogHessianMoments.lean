import HC4.Polynomial.ComplementaryFractionBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Logarithmic Hessian factorisation from line moments

For an exponent line `v + j w`, the scaled second derivatives of a polynomial
supported on that line are controlled by the three coefficient moments

    S0 = sum c_j t^j,
    S1 = sum j c_j t^j,
    S2 = sum j^2 c_j t^j.

This file proves the purely algebraic heart of the manuscript's logarithmic
Hessian identity.  If

    rho = S1 / S0,
    eta = (S2*S0 - S1^2) / S0^2,
    e = v + rho*w,

then the line-moment Hessian matrix is exactly

    S0 * (e e^T + eta w w^T - diag(e)).

No differentiation of Laurent monomials is used here.  A later bridge only has
to identify the scaled Hessian of an actual line-supported `MvPolynomial` with
the line-moment matrix below.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- The scaled Hessian matrix attached to the first three moments of a line of
exponents `v + j w`.  Entrywise this is

`S0*(vᵢvⱼ-δᵢⱼvᵢ) + S1*(vᵢwⱼ+wᵢvⱼ-δᵢⱼwᵢ) + S2*wᵢwⱼ`.
-/
def lineMomentHessian
    {K : Type*} [CommRing K]
    (v w : Fin 4 → K) (S0 S1 S2 : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j =>
    S0 * (v i * v j - if i = j then v i else 0) +
      S1 * (v i * w j + w i * v j - if i = j then w i else 0) +
      S2 * (w i * w j)

/-- The logarithmic Hessian core reconstructed from the three line moments. -/
def logarithmicCoreFromMoments
    {K : Type*} [Field K]
    (v w : Fin 4 → K) (S0 S1 S2 : K) : Matrix (Fin 4) (Fin 4) K :=
  let rho := S1 / S0
  let eta := (S2 * S0 - S1^2) / S0^2
  let e : Fin 4 → K := fun i => v i + rho * w i
  Matrix.of fun i j =>
    e i * e j + eta * (w i * w j) - if i = j then e i else 0

/-- Algebraic logarithmic-Hessian identity for a line of exponents.

This is the manuscript formula

`scaled Hessian = F * (e eᵀ + eta w wᵀ - diag(e))`

with `F=S0`, expressed only in terms of the coefficient moments. -/
theorem lineMomentHessian_eq_scaled_logarithmicCore
    {K : Type*} [Field K]
    (v w : Fin 4 → K) {S0 S1 S2 : K}
    (hS0 : S0 ≠ 0) :
    lineMomentHessian v w S0 S1 S2 =
      Matrix.of (fun i j => S0 * logarithmicCoreFromMoments v w S0 S1 S2 i j) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lineMomentHessian, logarithmicCoreFromMoments]
    field_simp [hS0] <;> ring
  · simp [lineMomentHessian, logarithmicCoreFromMoments, hij]
    field_simp [hS0] <;> ring

/-- Determinant form of the line-moment logarithmic-Hessian identity in four
variables. -/
theorem det_lineMomentHessian
    {K : Type*} [Field K]
    (v w : Fin 4 → K) {S0 S1 S2 : K}
    (hS0 : S0 ≠ 0) :
    (lineMomentHessian v w S0 S1 S2).det =
      S0^4 * (logarithmicCoreFromMoments v w S0 S1 S2).det := by
  rw [lineMomentHessian_eq_scaled_logarithmicCore v w hS0]
  calc
    (Matrix.of (fun i j =>
        S0 * logarithmicCoreFromMoments v w S0 S1 S2 i j)).det =
        (∏ _i : Fin 4, S0) *
          (logarithmicCoreFromMoments v w S0 S1 S2).det := by
            exact Matrix.det_mul_column
              (fun _i : Fin 4 => S0)
              (logarithmicCoreFromMoments v w S0 S1 S2)
    _ = S0^4 * (logarithmicCoreFromMoments v w S0 S1 S2).det := by
      rw [Fin.prod_univ_four]
      ring

/-- Base exponent `v=(0,0,kMβ₁,kMβ₂)` for a complementary edge. -/
def complementaryLogBaseExponent
    {K : Type*} [CommRing K]
    (b1 b2 k M : K) : Fin 4 → K :=
  ![0, 0, k * M * b1, k * M * b2]

/-- The affine exponent vector reconstructed from the complementary base and
line direction is exactly the exponent vector used by the Phase 68 core. -/
theorem complementaryLogExponent_eq_base_add_direction
    {K : Type*} [CommRing K]
    (a1 a2 b1 b2 h k M rho : K) :
    (fun i => complementaryLogBaseExponent b1 b2 k M i +
      rho * complementaryLogDirection a1 a2 b1 b2 h k i) =
      complementaryLogExponent a1 a2 b1 b2 h k M rho := by
  funext i
  fin_cases i <;>
    simp [complementaryLogBaseExponent, complementaryLogExponent,
      complementaryLogDirection] <;> ring

/-- The general moment core specialises exactly to the complementary core from
Phase 68. -/
theorem complementary_logarithmicCoreFromMoments_eq
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M S0 S1 S2 : K) :
    logarithmicCoreFromMoments
        (complementaryLogBaseExponent b1 b2 k M)
        (complementaryLogDirection a1 a2 b1 b2 h k)
        S0 S1 S2 =
      complementaryLogHessianCore
        a1 a2 b1 b2 h k M
        (S1 / S0) ((S2 * S0 - S1^2) / S0^2) := by
  let rho : K := S1 / S0
  let eta : K := (S2 * S0 - S1^2) / S0^2
  have he :
      (fun i => complementaryLogBaseExponent b1 b2 k M i +
        rho * complementaryLogDirection a1 a2 b1 b2 h k i) =
        complementaryLogExponent a1 a2 b1 b2 h k M rho :=
    complementaryLogExponent_eq_base_add_direction
      a1 a2 b1 b2 h k M rho
  ext i j
  have hei := congrFun he i
  have hej := congrFun he j
  change
    (complementaryLogBaseExponent b1 b2 k M i +
          rho * complementaryLogDirection a1 a2 b1 b2 h k i) *
        (complementaryLogBaseExponent b1 b2 k M j +
          rho * complementaryLogDirection a1 a2 b1 b2 h k j) +
        eta *
          (complementaryLogDirection a1 a2 b1 b2 h k i *
            complementaryLogDirection a1 a2 b1 b2 h k j) -
        (if i = j then
          complementaryLogBaseExponent b1 b2 k M i +
            rho * complementaryLogDirection a1 a2 b1 b2 h k i
        else 0) =
      complementaryLogExponent a1 a2 b1 b2 h k M rho i *
          complementaryLogExponent a1 a2 b1 b2 h k M rho j +
        eta *
          (complementaryLogDirection a1 a2 b1 b2 h k i *
            complementaryLogDirection a1 a2 b1 b2 h k j) -
        (if i = j then complementaryLogExponent a1 a2 b1 b2 h k M rho i else 0)
  rw [hei, hej]

/-- A zero line-moment Hessian determinant forces the complementary logarithmic
core determinant to vanish. -/
theorem complementary_core_det_zero_of_lineMoment_det_zero
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M S0 S1 S2 : K}
    (hS0 : S0 ≠ 0)
    (hdet :
      (lineMomentHessian
        (complementaryLogBaseExponent b1 b2 k M)
        (complementaryLogDirection a1 a2 b1 b2 h k)
        S0 S1 S2).det = 0) :
    (complementaryLogHessianCore
      a1 a2 b1 b2 h k M
      (S1 / S0) ((S2 * S0 - S1^2) / S0^2)).det = 0 := by
  have hfactor := det_lineMomentHessian
    (complementaryLogBaseExponent b1 b2 k M)
    (complementaryLogDirection a1 a2 b1 b2 h k)
    (S0 := S0) (S1 := S1) (S2 := S2) hS0
  have hz :
      S0^4 *
        (logarithmicCoreFromMoments
          (complementaryLogBaseExponent b1 b2 k M)
          (complementaryLogDirection a1 a2 b1 b2 h k)
          S0 S1 S2).det = 0 := by
    rw [← hfactor]
    exact hdet
  have hcore :
      (logarithmicCoreFromMoments
        (complementaryLogBaseExponent b1 b2 k M)
        (complementaryLogDirection a1 a2 b1 b2 h k)
        S0 S1 S2).det = 0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hS0)
  rw [complementary_logarithmicCoreFromMoments_eq] at hcore
  exact hcore

/-- Moment-level version of `ComplementaryFractionCoreDetZero`.

Here `S0=phi`, `S1=X phi'`, and `S2=X d/dX (X phi')`, all embedded in the
fraction field of `K[X]`. -/
def ComplementaryFractionMomentDetZero
    {K : Type*} [Field K]
    (phi : Polynomial K) (a1 a2 b1 b2 h k M : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let S0 := ι phi
  let S1 := ι (eulerDerivative phi)
  let S2 := ι (eulerDerivative (eulerDerivative phi))
  (lineMomentHessian
      (complementaryLogBaseExponent
        (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
        (ι (Polynomial.C k)) (ι (Polynomial.C M)))
      (complementaryLogDirection
        (ι (Polynomial.C a1)) (ι (Polynomial.C a2))
        (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
        (ι (Polynomial.C h)) (ι (Polynomial.C k)))
      S0 S1 S2).det = 0

/-- The moment-level zero determinant gives exactly the Phase 71 fraction-field
core determinant. -/
theorem complementary_fraction_core_det_zero_of_moment_det_zero
    {K : Type*} [Field K]
    {phi : Polynomial K} {a1 a2 b1 b2 h k M : K}
    (hphi : phi ≠ 0)
    (hdet : ComplementaryFractionMomentDetZero
      phi a1 a2 b1 b2 h k M) :
    ComplementaryFractionCoreDetZero phi a1 a2 b1 b2 h k M := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let S0 : F := ι phi
  let S1 : F := ι (eulerDerivative phi)
  let S2 : F := ι (eulerDerivative (eulerDerivative phi))
  have hS0 : S0 ≠ 0 := by
    dsimp [S0]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr hphi
  have hmoment :
      (lineMomentHessian
        (complementaryLogBaseExponent
          (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
          (ι (Polynomial.C k)) (ι (Polynomial.C M)))
        (complementaryLogDirection
          (ι (Polynomial.C a1)) (ι (Polynomial.C a2))
          (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
          (ι (Polynomial.C h)) (ι (Polynomial.C k)))
        S0 S1 S2).det = 0 := by
    simpa [ComplementaryFractionMomentDetZero, F, ι, S0, S1, S2] using hdet
  have hcore :=
    complementary_core_det_zero_of_lineMoment_det_zero
      (K := F)
      (a1 := ι (Polynomial.C a1)) (a2 := ι (Polynomial.C a2))
      (b1 := ι (Polynomial.C b1)) (b2 := ι (Polynomial.C b2))
      (h := ι (Polynomial.C h)) (k := ι (Polynomial.C k))
      (M := ι (Polynomial.C M))
      (S0 := S0) (S1 := S1) (S2 := S2)
      hS0 hmoment
  have hA :
      ι (logarithmicEtaNumerator phi) = S2 * S0 - S1^2 := by
    dsimp [S0, S1, S2]
    simp [logarithmicEtaNumerator, map_sub, map_mul, map_pow]
  unfold ComplementaryFractionCoreDetZero
  simpa [F, ι, S0, S1, S2, hA] using hcore

/-- End-to-end contradiction from the line-moment Hessian determinant for a
genuine complementary local term.  The only remaining upstream step is to
identify this moment matrix with the diagonally-scaled Hessian of the actual
line-supported `MvPolynomial`. -/
theorem complementary_fraction_moment_local_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k m : ℕ}
    {c : K} {q : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hdet : ComplementaryFractionMomentDetZero
      (Polynomial.C c + Polynomial.X ^ m * q)
      (alpha1 : K) (alpha2 : K) (beta1 : K) (beta2 : K)
      (h : K) (k : K) (M : K)) : False := by
  let phi : Polynomial K := Polynomial.C c + Polynomial.X ^ m * q
  have hphi : phi ≠ 0 := by
    intro hz
    have hz0 := congrArg (Polynomial.eval 0) hz
    apply hc
    simpa [phi, Nat.ne_of_gt hm] using hz0
  have hcore :=
    complementary_fraction_core_det_zero_of_moment_det_zero
      (K := K) hphi (by simpa [phi] using hdet)
  exact complementary_fraction_core_local_impossible
    (K := K) ha1 ha2 hb1 hb2 hM hh hk hm hc hq0
    (by simpa [phi] using hcore)

end

end HC4.Polynomial
