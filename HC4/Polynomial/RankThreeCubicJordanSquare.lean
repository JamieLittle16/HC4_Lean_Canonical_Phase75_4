import HC4.Polynomial.RankThreeCubicCharacteristics
import HC4.Polynomial.DerivativeWeight
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Reference square in the nilpotent Jordan charts

The stationary reference cubic in the polynomial-characteristic branch
has a square partial derivative in either nonzero nilpotent Jordan chart.
This module checks the extraction on the actual homogeneous cubic.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section


/-- In the linear-characteristic chart, the coefficient of time in the
Jacobian transport equation makes the velocity self-adjoint against the
reference Hessian. -/
theorem selfAdjoint_of_linearCharacteristic
    {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (_root_.Polynomial A)) (M N : Matrix ι ι A)
    (hs : ∀ i j, H i j = H j i)
    (h : H * (1 + (_root_.Polynomial.X : _root_.Polynomial A) •
      N.map _root_.Polynomial.C) = M.map _root_.Polynomial.C) :
    ∀ i j, (M * N) i j = (M * N) j i := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h
  have hz (i j) : (H i j).coeff 0 = M i j := by
    have h0 := congrArg (fun T : Matrix ι ι (_root_.Polynomial A) => (T i j).coeff 0) h
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_X_mul_zero, add_zero,
      _root_.Polynomial.coeff_C_zero] using h0
  have hcoef (i j) : (H i j).coeff 1 + (M * N) i j = 0 := by
    have h1 := congrArg (fun T : Matrix ι ι (_root_.Polynomial A) => (T i j).coeff 1) h
    change (H i j + _root_.Polynomial.X * (H * N.map _root_.Polynomial.C) i j).coeff (0 + 1)
        = (_root_.Polynomial.C (M i j)).coeff (0 + 1) at h1
    rw [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_C] at h1
    simpa [Matrix.mul_apply, _root_.Polynomial.finset_sum_coeff,
      _root_.Polynomial.coeff_mul_C, hz] using h1
  intro i j
  have h₁ := hcoef i j
  have h₂ := hcoef j i
  rw [hs i j] at h₁
  exact add_left_cancel (h₁.trans h₂.symm)

variable {K : Type*} [Field K] [CharZero K]

private theorem homogeneous_two_eq_single_coordinate_square
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 2) (j : Fin 3)
    (hpartials : ∀ i, i ≠ j → pderiv i q = 0) :
    q = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 2) q) * X j ^ 2 := by
  classical
  have he (m : Fin 3 →₀ ℕ) (hm : MvPolynomial.coeff m q ≠ 0) :
      m = Finsupp.single j 2 := by
    have hother (i : Fin 3) (hi : i ≠ j) : m i = 0 :=
      HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero i q (hpartials i hi) m hm
    have hw := hq hm
    change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) m = 2 at hw
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hw
    have hw' : (∑ x : Fin 3, m x) = 2 := by simpa using hw
    have hsum : (∑ x : Fin 3, m x) = m j := by
      apply Finset.sum_eq_single
      · exact fun i _ hi => hother i hi
      · simp
    rw [hsum] at hw'
    ext i
    by_cases hi : i = j
    · subst i
      simpa using hw'
    · simp [hi, hother i hi]
  have hmono : (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 2) q) : MvPolynomial (Fin 3) K)
      * X j ^ 2 = MvPolynomial.monomial (Finsupp.single j 2)
        (MvPolynomial.coeff (Finsupp.single j 2) q) := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  rw [hmono]
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = Finsupp.single j 2
  · simp [hm]
  · have hc : MvPolynomial.coeff m q = 0 := by by_contra h; exact hm (he m h)
    simp [MvPolynomial.coeff_monomial, Ne.symm hm, hc]

/-- The two nonzero nilpotent Jordan charts in dimension three. -/
def jordanVelocity (chain : Bool) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K) :=
  !![0, 1, 0; 0, 0, if chain then 1 else 0; 0, 0, 0]

/-- Self-adjointness of the characteristic velocity against the
reference Hessian produces the square in its fixed direction. -/
theorem reference_square_of_jordan_velocity
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    (hdet : (hessian q).det ≠ 0) (chain : Bool)
    (hs : ∀ i j : Fin 3, (hessian q * jordanVelocity (K := K) chain) i j =
      (hessian q * jordanVelocity (K := K) chain) j i) :
    ∃ c : K, c ≠ 0 ∧
      pderiv 0 q = MvPolynomial.C c * X (if chain then 2 else 1) ^ 2 := by
  let j : Fin 3 := if chain then 2 else 1
  have hrow : ∀ i : Fin 3, i ≠ j → pderiv i (pderiv 0 q) = 0 := by
    intro i hi
    have h00 := hs 0 1
    have h02 := hs 0 2
    have h12 := hs 1 2
    cases chain <;> fin_cases i <;>
      simp [j, jordanVelocity, Matrix.mul_apply, Fin.sum_univ_three] at hi h00 h02 h12 ⊢
    · exact h00
    · rw [HC4.Newton.pderiv_comm_backport]
      exact h12.symm
    · exact h00
    · exact h02
  have hsquare := homogeneous_two_eq_single_coordinate_square
    (pderiv 0 q) (hq.pderiv (i := 0)) j hrow
  let c := MvPolynomial.coeff (Finsupp.single j 2) (pderiv 0 q)
  have hc : c ≠ 0 := by
    intro hc0
    have hz : pderiv 0 q = 0 := by
      rw [hsquare]
      change MvPolynomial.C c * X j ^ 2 = 0
      simp [hc0]
    apply hdet
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro i
    simp [hessian_apply, hz]
  exact ⟨c, hc, hsquare⟩

/-- In a constant Jordan chart the affine characteristic substitution
is a triangular shear in the three transverse variables. -/
def jordanLineEval (a : K) (chain : Bool) :
    MvPolynomial (Unit ⊕ Fin 3) K →ₐ[K] _root_.Polynomial (MvPolynomial (Fin 3) K) :=
  lineEval (Sum.elim (fun _ => MvPolynomial.C a) X)
    (Sum.elim (fun _ => 1) ![X 1, if chain then X 2 else 0, 0])

theorem jordanLineEval_injective (a : K) (chain : Bool) :
    Function.Injective (jordanLineEval a chain : MvPolynomial (Unit ⊕ Fin 3) K →
      _root_.Polynomial (MvPolynomial (Fin 3) K)) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro b
  let t := b (.inl ()) - a
  let z₁ := b (.inr 1) - t * (if chain then b (.inr 2) else 0)
  let z : Fin 3 → K := ![b (.inr 0) - t * z₁, z₁, b (.inr 2)]
  let B := MvPolynomial (Fin 3) K
  let e : B →ₐ[K] K := MvPolynomial.aeval z
  let ev : _root_.Polynomial B →ₐ[K] K :=
    e.comp ((_root_.Polynomial.aeval (MvPolynomial.C t) :
      _root_.Polynomial B →ₐ[B] B).restrictScalars K)
  have h : ev.comp (jordanLineEval a chain) = MvPolynomial.aeval b := by
    ext i
    have hc (v : K) : e (MvPolynomial.C v) = v := e.commutes v
    have hx (j : Fin 3) : e (X j) = z j := MvPolynomial.aeval_X z j
    have heval (r s : B) :
        ev (_root_.Polynomial.C r + _root_.Polynomial.C s * _root_.Polynomial.X) =
          e r + e s * t := by
      change e (_root_.Polynomial.eval (MvPolynomial.C t)
        (_root_.Polynomial.C r + _root_.Polynomial.C s * _root_.Polynomial.X)) = _
      rw [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
        map_add, map_mul, hc]
    have hJ (j : Unit ⊕ Fin 3) : jordanLineEval a chain (X j) =
        _root_.Polynomial.C (Sum.elim (fun _ : Unit => MvPolynomial.C a) X j) +
        _root_.Polynomial.C
          (Sum.elim (fun _ : Unit => (1 : B)) ![X 1, if chain then X 2 else 0, 0] j) *
          _root_.Polynomial.X :=
      MvPolynomial.aeval_X _ j
    have hform (j) : ev (jordanLineEval a chain (X j)) = b j := by
      rw [hJ, heval]
      cases j with
      | inl j => cases j; simp [hc, t]
      | inr j =>
        cases chain <;> fin_cases j <;>
          simp [hx, z, z₁, t] <;> ring
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hform i
  have he := congrArg ev hpq
  change (ev.comp (jordanLineEval a chain)) p = (ev.comp (jordanLineEval a chain)) q at he
  rw [h] at he
  exact he

/-- The square in the reference cubic transfers back to the source in
either constant Jordan chart. The transport equation is the fibre
component of the straight characteristic identity. -/
theorem source_square_of_jordan_transport
    (a : K) (chain : Bool) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    (hdet : (hessian q).det ≠ 0)
    (hs : ∀ i j : Fin 3, (hessian q * jordanVelocity (K := K) chain) i j =
      (hessian q * jordanVelocity (K := K) chain) j i)
    (htransport : jordanLineEval a chain (pderiv (.inr 0) L) =
      _root_.Polynomial.C (pderiv 0 q)) :
    ∃ c : K, c ≠ 0 ∧ pderiv (.inr 0) L =
      MvPolynomial.C c * X (.inr (if chain then 2 else 1)) ^ 2 := by
  obtain ⟨c, hc, hsq⟩ := reference_square_of_jordan_velocity q hq hdet chain hs
  refine ⟨c, hc, jordanLineEval_injective a chain ?_⟩
  rw [htransport, hsq]
  cases chain <;>
    simp [jordanLineEval, lineEval, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (_root_.Polynomial (MvPolynomial (Fin 3) K)), _root_.Polynomial.algebraMap_eq]

end

end HC4.Polynomial.RankThreeCubic
