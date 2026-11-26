import HC4.Polynomial.RationalCharacteristicRankOneNormalizedClosure

/-!
# Nilpotent normalized rank-one polynomial factors

The trace relation of the normalized rank-one factorization follows
from cube-zero, including a nonzero common scalar. Evaluation at
x/y is injective on ground-field parameter polynomials, as follows
from the verified polynomial chart descent. Scaling the operator
does not change self-adjointness. Therefore independent polynomial
parameter components are impossible without assuming a trace identity.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section MatrixAlgebra

variable {F ι : Type*} [Field F] [Fintype ι]

/-- Squaring a rank-one matrix multiplies it by the contraction
of its two factors. -/
theorem rankOne_mul_self_eq_smul
    (N : Matrix ι ι F) (u v : ι → F)
    (hN : ∀ i j, N i j = u i * v j) :
    N * N = (v ⬝ᵥ u) • N := by
  ext i j
  change (∑ k : ι, N i k * N k j) = (v ⬝ᵥ u) * N i j
  simp only [hN, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable [DecidableEq ι]

/-- A cube-zero rank-one matrix has zero contraction. The conclusion
also holds for a zero left factor, so no exact rank hypothesis is
needed. -/
theorem rankOne_dot_zero_of_cube_zero
    (N : Matrix ι ι F) (u v : ι → F)
    (hN : ∀ i j, N i j = u i * v j)
    (h3 : N ^ 3 = 0) (k : ι) (hk : v k ≠ 0) :
    v ⬝ᵥ u = 0 := by
  classical
  let a := v ⬝ᵥ u
  have hsq : N * N = a • N := rankOne_mul_self_eq_smul N u v hN
  have hcube : a • (a • N) = 0 := by
    rw [show N ^ 3 = (N * N) * N by simp only [pow_succ, pow_zero, one_mul],
      hsq, Matrix.smul_mul, hsq] at h3
    exact h3
  by_contra ha
  have hu : ∀ i : ι, u i = 0 := by
    intro i
    have h := congrArg (fun A : Matrix ι ι F => A i k) hcube
    change a * (a * N i k) = 0 at h
    rw [hN] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp
      ((mul_eq_zero.mp h).resolve_left ha)).resolve_left ha)).resolve_right hk
  apply ha
  change (∑ i : ι, v i * u i) = 0
  simp [hu]

end MatrixAlgebra

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)

/-- Evaluation at x/y has trivial kernel on scalar polynomials.
The bivariate chart map sends such a polynomial to its constant
image over the coefficient ring K[T]. -/
theorem rankOne_normalizedParameter_eval_zero
    (P : _root_.Polynomial K)
    (h : P.eval₂ (algebraMap K (E K)) rankOne_normalizedParameter = 0) :
    P = 0 := by
  have he : (P.map (MvPolynomial.C : K →+* B K)).eval₂
      (algebraMap (B K) (E K)) rankOne_normalizedParameter = 0 := by
    rw [rankOne_parameter_eval_map]
    exact h
  have hz := rankOne_normalizedChartTime_zero_of_eval_zero _ he
  have hc := congrArg (rankOne_bivariateChart (K := K)) hz
  rw [rankOne_bivariateChartTime_parameter, map_zero] at hc
  have hcoeff := congrArg (MvPolynomial.coeff (0 : Fin 2 →₀ ℕ)) hc
  simpa [MvPolynomial.coeff] using hcoeff

/-- Cube-zero supplies the polynomial trace relation after clearing
a common nonzero scalar from the normalized factorization. -/
theorem rankOne_normalized_trace_of_cube_zero
    (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K) (s : E K) (hs : s ≠ 0)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j)
    (h3 : N ^ 3 = 0) :
    U 0 = _root_.Polynomial.X * U 1 := by
  let u : Fin 3 → E K := fun i =>
    s * (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter
  have h := rankOne_dot_zero_of_cube_zero N u rankOne_normalizedRow
    hN h3 (0 : Fin 3) (by simp [rankOne_normalizedRow])
  change (∑ i : Fin 3, rankOne_normalizedRow i * u i) = 0 at h
  simp [Fin.sum_univ_three, rankOne_normalizedRow, u] at h
  have he : s * ((U 0).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter -
      rankOne_normalizedParameter *
        (U 1).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter) = 0 := by
    linear_combination h
  have hz := (mul_eq_zero.mp he).resolve_left hs
  apply sub_eq_zero.mp
  apply rankOne_normalizedParameter_eval_zero
  rw [_root_.Polynomial.eval₂_sub, _root_.Polynomial.eval₂_mul,
    _root_.Polynomial.eval₂_X]
  exact hz

variable [CharZero K]

/-- A nonzero scalar multiple of a polynomial parameter factorization
cannot have independent components if it is cube-zero and
self-adjoint for a regular source Hessian. -/
theorem rankOne_normalized_scaled_independent_impossible
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K) (s : E K) (hs : s ≠ 0)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j)
    (h3 : N ^ 3 = 0)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N)
    (hind : ∀ a b c : K,
      _root_.Polynomial.C a * U 0 + _root_.Polynomial.C b * U 1 +
        _root_.Polynomial.C c * U 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hreg : (hessian f).det ≠ 0) : False := by
  let M : Matrix (Fin 3) (Fin 3) (E K) := fun i j =>
    (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
      rankOne_normalizedRow j
  let H := (hessian f).map (algebraMap (B K) (E K))
  have hscale : N = s • M := by
    ext i j
    change N i j = s * M i j
    rw [hN]
    dsimp [M]
    ring
  have hself' : (s • M.transpose) * H = H * (s • M) := by
    rw [hscale] at hself
    exact hself
  rw [Matrix.smul_mul, Matrix.mul_smul] at hself'
  have hm : M.transpose * H = H * M := by
    ext i j
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) (E K) => A i j) hself'
    change s * (M.transpose * H) i j = s * (H * M) i j at h
    exact mul_left_cancel₀ hs h
  exact rankOne_normalized_independent_impossible f M U (fun _ _ => rfl)
    hm (rankOne_normalized_trace_of_cube_zero N U s hs hN h3) hind hreg

end
end HC4.Polynomial.RankThreeCubic
