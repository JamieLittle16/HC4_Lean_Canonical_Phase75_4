import HC4.Polynomial.RationalCharacteristicSymmetricPencil

/-!
# Lifted rank-one trace identity forces affine parameter polynomials

The lifted trace identity is represented as a polynomial in the
independent parameter T with transverse polynomial coefficients.
The parameter vector U is a ground-field polynomial vector (obtained
mathematically by clearing denominators of the parametrized derivative).

Differentiating coefficientwise in the transverse variables gives a
symmetric Hessian pencil. Taking each transverse monomial coefficient
and using symmetric pencil rigidity forces both Hessians to vanish.

The lift of the trace identity from a reduced rational parameter and
the existence of such a parametrization are separate obligations.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev T (K : Type*) [Field K] := _root_.Polynomial (B K)

section Affine

variable [CharZero K]

/-- Vanishing Hessian gives a polynomial with constant first partials
and an explicit affine representation. -/
theorem transverse_affine_of_hessian_zero
    (p : B K) (hp : hessian p = 0) :
    p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j := by
  classical
  have hconst (j : Fin 3) : pderiv j p = MvPolynomial.C ((pderiv j p).coeff 0) := by
    apply transverse_eq_C_of_all_pderiv_zero
    intro i
    exact congrArg (fun H : Matrix (Fin 3) (Fin 3) (B K) => H j i) hp
  let l : B K := ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j
  have hl (i : Fin 3) : pderiv i l = MvPolynomial.C ((pderiv i p).coeff 0) := by
    unfold l
    rw [map_sum]
    simp only [MvPolynomial.pderiv_C_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne hj, mul_zero]
    · simp
  have hdiff : ∀ i : Fin 3, pderiv i (p - l) = 0 := by
    intro i
    rw [map_sub, hl]
    exact sub_eq_zero.mpr (hconst i)
  have hc := transverse_eq_C_of_all_pderiv_zero (p - l) hdiff
  have hl0 : l.coeff 0 = 0 := by
    simp only [l, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_zero_X, mul_zero, Finset.sum_const_zero]
  have hd0 : (p - l).coeff 0 = p.coeff 0 := by
    rw [MvPolynomial.coeff_sub, hl0, sub_zero]
  rw [hd0] at hc
  exact sub_eq_iff_eq_add.mp hc

end Affine

/-- The transverse coefficient of a product by a scalar is the
corresponding scalar multiple of the coefficient. -/
private theorem transverse_coeff_mul_C
    (p : B K) (c : K) (m : Fin 3 →₀ ℕ) :
    (p * MvPolynomial.C c).coeff m = p.coeff m * c := by
  rw [mul_comm, MvPolynomial.coeff_C_mul, mul_comm]

/-- Each transverse monomial coefficient of the lifted trace identity
supplies the coefficient recurrence of a symmetric affine Hessian pencil. -/
theorem rankOne_hessians_zero_of_lifted_trace_independent
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (hlift : ∑ j : Fin 3,
      _root_.Polynomial.C (pderiv j p) *
        (U j).map (MvPolynomial.C : K →+* B K) =
      (_root_.Polynomial.X : T K) * ∑ j : Fin 3,
        _root_.Polynomial.C (pderiv j q) *
          (U j).map (MvPolynomial.C : K →+* B K))
    (hind : ∀ b : Fin 3 → K,
      (∑ j : Fin 3, _root_.Polynomial.C (b j) * U j) = 0 → b = 0) :
    hessian p = 0 ∧ hessian q = 0 := by
  classical
  let u : ℕ → Fin 3 → K := fun n j => (U j).coeff n
  have hspan (b : Fin 3 → K) (hb : ∀ n : ℕ, b ⬝ᵥ u n = 0) : b = 0 := by
    apply hind
    apply _root_.Polynomial.ext
    intro n
    simp only [_root_.Polynomial.finset_sum_coeff, _root_.Polynomial.coeff_C_mul,
      _root_.Polynomial.coeff_zero]
    exact hb n
  have hzero : (∑ j : Fin 3, pderiv j p * MvPolynomial.C (u 0 j)) = 0 := by
    have h := congrArg (fun f : T K => f.coeff 0) hlift
    change (∑ j : Fin 3, _root_.Polynomial.C (pderiv j p) *
      (U j).map (MvPolynomial.C : K →+* B K)).coeff 0 =
      ((_root_.Polynomial.X : T K) * ∑ j : Fin 3,
        _root_.Polynomial.C (pderiv j q) *
          (U j).map (MvPolynomial.C : K →+* B K)).coeff 0 at h
    simpa only [_root_.Polynomial.finset_sum_coeff, _root_.Polynomial.coeff_C_mul,
      _root_.Polynomial.coeff_map, _root_.Polynomial.coeff_X_mul_zero, u] using h
  have hstep (n : ℕ) :
      (∑ j : Fin 3, pderiv j p * MvPolynomial.C (u (n + 1) j)) =
        ∑ j : Fin 3, pderiv j q * MvPolynomial.C (u n j) := by
    have h := congrArg (fun f : T K => f.coeff (n + 1)) hlift
    change (∑ j : Fin 3, _root_.Polynomial.C (pderiv j p) *
      (U j).map (MvPolynomial.C : K →+* B K)).coeff (n + 1) =
      ((_root_.Polynomial.X : T K) * ∑ j : Fin 3,
        _root_.Polynomial.C (pderiv j q) *
          (U j).map (MvPolynomial.C : K →+* B K)).coeff (n + 1) at h
    simpa only [_root_.Polynomial.coeff_X_mul, _root_.Polynomial.finset_sum_coeff,
      _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_map, u] using h
  have hDzero (i : Fin 3) :
      (∑ j : Fin 3, hessian p i j * MvPolynomial.C (u 0 j)) = 0 := by
    have h := congrArg (pderiv i : Derivation K (B K) (B K)) hzero
    simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul, pderiv_C,
      mul_zero, zero_add] at h
    simpa only [hessian_apply, HC4.Newton.pderiv_comm_backport i, mul_comm] using h
  have hDstep (i : Fin 3) (n : ℕ) :
      (∑ j : Fin 3, hessian p i j * MvPolynomial.C (u (n + 1) j)) =
        ∑ j : Fin 3, hessian q i j * MvPolynomial.C (u n j) := by
    have h := congrArg (pderiv i : Derivation K (B K) (B K)) (hstep n)
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, pderiv_C,
      mul_zero, zero_add] at h
    simpa only [hessian_apply, HC4.Newton.pderiv_comm_backport i, mul_comm] using h
  have hcoeff (m : Fin 3 →₀ ℕ) :
      (fun i j => (hessian p i j).coeff m : Matrix (Fin 3) (Fin 3) K) = 0 ∧
      (fun i j => (hessian q i j).coeff m : Matrix (Fin 3) (Fin 3) K) = 0 := by
    let A : Matrix (Fin 3) (Fin 3) K := fun i j => (hessian p i j).coeff m
    let D : Matrix (Fin 3) (Fin 3) K := fun i j => (hessian q i j).coeff m
    have hA : A.transpose = A := by
      apply Matrix.ext
      intro i j
      simp only [A, Matrix.transpose_apply, hessian_apply]
      rw [HC4.Newton.pderiv_comm_backport]
    have hD : D.transpose = D := by
      apply Matrix.ext
      intro i j
      simp only [D, Matrix.transpose_apply, hessian_apply]
      rw [HC4.Newton.pderiv_comm_backport]
    apply symmetric_affinePencil_eq_zero_of_coefficientRecurrence A D hA hD u
    · funext i
      have h := congrArg (MvPolynomial.coeff m) (hDzero i)
      change (∑ j : Fin 3, hessian p i j * MvPolynomial.C (u 0 j)).coeff m =
        (0 : B K).coeff m at h
      simpa only [MvPolynomial.coeff_sum, transverse_coeff_mul_C, MvPolynomial.coeff_zero,
        Matrix.mulVec, dotProduct, A, Pi.zero_apply] using h
    · intro n
      funext i
      have h := congrArg (MvPolynomial.coeff m) (hDstep i n)
      change (∑ j : Fin 3, hessian p i j * MvPolynomial.C (u (n + 1) j)).coeff m =
        (∑ j : Fin 3, hessian q i j * MvPolynomial.C (u n j)).coeff m at h
      simpa only [MvPolynomial.coeff_sum, transverse_coeff_mul_C, Matrix.mulVec, dotProduct, A, D] using h
    · exact hspan
  constructor
  · apply Matrix.ext
    intro i j
    apply MvPolynomial.ext
    intro m
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) (hcoeff m).1
    simpa only [Matrix.zero_apply, MvPolynomial.coeff_zero] using h
  · apply Matrix.ext
    intro i j
    apply MvPolynomial.ext
    intro m
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) (hcoeff m).2
    simpa only [Matrix.zero_apply, MvPolynomial.coeff_zero] using h

variable [CharZero K]

/-- The lifted rank-one trace identity forces both parameter
polynomials to be affine in the absence of a constant relation on U. -/
theorem rankOne_affine_parameters_of_lifted_trace_independent
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (hlift : ∑ j : Fin 3,
      _root_.Polynomial.C (pderiv j p) *
        (U j).map (MvPolynomial.C : K →+* B K) =
      (_root_.Polynomial.X : T K) * ∑ j : Fin 3,
        _root_.Polynomial.C (pderiv j q) *
          (U j).map (MvPolynomial.C : K →+* B K))
    (hind : ∀ b : Fin 3 → K,
      (∑ j : Fin 3, _root_.Polynomial.C (b j) * U j) = 0 → b = 0) :
    (p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j) ∧
    (q = MvPolynomial.C (q.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j q).coeff 0) * X j) := by
  obtain ⟨hp, hq⟩ := rankOne_hessians_zero_of_lifted_trace_independent p q U hlift hind
  exact ⟨transverse_affine_of_hessian_zero p hp, transverse_affine_of_hessian_zero q hq⟩

end
end HC4.Polynomial.RankThreeCubic
