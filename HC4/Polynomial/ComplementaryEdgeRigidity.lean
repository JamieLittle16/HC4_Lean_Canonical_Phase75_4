import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Complementary-edge rigidity in endpoint form

Phase 74.5 proves the end-to-end contradiction once the one-variable edge
polynomial has been written in local form

  `C c + X^m * q`, with `m > 0`, `c ≠ 0`, and `q.coeff 0 ≠ 0`.

This file removes that normal-form hypothesis.  The tail

  `r = phi - C (phi.coeff 0)`

has positive `natTrailingDegree` whenever `phi` is nonconstant.  Hence `X^m`
divides `r`, with a quotient whose constant coefficient is nonzero.  This
feeds directly into the Phase-74.5 theorem.

The final endpoint theorem assumes the two endpoint coefficients are nonzero,
matching the complementary-edge statement used in the manuscript.
-/

namespace HC4.Polynomial

noncomputable section

/-- Every nonconstant polynomial can be written as its constant term plus a
positive power of `X` times a polynomial with nonzero constant coefficient.
The exponent is canonically the natural trailing degree of the nonconstant
tail. -/
theorem exists_positive_tail_factorisation
    {K : Type*} [Field K]
    {phi : Polynomial K}
    (hnonconstant : phi ≠ Polynomial.C (phi.coeff 0)) :
    ∃ m : ℕ, ∃ q : Polynomial K,
      0 < m ∧ q.coeff 0 ≠ 0 ∧
        phi = Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q := by
  let r : Polynomial K := phi - Polynomial.C (phi.coeff 0)
  have hr0 : r.coeff 0 = 0 := by
    simp [r]
  have hr : r ≠ 0 := by
    intro hrz
    apply hnonconstant
    dsimp [r] at hrz
    exact sub_eq_zero.mp hrz
  let m : ℕ := r.natTrailingDegree
  have hm : 0 < m := by
    exact Nat.pos_of_ne_zero ((Polynomial.natTrailingDegree_ne_zero).2 ⟨hr, hr0⟩)
  have hdiv : Polynomial.X ^ m ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  rcases hdiv with ⟨q, hq⟩
  have hrm : r.coeff m ≠ 0 := by
    exact (Polynomial.coeff_natTrailingDegree_ne_zero).2 hr
  have hq0 : q.coeff 0 ≠ 0 := by
    rw [hq] at hrm
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, if_true, Nat.sub_self] using hrm
  refine ⟨m, q, hm, hq0, ?_⟩
  calc
    phi = Polynomial.C (phi.coeff 0) + r := by
      dsimp [r]
      ring
    _ = Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q := by
      rw [hq]

/-- A nonzero coefficient at a positive exponent rules out constancy. -/
theorem nonconstant_of_positive_coeff_ne_zero
    {K : Type*} [Field K]
    {phi : Polynomial K} {M : ℕ}
    (hM : 0 < M) (hphiM : phi.coeff M ≠ 0) :
    phi ≠ Polynomial.C (phi.coeff 0) := by
  intro hconst
  apply hphiM
  calc
    phi.coeff M = (Polynomial.C (phi.coeff 0)).coeff M :=
      congrArg (fun p : Polynomial K => p.coeff M) hconst
    _ = 0 := by
      rw [Polynomial.coeff_C]
      simp [Nat.ne_of_gt hM]

/-- Complementary-edge rigidity with an abstract nonconstancy hypothesis.
This removes the local-form assumption from Phase 74.5. -/
theorem complementary_line_hessian_impossible_of_nonconstant
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k : ℕ}
    {phi : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hnonconstant : phi ≠ Polynomial.C (phi.coeff 0))
    (hdeg : phi.natDegree ≤ M)
    (hdet : hessianDeterminant
      (complementaryLinePolynomial
        alpha1 alpha2 beta1 beta2 h k M phi) = 0) : False := by
  rcases exists_positive_tail_factorisation
      (K := K) (phi := phi) hnonconstant with ⟨m, q, hm, hq0, hphi⟩
  have hdeg' :
      (Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q).natDegree ≤ M := by
    rw [← hphi]
    exact hdeg
  have hdet' : hessianDeterminant
      (complementaryLinePolynomial alpha1 alpha2 beta1 beta2 h k M
        (Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q)) = 0 := by
    rw [← hphi]
    exact hdet
  exact complementary_line_hessian_local_impossible
    (K := K)
    ha1 ha2 hb1 hb2 hM hh hk hm hphi0 hq0 hdeg' hdet'

/-- Manuscript-style complementary-edge rigidity.  If both endpoint
coefficients of `phi` are nonzero and its degree is at most `M`, then the
honest complementary line polynomial cannot have identically zero Hessian
determinant. -/
theorem complementary_line_hessian_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k : ℕ}
    {phi : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hphiM : phi.coeff M ≠ 0)
    (hdeg : phi.natDegree ≤ M)
    (hdet : hessianDeterminant
      (complementaryLinePolynomial
        alpha1 alpha2 beta1 beta2 h k M phi) = 0) : False := by
  have hnonconstant : phi ≠ Polynomial.C (phi.coeff 0) :=
    nonconstant_of_positive_coeff_ne_zero (K := K) hM hphiM
  exact complementary_line_hessian_impossible_of_nonconstant
    (K := K)
    ha1 ha2 hb1 hb2 hM hh hk hphi0 hnonconstant hdeg hdet

end

end HC4.Polynomial
