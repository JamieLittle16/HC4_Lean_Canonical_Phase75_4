import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# Locked-binomial first-variation Euler rigidity

The first positive layer of the singular planar-contact Rees is supported on
one fixed quotient fibre.  Linearising the Hessian determinant around the
locked two-monomial special fibre produces, after the harmless affine
normalisation of the locked linear factor, the Euler equation

    E(E phi) + (1 - 2k) E(phi) + k(k-1) phi = 0,

where `E(phi) = X * phi'` and `k` is the pair degree of the first departing
fibre.

Coefficientwise the operator is diagonal:

    [X^n] = (n-k)(n-(k-1)) * phi_n.

Hence in characteristic zero every polynomial solution is supported only in
degrees `k-1` and `k`.  This is the exact state-free rigidity statement needed
before returning to the source-honest A19 carrier.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Canonical Euler operator arising from the first variation about the locked
binomial after sending its nonconstant linear factor to `X`. -/
def lockedBinomialFirstVariationEulerResidual
    (k : ℕ) (phi : Polynomial K) : Polynomial K :=
  eulerDerivative (eulerDerivative phi) +
    Polynomial.C (1 - 2 * (k : K)) * eulerDerivative phi +
    Polynomial.C ((k : K) * ((k : K) - 1)) * phi

/-- The locked-binomial first-variation operator is diagonal on monomials. -/
@[simp] theorem coeff_lockedBinomialFirstVariationEulerResidual
    (k n : ℕ) (phi : Polynomial K) :
    (lockedBinomialFirstVariationEulerResidual k phi).coeff n =
      ((n : K) - (k : K)) *
        ((n : K) - ((k : K) - 1)) * phi.coeff n := by
  unfold lockedBinomialFirstVariationEulerResidual
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coeff_eulerDerivative]
  ring

/-- A nonzero coefficient of a polynomial solution can occur only at one of
the two adjacent indicial roots `k-1` and `k`. -/
theorem support_index_eq_pred_or_eq_of_lockedBinomialFirstVariationEulerResidual_eq_zero
    (k : ℕ) (hk : 1 ≤ k) (phi : Polynomial K)
    (hres : lockedBinomialFirstVariationEulerResidual k phi = 0)
    {n : ℕ} (hn : n ∈ phi.support) :
    n = k - 1 ∨ n = k := by
  have hcoeff : phi.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hz :
      (lockedBinomialFirstVariationEulerResidual k phi).coeff n = 0 := by
    rw [hres]
    rfl
  rw [coeff_lockedBinomialFirstVariationEulerResidual] at hz
  have hroot :
      ((n : K) - (k : K)) *
          ((n : K) - ((k : K) - 1)) = 0 :=
    (mul_eq_zero.mp hz).resolve_right hcoeff
  rcases mul_eq_zero.mp hroot with hnk | hnkm
  · right
    have hcast : (n : K) = (k : K) := sub_eq_zero.mp hnk
    exact_mod_cast hcast
  · left
    have heq : (n : K) = (k : K) - 1 := sub_eq_zero.mp hnkm
    have hpred : ((k - 1 : ℕ) : K) = (k : K) - 1 := by
      rw [Nat.cast_sub hk]
      norm_num
    rw [← hpred] at heq
    exact_mod_cast heq

/-- Finset form of the preceding coefficient classification. -/
theorem support_lockedBinomialFirstVariationEulerResidual_subset
    (k : ℕ) (hk : 1 ≤ k) (phi : Polynomial K)
    (hres : lockedBinomialFirstVariationEulerResidual k phi = 0) :
    phi.support ⊆ {k - 1, k} := by
  intro n hn
  rcases
      support_index_eq_pred_or_eq_of_lockedBinomialFirstVariationEulerResidual_eq_zero
        k hk phi hres hn with hpred | hk'
  · simp [hpred]
  · simp [hk']

/-- Explicit two-term normal form of every polynomial solution. -/
theorem eq_two_adjacent_terms_of_lockedBinomialFirstVariationEulerResidual_eq_zero
    (k : ℕ) (hk : 1 ≤ k) (phi : Polynomial K)
    (hres : lockedBinomialFirstVariationEulerResidual k phi = 0) :
    phi =
      Polynomial.C (phi.coeff (k - 1)) * Polynomial.X ^ (k - 1) +
        Polynomial.C (phi.coeff k) * Polynomial.X ^ k := by
  apply Polynomial.ext
  intro n
  by_cases hpred : n = k - 1
  · subst n
    by_cases hkpred : k = k - 1
    · omega
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hkpred]
  by_cases hkeq : n = k
  · subst n
    have hne : k ≠ k - 1 := by omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  have hnnot : n ∉ phi.support := by
    intro hn
    have hc :=
      support_index_eq_pred_or_eq_of_lockedBinomialFirstVariationEulerResidual_eq_zero
        k hk phi hres hn
    exact hc.elim hpred hkeq
  have hnzero : phi.coeff n = 0 := by
    simpa [Polynomial.mem_support_iff] using hnnot
  rw [hnzero]
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hpred, hkeq,
    Ne.symm hpred, Ne.symm hkeq]

end

end HC4.Polynomial
