import HC4.Polynomial.AutonomousODETranslation
import Mathlib.Tactic

/-!
# A18.5.28: the root factorisation required by the Phase-79 degree bound

Phase 80 transports a polynomial autonomous ODE to a nonzero root, but leaves
the standard multiplicity factorisation

    translatePolynomial alpha phi = X^(n+1) * q,
    q(0) != 0

to the caller.  For the rank-three edge this datum is automatic: `phi` is
nonconstant, the coefficient field is algebraically closed, and the constant
coefficient of `phi` is nonzero.

This file closes that small seam once and for all.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Translating by `alpha` and then by `-alpha` is the identity. -/
theorem translatePolynomial_neg_comp
    (alpha : K) (p : Polynomial K) :
    translatePolynomial (-alpha) (translatePolynomial alpha p) = p := by
  unfold translatePolynomial
  rw [Polynomial.comp_assoc]
  have hinner :
      (Polynomial.X + Polynomial.C alpha).comp
          (Polynomial.X + Polynomial.C (-alpha)) =
        (Polynomial.X : Polynomial K) := by
    simp
  rw [hinner]
  simp

/-- Translation by a scalar is injective. -/
theorem translatePolynomial_injective (alpha : K) :
    Function.Injective (translatePolynomial alpha : Polynomial K → Polynomial K) := by
  intro p q h
  have h' := congrArg (translatePolynomial (-alpha)) h
  simpa [translatePolynomial_neg_comp] using h'

/-- A nonconstant polynomial with nonzero constant coefficient has a nonzero
root, and translation to that root has the exact positive multiplicity
factorisation consumed by Phase 80. -/
theorem exists_nonzero_root_multiplicity_factorisation
    {phi : Polynomial K}
    (hdeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0) :
    ∃ alpha : K, ∃ n : ℕ, ∃ q : Polynomial K,
      alpha ≠ 0 ∧ q.coeff 0 ≠ 0 ∧
        translatePolynomial alpha phi = Polynomial.X ^ (n + 1) * q := by
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hdeg
  have hdegree : phi.degree ≠ 0 := by
    intro hz
    have hconst : phi = Polynomial.C (phi.coeff 0) :=
      Polynomial.eq_C_of_degree_eq_zero hz
    rw [hconst] at hdeg
    simp at hdeg
  obtain ⟨alpha, hroot⟩ := IsAlgClosed.exists_root phi hdegree
  have halpha : alpha ≠ 0 := by
    intro hz
    subst alpha
    have : phi.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa using hroot
    exact hphi0 this

  let p := translatePolynomial alpha phi
  have hp : p ≠ 0 := by
    intro hp0
    apply hphi
    have hback := congrArg (translatePolynomial (-alpha)) hp0
    simpa [p, translatePolynomial_neg_comp] using hback
  have hp0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    dsimp [p, translatePolynomial]
    simpa using hroot

  let t := p.natTrailingDegree
  have ht0 : t ≠ 0 :=
    (Polynomial.natTrailingDegree_ne_zero).2 ⟨hp, hp0⟩
  have htpos : 0 < t := Nat.pos_of_ne_zero ht0
  have hdiv : Polynomial.X ^ t ∣ p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  rcases hdiv with ⟨q, hq⟩
  have hpt : p.coeff t ≠ 0 :=
    (Polynomial.coeff_natTrailingDegree_ne_zero).2 hp
  have hq0 : q.coeff 0 ≠ 0 := by
    rw [hq] at hpt
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, if_true,
      Nat.sub_self] using hpt

  let n := t - 1
  have htn : t = n + 1 := by
    dsimp [n]
    omega
  refine ⟨alpha, n, q, halpha, hq0, ?_⟩
  dsimp [p] at hq ⊢
  rw [← htn]
  exact hq

end

end HC4.Polynomial
