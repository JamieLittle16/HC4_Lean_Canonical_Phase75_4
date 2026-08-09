import HC4.Valuation.ParameterRamification
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# Common parameter factor and strict defect restart

The zero-kernel-slope Smith branch has a cleaner escape mechanism than an
abstract "choose a pole-minimal representative" assumption.

After denominator clearing and an integral Smith conformal move, a strict
improvement raises every normalised coefficient valuation.  In the integral
polynomial model this means that every source coefficient acquires a common
factor of the parameter `tau`.

In four source variables, factoring one common `tau` from the potential
removes exactly four powers of `tau` from the Hessian determinant:

    P = tau * Q
      ==> det Hess(P) = tau^4 * det Hess(Q).

This file formalises that operation without polynomial division.  The
quotient family is reconstructed coefficientwise from divisibility.

We prove:

* exact coefficient reconstruction;
* `P = C(tau^n) * Q` for a common factor `tau^n`;
* exact polynomial-family gradient collision survives common-factor
  extraction by cancellation;
* for one common factor, a pure Hessian defect `Delta` satisfies `4 <= Delta`;
* the quotient has exact defect `Delta - 4`;
* hence one common factor gives a strict `GlobalRestartProgress` step.

Thus a non-pole-minimal Smith separator can be turned into an ordinary
strict defect restart as soon as the next adapter proves that its transformed
family has one common parameter factor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]
variable {σ : Type*}

/-! ## Coefficientwise common-factor extraction -/

/-- Every nonzero source coefficient of `P` is divisible by `tau^n`. -/
def HasCommonParameterFactor
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    Polynomial.X ^ n ∣ MvPolynomial.coeff d P

/-- Chosen quotient coefficient after removing a common parameter factor. -/
noncomputable def commonParameterCoefficientQuotient
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    (d : σ →₀ ℕ) :
    Polynomial K := by
  classical
  exact
    if hd : d ∈ P.support then
      Classical.choose (hdiv d hd)
    else
      0

/-- Exact quotient relation on the original support. -/
theorem commonParameterCoefficientQuotient_spec_of_mem
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    {d : σ →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d P =
      Polynomial.X ^ n *
        commonParameterCoefficientQuotient
          n P hdiv d := by
  classical
  unfold commonParameterCoefficientQuotient
  rw [dif_pos hd]
  exact Classical.choose_spec (hdiv d hd)

/-- Explicit quotient family after extracting a common `tau^n`. -/
noncomputable def commonParameterFactorFamily
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P) :
    MvPolynomial σ (Polynomial K) :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (commonParameterCoefficientQuotient
        n P hdiv d)

/-- Exact coefficient formula for the reconstructed quotient. -/
theorem coeff_commonParameterFactorFamily_of_mem
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    {d : σ →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (commonParameterFactorFamily n P hdiv) =
      commonParameterCoefficientQuotient
        n P hdiv d := by
  classical
  unfold commonParameterFactorFamily
  simp [MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, hd]

theorem coeff_commonParameterFactorFamily_of_not_mem
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    {d : σ →₀ ℕ}
    (hd : d ∉ P.support) :
    MvPolynomial.coeff d
        (commonParameterFactorFamily n P hdiv) = 0 := by
  classical
  unfold commonParameterFactorFamily
  simp [MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, hd]

/-- The quotient introduces no new source monomials. -/
theorem support_commonParameterFactorFamily_subset
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P) :
    (commonParameterFactorFamily n P hdiv).support ⊆
      P.support := by
  intro d hd
  by_contra hnot
  have hzero :
      MvPolynomial.coeff d
          (commonParameterFactorFamily n P hdiv) = 0 :=
    coeff_commonParameterFactorFamily_of_not_mem
      n P hdiv hnot
  exact
    (MvPolynomial.mem_support_iff.mp hd) hzero

/-- Exact coefficientwise factorisation. -/
theorem commonParameterFactorFamily_coeff_factorisation
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    (d : σ →₀ ℕ) :
    MvPolynomial.coeff d P =
      Polynomial.X ^ n *
        MvPolynomial.coeff d
          (commonParameterFactorFamily n P hdiv) := by
  by_cases hd : d ∈ P.support
  · rw [coeff_commonParameterFactorFamily_of_mem
      n P hdiv hd]
    exact
      commonParameterCoefficientQuotient_spec_of_mem
        n P hdiv hd
  · have hP :
      MvPolynomial.coeff d P = 0 :=
    MvPolynomial.notMem_support_iff.mp hd
    rw [hP,
      coeff_commonParameterFactorFamily_of_not_mem
        n P hdiv hd]
    simp

/-- **Exact polynomial factorisation.**

The coefficientwise quotient really satisfies

    P = C(tau^n) * Q.
-/
theorem commonParameterFactorFamily_factorisation
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P) :
    P =
      MvPolynomial.C (Polynomial.X ^ n) *
        commonParameterFactorFamily n P hdiv := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_C_mul]
  exact
    commonParameterFactorFamily_coeff_factorisation
      n P hdiv d

/-! ## Collision covariance -/

/-- Exact family-gradient collision survives extraction of a nonzero common
parameter factor. -/
theorem polynomialFamilyExactGradientCollision_commonParameterFactor
    (n : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    (a b : σ → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (commonParameterFactorFamily n P hdiv)
      a b := by
  intro i
  let Q :=
    commonParameterFactorFamily n P hdiv
  have hfactor :
      P = MvPolynomial.C (Polynomial.X ^ n) * Q := by
    exact
      commonParameterFactorFamily_factorisation
        n P hdiv
  have hpd :=
    congrArg (MvPolynomial.pderiv i) hfactor
  have hpd' :
      MvPolynomial.pderiv i P =
        MvPolynomial.C (Polynomial.X ^ n) *
          MvPolynomial.pderiv i Q := by
    simpa [MvPolynomial.pderiv_C_mul] using hpd
  have ha :=
    congrArg (MvPolynomial.eval a) hpd'
  have hb :=
    congrArg (MvPolynomial.eval b) hpd'
  simp only [map_mul, MvPolynomial.eval_C] at ha hb
  apply polynomial_X_pow_mul_cancel
    (K := K) n
  calc
    Polynomial.X ^ n *
        MvPolynomial.eval a
          (MvPolynomial.pderiv i Q) =
      MvPolynomial.eval a
        (MvPolynomial.pderiv i P) := ha.symm
    _ =
      MvPolynomial.eval b
        (MvPolynomial.pderiv i P) := hcoll i
    _ =
      Polynomial.X ^ n *
        MvPolynomial.eval b
          (MvPolynomial.pderiv i Q) := hb

/-! ## Four-dimensional Hessian defect drop -/

section FinFour

/-- Factoring a single common parameter from a four-variable potential
forces at least four parameter powers in a pure Hessian determinant defect. -/
theorem four_le_defect_of_commonParameterFactor_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    4 ≤ Delta := by
  let Q :=
    commonParameterFactorFamily 1 P hdiv
  have hfactor :
      P =
        MvPolynomial.C Polynomial.X * Q := by
    simpa using
      commonParameterFactorFamily_factorisation
        (K := K) 1 P hdiv
  have hdet :=
    congrArg HC4.Polynomial.hessianDeterminant
      hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef] at hdet
  have hdvdMv :
      (MvPolynomial.C
          (Polynomial.X ^ 4) :
          MvPolynomial (Fin 4) (Polynomial K)) ∣
        MvPolynomial.C
          (Polynomial.X ^ Delta) := by
    refine
      ⟨HC4.Polynomial.hessianDeterminant Q, ?_⟩
    simpa [MvPolynomial.C_pow] using hdet
  have hdvdPoly :
      (Polynomial.X ^ 4 : Polynomial K) ∣
        Polynomial.X ^ Delta := by
    have hall :=
      (MvPolynomial.C_dvd_iff_dvd_coeff
        (Polynomial.X ^ 4)
        (MvPolynomial.C
          (Polynomial.X ^ Delta) :
          MvPolynomial (Fin 4) (Polynomial K))).mp
        hdvdMv
    simpa only [MvPolynomial.coeff_zero_C] using
      (hall (0 : Fin 4 →₀ ℕ))
  rcases hdvdPoly with ⟨R, hR⟩
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hR
    exact
      (pow_ne_zero Delta Polynomial.X_ne_zero)
        hR
  have hX4 :
      (Polynomial.X ^ 4 : Polynomial K) ≠ 0 :=
    pow_ne_zero 4 Polynomial.X_ne_zero
  have hdeg :
      Delta = 4 + R.natDegree := by
    calc
      Delta =
          (Polynomial.X ^ Delta :
            Polynomial K).natDegree := by
              simp
      _ =
          ((Polynomial.X ^ 4 :
            Polynomial K) * R).natDegree := by
              rw [hR]
      _ =
          (Polynomial.X ^ 4 :
            Polynomial K).natDegree +
              R.natDegree := by
                exact
                  Polynomial.natDegree_mul
                    hX4 hRne
      _ = 4 + R.natDegree := by simp
  omega

/-- **Exact defect after removing one common parameter factor.**

    det Hess(P) = tau^Delta
    P = tau * Q

implies

    det Hess(Q) = tau^(Delta - 4).
-/
theorem commonParameterFactor_one_hasHessianDefect_sub_four
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (commonParameterFactorFamily 1 P hdiv)
      (Delta - 4) := by
  let Q :=
    commonParameterFactorFamily 1 P hdiv
  have hle :
      4 ≤ Delta :=
    four_le_defect_of_commonParameterFactor_one
      P hdiv Delta hdef
  have hfactor :
      P =
        MvPolynomial.C Polynomial.X * Q := by
    simpa using
      commonParameterFactorFamily_factorisation
        (K := K) 1 P hdiv
  have hdet :=
    congrArg HC4.Polynomial.hessianDeterminant
      hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hdef] at hdet
  have hexp :
      4 + (Delta - 4) = Delta := by
    omega
  have hpow :
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C
          (Polynomial.X ^ (Delta - 4)) =
      MvPolynomial.C
        (Polynomial.X ^ Delta) := by
    rw [← MvPolynomial.C_pow,
        ← MvPolynomial.C_mul]
    congr 1
    rw [← pow_add, hexp]
  have hcancel :
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C
          (Polynomial.X ^ (Delta - 4)) =
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        HC4.Polynomial.hessianDeterminant Q := by
    calc
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
          MvPolynomial.C
            (Polynomial.X ^ (Delta - 4)) =
        MvPolynomial.C
          (Polynomial.X ^ Delta) := hpow
      _ =
        (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
          HC4.Polynomial.hessianDeterminant Q := by
            simpa [Q] using hdet
  have hfac :
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 ≠ 0 := by
    exact
      pow_ne_zero 4
        (MvPolynomial.C_ne_zero.mpr
          Polynomial.X_ne_zero)
  have hz :
      (MvPolynomial.C Polynomial.X :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        (MvPolynomial.C
            (Polynomial.X ^ (Delta - 4)) -
          HC4.Polynomial.hessianDeterminant Q) = 0 := by
    rw [mul_sub, hcancel, sub_self]
  have hsub :
      MvPolynomial.C
          (Polynomial.X ^ (Delta - 4)) -
        HC4.Polynomial.hessianDeterminant Q = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfac hzero)
    · exact hzero
  exact (sub_eq_zero.mp hsub).symm

/-- **A single common parameter factor is a strict global restart.**

The new repair coordinate is arbitrary because the first component of
`GlobalRestartProgress` is already strict defect descent. -/
theorem commonParameterFactor_one_strictGlobalRestart
    {s : GlobalRestartState}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hs : s.defect = Delta)
    (newRepair : RepairState) :
    let Q :=
      commonParameterFactorFamily 1 P hdiv
    let t : GlobalRestartState :=
      { defect := Delta - 4
        repair := newRepair }
    HasPolynomialFamilyHessianDefect
        (K := K) Q (Delta - 4) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  dsimp
  have htarget :=
    commonParameterFactor_one_hasHessianDefect_sub_four
      P hdiv Delta hdef
  have hle :=
    four_le_defect_of_commonParameterFactor_one
      P hdiv Delta hdef
  have hlt :
      Delta - 4 < Delta := by
    omega
  refine
    ⟨htarget, ?_, ?_⟩
  · rw [hs]
    exact hlt
  · exact
      Or.inl
        (by
          rw [hs]
          exact hlt)

/-- End-to-end common-factor restart preserving an exact family collision. -/
theorem commonParameterFactor_one_exactCollision_and_strictRestart
    {s : GlobalRestartState}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hs : s.defect = Delta)
    (newRepair : RepairState) :
    let Q :=
      commonParameterFactorFamily 1 P hdiv
    let t : GlobalRestartState :=
      { defect := Delta - 4
        repair := newRepair }
    HasPolynomialFamilyHessianDefect
        (K := K) Q (Delta - 4) ∧
      HasPolynomialFamilyExactGradientCollision
        Q a b ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  dsimp
  have htarget :=
    commonParameterFactor_one_hasHessianDefect_sub_four
      P hdiv Delta hdef
  have hcollision :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      1 P hdiv a b hcoll
  have hrestart :=
    commonParameterFactor_one_strictGlobalRestart
      (s := s) P hdiv hdef hs newRepair
  exact
    ⟨htarget,
      hcollision,
      hrestart.2.1,
      hrestart.2.2⟩

end FinFour

end

end HC4.Valuation
