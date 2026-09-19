import HC4.Valuation.SmithFrontierFourBlockExtraction
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import Mathlib.Tactic

/-!
# A19.R11: parameter-first coefficients are exact source layers

`parameterFirstEquiv` is the canonical swap

    K[x₀,x₁,x₂,x₃][τ]  ≃  K[x₀,x₁,x₂,x₃][τ]

which moves the coefficient-ring parameter `τ` to the outer polynomial
variable.  The exact source-layer API, on the other hand, is expressed by
`familyParameterLayer`.

This file records the coefficient bridge between the two representations and
its Hessian corollary.  It is representation plumbing only: no HC4 geometry or
rank argument enters.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial

universe u v

/-! ## Coefficients of the right Option equivalence -/

/-- Monomials under `optionEquivRight`: the `none` exponent becomes the
coefficient-polynomial exponent and the `some` exponents remain spatial. -/
theorem optionEquivRight_monomial
    {R : Type u} {σ : Type v} [CommSemiring R]
    (m : Option σ →₀ ℕ) (r : R) :
    MvPolynomial.optionEquivRight R σ (MvPolynomial.monomial m r) =
      MvPolynomial.monomial m.some (Polynomial.monomial (m none) r) := by
  rw [MvPolynomial.optionEquivRight_apply,
    MvPolynomial.aeval_monomial, Finsupp.prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    rw [IsScalarTower.algebraMap_apply R (Polynomial R)]
    simp only [Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq,
      Option.elim_none, Option.elim_some, map_mul, mul_assoc]
    simp only [mul_comm, map_pow]
  · simp
  · intros
    rw [pow_add]

/-- Coefficient form of `optionEquivRight`, dual to mathlib's
`optionEquivLeft_coeff_coeff`. -/
theorem optionEquivRight_coeff_coeff
    {R : Type u} {σ : Type v} [CommSemiring R]
    (n : Option σ →₀ ℕ) (f : MvPolynomial (Option σ) R) :
    (MvPolynomial.coeff n.some
        (MvPolynomial.optionEquivRight R σ f)).coeff (n none) =
      MvPolynomial.coeff n f := by
  induction f using MvPolynomial.induction_on' generalizing n with
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial j r =>
      rw [optionEquivRight_monomial]
      classical
      simp only [MvPolynomial.coeff_monomial, apply_ite]
      by_cases hj : j = n
      · subst j
        simp
      · by_cases hsome : j.some = n.some
        · have hnone : j none ≠ n none := by
            intro hnone
            apply hj
            apply Finsupp.ext
            intro x
            cases x with
            | none => exact hnone
            | some x =>
                have hx := congrArg (fun q : σ →₀ ℕ => q x) hsome
                simpa using hx
          simp [hj, hsome]
          rw [Polynomial.coeff_monomial]
          simp [hnone]
        · simp [hj, hsome]

/-! ## The canonical parameter swap -/

variable {K : Type u} [Field K]

/-- Outer coefficient `n` of `parameterFirstEquiv` is exactly the source
coefficient potential at parameter layer `n`. -/
theorem parameterFirstEquiv_coeff
    (P : MvPolynomial (Fin 4) (Polynomial K)) (n : ℕ) :
    (parameterFirstEquiv K P).coeff n = familyParameterLayer P n := by
  classical
  ext d
  rw [familyParameterLayer_coeff]
  let e : Option (Fin 4) →₀ ℕ :=
    d.embDomain .some + Finsupp.single .none n
  let Q : MvPolynomial (Option (Fin 4)) K :=
    (MvPolynomial.optionEquivRight K (Fin 4)).symm P
  have hleft :=
    MvPolynomial.optionEquivLeft_coeff_coeff K (Fin 4) e Q
  have hright := optionEquivRight_coeff_coeff e Q
  have hrecover : MvPolynomial.optionEquivRight K (Fin 4) Q = P := by
    dsimp [Q]
    exact (MvPolynomial.optionEquivRight K (Fin 4)).apply_symm_apply P
  rw [hrecover] at hright
  change
    MvPolynomial.coeff d
        ((MvPolynomial.optionEquivLeft K (Fin 4)
          ((MvPolynomial.optionEquivRight K (Fin 4)).symm P)).coeff n) =
      (MvPolynomial.coeff d P).coeff n
  simpa [e, Q] using hleft.trans hright.symm

/-- Entrywise coefficient form of `parameterFirstHessian`: the `n`th outer
parameter coefficient is literally the Hessian of the `n`th source layer. -/
theorem parameterFirstHessian_coeff
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i j : Fin 4) :
    (parameterFirstHessian P i j).coeff n =
      HC4.Polynomial.hessian (familyParameterLayer P n) i j := by
  change
    (parameterFirstEquiv K (HC4.Polynomial.hessian P i j)).coeff n =
      HC4.Polynomial.hessian (familyParameterLayer P n) i j
  rw [parameterFirstEquiv_coeff]
  exact familyParameterLayer_hessian_apply P n i j

end

end HC4.Valuation
