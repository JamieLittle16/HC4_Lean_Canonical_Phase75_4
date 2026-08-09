import HC4.Valuation.SmithConformalCovariance
import HC4.Newton.SmithPoleMinimality
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Parameter ramification and denominator clearing

The pole-minimal Smith argument uses a small rational conformal tilt and then
"clears denominators".  Phases 93.58--93.59 made the kernel blow-up and the
two-parameter Smith conformal action honest polynomial transformations.
This file makes the denominator-clearing ramification itself honest.

For a positive integer `D`, parameter ramification is

    tau |-> s^D.

On the coefficient ring `K[tau]` this is the ring endomorphism

    c(tau) |-> c(s^D),

implemented by polynomial composition with `X^D`.

The construction is extended coefficientwise to polynomial families and
moving marked sections.  We prove:

* evaluation commutes with ramification;
* exact polynomial-family gradient collision is preserved;
* source derivatives and Hessian determinants commute with ramification;
* a pure Hessian defect `Delta` becomes the pure defect `D * Delta`;
* parameter divisibility scales exactly:
      X^n | c  ->  X^(D*n) | c(s^D);
* the same scaling holds coefficientwise for multivariate families and
  coordinatewise for moving sections.

The last three statements are precisely what is required to turn the
denominator-cleared Smith valuation inequalities from
`SmithPoleMinimality.lean` into the integrality hypotheses consumed by the
green `SmithConformalCovariance.lean`.

No Laurent polynomial or abstract restart hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]
variable {σ : Type*}

/-! ## Coefficient-ring ramification -/

/-- Parameter ramification `tau |-> tau^D` as a ring endomorphism of
`K[tau]`.  The output variable is interpreted as the ramified parameter. -/
noncomputable def parameterRamificationHom
    (D : ℕ) :
    Polynomial K →+* Polynomial K :=
  (Polynomial.X ^ D).compRingHom

/-- Ramification is ordinary polynomial composition with `X^D`. -/
theorem parameterRamificationHom_apply
    (D : ℕ)
    (c : Polynomial K) :
    parameterRamificationHom (K := K) D c =
      c.comp (Polynomial.X ^ D) := by
  simpa [parameterRamificationHom] using
    (Polynomial.coe_compRingHom_apply
      c (Polynomial.X ^ D))

/-- A pure parameter power acquires exactly the ramification factor in its
exponent. -/
theorem parameterRamificationHom_X_pow
    (D n : ℕ) :
    parameterRamificationHom (K := K) D
        (Polynomial.X ^ n) =
      Polynomial.X ^ (D * n) := by
  rw [parameterRamificationHom_apply]
  rw [Polynomial.X_pow_comp]
  rw [← pow_mul]

/-- Ramification of a product is the product of the ramified factors. -/
theorem parameterRamificationHom_mul
    (D : ℕ)
    (a b : Polynomial K) :
    parameterRamificationHom (K := K) D (a * b) =
      parameterRamificationHom (K := K) D a *
        parameterRamificationHom (K := K) D b := by
  exact map_mul
    (parameterRamificationHom (K := K) D) a b

/-- **Parameter divisibility scales under ramification.**

If `tau^n` divides a coefficient before the base change
`tau = s^D`, then `s^(D*n)` divides the ramified coefficient. -/
theorem parameterRamification_pow_dvd
    (D n : ℕ)
    (c : Polynomial K)
    (hdiv :
      Polynomial.X ^ n ∣ c) :
    Polynomial.X ^ (D * n) ∣
      parameterRamificationHom (K := K) D c := by
  rcases hdiv with ⟨r, hr⟩
  refine
    ⟨parameterRamificationHom (K := K) D r, ?_⟩
  rw [hr]
  rw [map_mul]
  rw [parameterRamificationHom_X_pow]

/-! ## Ramified polynomial families and sections -/

/-- Coefficientwise ramification of a multivariate polynomial family. -/
noncomputable def parameterRamificationFamily
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K)) :
    MvPolynomial σ (Polynomial K) :=
  MvPolynomial.map
    (parameterRamificationHom (K := K) D) P

/-- Ramification of a moving polynomial section. -/
noncomputable def parameterRamificationSection
    (D : ℕ)
    (a : σ → Polynomial K) :
    σ → Polynomial K :=
  fun i =>
    parameterRamificationHom (K := K) D (a i)

/-- Evaluation of a ramified family at the ramified section is the
ramification of the original evaluation. -/
theorem eval_parameterRamificationFamily
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (a : σ → Polynomial K) :
    MvPolynomial.eval
        (parameterRamificationSection
          (K := K) D a)
        (parameterRamificationFamily
          (K := K) D P) =
      parameterRamificationHom (K := K) D
        (MvPolynomial.eval a P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [parameterRamificationFamily,
      parameterRamificationSection]
  · intro p q hp hq
    have hadd :=
      congrArg₂
        (fun x y : Polynomial K => x + y)
        hp hq
    simpa [parameterRamificationFamily] using hadd
  · intro p n hp
    have hmul :=
      congrArg
        (fun x : Polynomial K =>
          x *
            parameterRamificationHom (K := K) D (a n))
        hp
    simpa [parameterRamificationFamily,
      parameterRamificationSection] using hmul

/-- **Exact family-gradient collision survives parameter ramification.** -/
theorem polynomialFamilyExactGradientCollision_parameterRamification
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (parameterRamificationFamily
        (K := K) D P)
      (parameterRamificationSection
        (K := K) D a)
      (parameterRamificationSection
        (K := K) D b) := by
  intro i
  unfold parameterRamificationFamily
  rw [MvPolynomial.pderiv_map]
  change
    MvPolynomial.eval
        (parameterRamificationSection
          (K := K) D a)
        (parameterRamificationFamily
          (K := K) D
          (MvPolynomial.pderiv i P)) =
      MvPolynomial.eval
        (parameterRamificationSection
          (K := K) D b)
        (parameterRamificationFamily
          (K := K) D
          (MvPolynomial.pderiv i P))
  rw [eval_parameterRamificationFamily]
  rw [eval_parameterRamificationFamily]
  exact
    congrArg
      (parameterRamificationHom (K := K) D)
      (hcoll i)

/-! ## Hessian covariance under parameter base change -/

section FiniteSource

variable [Fintype σ] [DecidableEq σ]

/-- One Hessian entry commutes with coefficient ramification. -/
theorem hessian_parameterRamificationFamily_entry
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (i j : σ) :
    HC4.Polynomial.hessian
        (parameterRamificationFamily
          (K := K) D P) i j =
      MvPolynomial.map
        (parameterRamificationHom (K := K) D)
        (HC4.Polynomial.hessian P i j) := by
  rw [HC4.Polynomial.hessian_apply]
  unfold parameterRamificationFamily
  rw [MvPolynomial.pderiv_map]
  rw [MvPolynomial.pderiv_map]
  rw [HC4.Polynomial.hessian_apply]

/-- The whole Hessian matrix is obtained by applying ramification to each
entry. -/
theorem hessian_parameterRamificationFamily
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K)) :
    HC4.Polynomial.hessian
        (parameterRamificationFamily
          (K := K) D P) =
      (MvPolynomial.map
        (parameterRamificationHom (K := K) D)).mapMatrix
        (HC4.Polynomial.hessian P) := by
  apply Matrix.ext
  intro i j
  simpa using
    hessian_parameterRamificationFamily_entry
      (K := K) D P i j

/-- **Hessian determinant commutes exactly with parameter ramification.** -/
theorem hessianDeterminant_parameterRamificationFamily
    (D : ℕ)
    (P : MvPolynomial σ (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (parameterRamificationFamily
          (K := K) D P) =
      MvPolynomial.map
        (parameterRamificationHom (K := K) D)
        (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_parameterRamificationFamily]
  exact
    (RingHom.map_det
      (MvPolynomial.map
        (parameterRamificationHom (K := K) D))
      (HC4.Polynomial.hessian P)).symm

end FiniteSource

/-! ## Exact defect scaling -/

section FinFour

/-- **A pure four-variable Hessian defect scales by the ramification
index.**

If

    det Hess(P) = tau^Delta,

then after `tau = s^D`,

    det Hess(P_D) = s^(D*Delta).
-/
theorem parameterRamificationFamily_hasHessianDefect
    (D Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (parameterRamificationFamily
        (K := K) D P)
      (D * Delta) := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_parameterRamificationFamily]
  rw [hdef]
  rw [MvPolynomial.map_C]
  rw [parameterRamificationHom_X_pow]

end FinFour

/-! ## Divisibility packages transported by ramification -/

/-- A variable exponent of required parameter divisibility for every
multivariate source coefficient. -/
def HasParameterCoefficientDivisibility
    (need : (σ →₀ ℕ) → ℕ)
    (P : MvPolynomial σ (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    Polynomial.X ^ (need d) ∣
      MvPolynomial.coeff d P

/-- Ramification multiplies every required coefficient order by `D`. -/
theorem parameterRamificationFamily_coefficientDivisibility
    (D : ℕ)
    (need : (σ →₀ ℕ) → ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasParameterCoefficientDivisibility
        need P) :
    HasParameterCoefficientDivisibility
      (fun d => D * need d)
      (parameterRamificationFamily
        (K := K) D P) := by
  intro d hd
  have hdP :
      d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom (K := K) D)
      P) hd
  have hsource :=
    hdiv d hdP
  unfold parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  exact
    parameterRamification_pow_dvd
      (K := K) D (need d)
      (MvPolynomial.coeff d P)
      hsource

/-- Coordinatewise parameter divisibility for a moving section. -/
def HasParameterSectionDivisibility
    (need : σ → ℕ)
    (a : σ → Polynomial K) : Prop :=
  ∀ i : σ,
    Polynomial.X ^ (need i) ∣ a i

/-- Ramification multiplies every required moving-section order by `D`. -/
theorem parameterRamificationSection_divisibility
    (D : ℕ)
    (need : σ → ℕ)
    (a : σ → Polynomial K)
    (hdiv :
      HasParameterSectionDivisibility
        need a) :
    HasParameterSectionDivisibility
      (fun i => D * need i)
      (parameterRamificationSection
        (K := K) D a) := by
  intro i
  unfold parameterRamificationSection
  exact
    parameterRamification_pow_dvd
      (K := K) D (need i) (a i)
      (hdiv i)

/-! ## The exact Smith denominator as a ramification index -/

/-- Ramification index clearing the explicit finite Smith small tilt. -/
def smithSeparatorRamificationIndex
    (k l : ℕ) : ℕ :=
  finiteTiltDenominator
    (smithExtremeSeparatorBound k l)

/-- Every Smith separator ramification index is positive. -/
theorem smithSeparatorRamificationIndex_pos
    (k l : ℕ) :
    0 < smithSeparatorRamificationIndex k l := by
  unfold smithSeparatorRamificationIndex
  exact
    finiteTiltDenominator_pos
      (smithExtremeSeparatorBound k l)

/-- The integer denominator-cleared tilted value is exactly the affine
valuation expression associated with the Smith ramification index. -/
theorem smithIntegralSeparatorTilt_eq
    (k l : ℕ)
    (base : SmithSupportExponent → ℤ)
    (e : SmithSupportExponent) :
    smithIntegralSeparatorTilt k l base e =
      (smithSeparatorRamificationIndex k l : ℤ) *
          base e +
        smithSeparatorDelta k l e := by
  rfl

/-! ## Pole-minimality as absence of a strict denominator-cleared move -/

/-- A Smith separator strictly improves every supported rescaled valuation. -/
def HasStrictSmithSeparatorImprovement
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ) : Prop :=
  ∃ k l : ℕ,
    ∀ e ∈ S,
      smithRescaledOldMinimum k l m <
        smithIntegralSeparatorTilt k l base e

/-- **Exact logical form of the pole-minimality interface.**

The finite predicate from `SmithPoleMinimality.lean` is precisely the
assertion that no denominator-cleared Smith separator strictly improves
every supported value. -/
theorem isPoleMinimalAgainstSmithSeparators_iff_no_strictImprovement
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ) :
    IsPoleMinimalAgainstSmithSeparators S m base ↔
      ¬ HasStrictSmithSeparatorImprovement S m base := by
  constructor
  · intro hpole himprove
    rcases himprove with ⟨k, l, hall⟩
    rcases hpole k l with
      ⟨e, heS, hnotImprove⟩
    have hstrict := hall e heS
    omega
  · intro hnone k l
    by_contra hmissing
    apply hnone
    refine ⟨k, l, ?_⟩
    intro e heS
    by_contra hnotStrict
    have hle :
        smithIntegralSeparatorTilt k l base e ≤
          smithRescaledOldMinimum k l m :=
      le_of_not_gt hnotStrict
    exact hmissing ⟨e, heS, hle⟩

end

end HC4.Valuation
