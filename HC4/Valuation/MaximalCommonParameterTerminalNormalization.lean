import HC4.Valuation.CommonParameterFactorGeneralDefect
import HC4.Valuation.StrictSmithMaximalNormalization
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# A18.5.15: canonical maximal common-parameter normalization

Every nonzero polynomial-parameter family has a least parameter order among
its finitely many nonzero source coefficients.  Removing exactly that common
power has three crucial properties:

* the normalized special fibre is nonzero because the minimum is attained;
* the exact marked gradient collision survives common-factor cancellation;
* in four source variables the pure Hessian clock changes from `Delta` to
  `Delta - 4*m`.

This is the terminal normalization needed before the final polynomial support
analysis.  It is independent of any Smith or rank-three case split.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact finite-support normalization data for a nonzero family with a pure
Hessian clock. -/
structure MaximalCommonParameterFamilyData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ) : Type (u + 1) where
  order : ℕ
  witness : Fin 4 →₀ ℕ
  witness_mem : witness ∈ P.support
  witness_order : smithFamilyCoefficientOrder P witness = order
  minimum : ∀ d ∈ P.support, order ≤ smithFamilyCoefficientOrder P d
  divisible : HasCommonParameterFactor order P
  family : MvPolynomial (Fin 4) (Polynomial K)
  family_eq : family = commonParameterFactorFamily order P divisible
  specialFiber_ne_zero : polynomialFamilySpecialFiber family ≠ 0
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K) family (Delta - 4 * order)

/-- Select the attained least coefficient order and remove it in one step. -/
noncomputable def maximalCommonParameterFamilyData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    MaximalCommonParameterFamilyData P Delta := by
  have hsupport : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  rcases Finset.exists_min_image P.support
      (smithFamilyCoefficientOrder P) hsupport with ⟨d, hd, hmin⟩
  let m := smithFamilyCoefficientOrder P d
  have hdiv : HasCommonParameterFactor m P := by
    intro q hq
    have hle : m ≤ smithFamilyCoefficientOrder P q := hmin q hq
    exact dvd_trans
      (polynomial_X_pow_dvd_X_pow_of_le (K := K)
        m (smithFamilyCoefficientOrder P q) hle)
      (smithFamilyCoefficientOrder_dvd P hq)
  let Q := commonParameterFactorFamily m P hdiv
  have hspecial : polynomialFamilySpecialFiber Q ≠ 0 := by
    dsimp [Q]
    exact polynomialFamilySpecialFiber_commonParameterFactor_minOrder_ne_zero
      (K := K) P m (fun q hq => hmin q hq) hdiv ⟨d, hd, rfl⟩
  have hQdef :
      HasPolynomialFamilyHessianDefect (K := K) Q (Delta - 4 * m) := by
    dsimp [Q]
    exact commonParameterFactor_hasHessianDefect_sub_four_mul
      m P hdiv Delta hdef
  exact {
    order := m
    witness := d
    witness_mem := hd
    witness_order := rfl
    minimum := fun q hq => hmin q hq
    divisible := hdiv
    family := Q
    family_eq := rfl
    specialFiber_ne_zero := hspecial
    hessianDefect := hQdef
  }

/-- A pure Hessian clock makes the original parameter family nonzero. -/
theorem polynomialFamily_ne_zero_of_hessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    P ≠ 0 := by
  intro hP
  have hzero : HC4.Polynomial.hessianDeterminant P = 0 := by
    rw [hP]
    simp [HC4.Polynomial.hessianDeterminant, HC4.Polynomial.hessian]
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef] at hzero
  have hC :
      (MvPolynomial.C (Polynomial.X ^ Delta) :
        MvPolynomial (Fin 4) (Polynomial K)) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (pow_ne_zero Delta Polynomial.X_ne_zero)
  exact hC hzero

/-- State-facing normalized terminal-family package.  The finite restart state
itself is not changed; this is a polynomial carrier for terminal analysis. -/
structure ScaleAwareMaximalCommonParameterFamilyData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  core : MaximalCommonParameterFamilyData s.family s.rawDefect
  nonlinearDegreeBound : NonlinearDegreeBound s.degreeCap core.family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      core.family (fun _ => (0 : Polynomial K)) s.movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint s.movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  specialFiberCollision :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber core.family)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))

/-- Every scale-aware state canonically supplies a maximally parameter-normalized
polynomial carrier with nonzero special fibre. -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.maximalCommonParameterFamily
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    ScaleAwareMaximalCommonParameterFamilyData s := by
  have hP : s.family ≠ 0 :=
    polynomialFamily_ne_zero_of_hessianDefect
      s.family s.rawDefect s.hessianDefect
  let C := maximalCommonParameterFamilyData
    s.family hP s.rawDefect s.hessianDefect
  have hdegree : NonlinearDegreeBound s.degreeCap C.family := by
    rw [C.family_eq]
    apply nonlinearDegreeBound_of_support_subset s.nonlinearDegreeBound
    exact support_commonParameterFactorFamily_subset
      C.order s.family C.divisible
  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        C.family (fun _ => (0 : Polynomial K)) s.movingSection := by
    rw [C.family_eq]
    exact polynomialFamilyExactGradientCollision_commonParameterFactor
      C.order s.family C.divisible
      (fun _ => (0 : Polynomial K)) s.movingSection s.exactCollision
  have hspecial :
      HasExactGradientCollision
        (polynomialFamilySpecialFiber C.family)
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
    have h := polynomialFamilyZeroCollision_specialFiber
      C.family s.movingSection hcoll
    rw [s.sectionSpecial] at h
    exact h
  exact {
    core := C
    nonlinearDegreeBound := hdegree
    exactCollision := hcoll
    sectionSpecial := s.sectionSpecial
    specialFiberCollision := hspecial
  }

end

end HC4.Valuation
