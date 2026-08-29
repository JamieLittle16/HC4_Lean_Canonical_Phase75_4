import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFirstSuperfacePolynomial
import Mathlib.Tactic

/-!
# A19.125: the locked ray is the exact primary initial form of the first superface

A19.117 constructs the first strict superface by perturbing the primary
ray-leading weight.  A19.122 realises that superface as an honest polynomial.
This file records the corresponding nested initial-form identity:

    initialForm rayWeight rayLevel superfacePolynomial = ray.face.

The proof uses only support exposure and exact coefficient inheritance.  In
particular it does not identify the first superface with a plane or add any
new source-homogeneity statement.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- Integer cast of the primary natural ray weight. -/
def qsRayPrimaryIntegerWeight (R : QsOtherFacetRayReverseReesPackage C) :
    Fin 4 → ℤ := fun i => (R.weight i : ℤ)

/-- The primary ray remains an exposed face after restricting from the whole
represented source to A19.117's first strict superface. -/
theorem QsOtherFacetRayFirstSuperfacePackage.ray_exposed_in_polynomial
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Newton.IsExposedFace
      (↑S.polynomial.support : Set (Fin 4 →₀ ℕ))
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
      (fun e => Finsupp.weight (qsRayPrimaryIntegerWeight R) e)
      (R.level : ℤ) := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let wR : Fin 4 → ℤ := qsRayPrimaryIntegerWeight R
  have hRbound : HC4.Polynomial.IsWeightLE wR (R.level : ℤ) F := by
    intro e he
    have h := R.bound e he
    rw [show Finsupp.weight wR e = (Finsupp.weight R.weight e : ℤ) by
      exact weight_natCast_eq R.weight e]
    exact_mod_cast h
  have hRsource :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight wR e) (R.level : ℤ) := by
    have h := HC4.Newton.initialForm_support_isExposedFace
      wR (R.level : ℤ) F hRbound
    rw [R.initialForm_eq_ray] at h
    exact h
  constructor
  · ext e
    constructor
    · intro heRay
      have heRayFin : e ∈ C.ray.face.support := by simpa using heRay
      have heSFin : e ∈ S.polynomial.support := S.ray_support_subset heRayFin
      exact ⟨by simpa using heSFin, hRsource.weight_eq heRay⟩
    · rintro ⟨heS, hw⟩
      have heSFin : e ∈ S.polynomial.support := by simpa using heS
      have heSourceFin : e ∈ F.support := by
        exact HC4.Polynomial.support_initialForm_subset
          S.combinedWeight S.combinedLevel F heSFin
      exact hRsource.mem_iff.mpr ⟨by simpa using heSourceFin, hw⟩
  · intro e heS
    have heSFin : e ∈ S.polynomial.support := by simpa using heS
    have heSourceFin : e ∈ F.support := by
      exact HC4.Polynomial.support_initialForm_subset
        S.combinedWeight S.combinedLevel F heSFin
    exact hRsource.weight_le (by simpa using heSourceFin)

/-- **Nested exact initial-form identity.**  Taking the original ray-leading
initial form of the honest first-superface polynomial recovers the locked ray
with its actual coefficients. -/
theorem QsOtherFacetRayFirstSuperfacePackage.initialForm_primary_eq_ray
    (S : QsOtherFacetRayFirstSuperfacePackage C R) :
    HC4.Polynomial.initialForm (qsRayPrimaryIntegerWeight R) (R.level : ℤ)
        S.polynomial = C.ray.face := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let wR : Fin 4 → ℤ := qsRayPrimaryIntegerWeight R
  apply HC4.Newton.initialForm_eq_of_exposedSupport_and_coeff
    wR (R.level : ℤ) S.polynomial C.ray.face S.ray_exposed_in_polynomial
  intro d hdRay
  have hdS : d ∈ S.polynomial.support := S.ray_support_subset hdRay
  have hScoeff :
      MvPolynomial.coeff d S.polynomial = MvPolynomial.coeff d F := by
    simpa [F] using S.coeff_polynomial_eq_source_of_mem hdS
  have hdInit :
      d ∈ (HC4.Polynomial.initialForm wR (R.level : ℤ) F).support := by
    rw [R.initialForm_eq_ray]
    exact hdRay
  have hRayCoeff :
      MvPolynomial.coeff d C.ray.face = MvPolynomial.coeff d F := by
    have h := HC4.Newton.initialForm_coeff_eq_source_of_mem
      wR (R.level : ℤ) F hdInit
    rw [R.initialForm_eq_ray] at h
    exact h
  exact hRayCoeff.trans hScoeff.symm

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
