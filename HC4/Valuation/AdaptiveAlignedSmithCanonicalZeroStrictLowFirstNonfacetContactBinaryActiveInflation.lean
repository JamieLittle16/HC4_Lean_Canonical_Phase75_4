import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryHomogenization
import HC4.Valuation.KernelInflationHessianDefect
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# A19.R18: exact transverse-inflation factor on the cyclic active pivots

The binary contact family is obtained from the honest contact Rees by inflating
all three transverse source coordinates once.  Every transverse Hessian row
and column therefore acquires one parameter factor.  A principal minor on two
transverse coordinates acquires exactly four factors of `tau`.

The three surviving other-facet pivots use precisely the pairs `(2,3)`,
`(1,3)`, and `(1,2)`.  We record those identities directly.  This isolates the
exact valuation shift contributed by the active block and avoids treating mere
nonvanishing as coefficientwise invertibility.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem kernelInflateHom_C
    (kernel : Fin 4) (slope : ℕ) (p : Polynomial K) :
    kernelInflateHom (K := K) kernel slope (MvPolynomial.C p) =
      MvPolynomial.C p := by
  simp [kernelInflateHom]

private theorem hessianPrincipalMinor_unitTransverseInflate_two_three
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianPrincipalMinor
        (unitTransverseInflateFamily (K := K) P) (2 : Fin 4) 3 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P (2 : Fin 4) 3) := by
  unfold unitTransverseInflateFamily HC4.Polynomial.hessianPrincipalMinor
  repeat' rw [hessian_kernelInflateHom_entry]
  simp [kernelInflateDerivativeCoefficient, map_sub, map_mul,
    kernelInflateHom_C]
  ring

private theorem hessianPrincipalMinor_unitTransverseInflate_one_three
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianPrincipalMinor
        (unitTransverseInflateFamily (K := K) P) (1 : Fin 4) 3 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P (1 : Fin 4) 3) := by
  unfold unitTransverseInflateFamily HC4.Polynomial.hessianPrincipalMinor
  repeat' rw [hessian_kernelInflateHom_entry]
  simp [kernelInflateDerivativeCoefficient, map_sub, map_mul,
    kernelInflateHom_C]
  ring

private theorem hessianPrincipalMinor_unitTransverseInflate_one_two
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianPrincipalMinor
        (unitTransverseInflateFamily (K := K) P) (1 : Fin 4) 2 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P (1 : Fin 4) 2) := by
  unfold unitTransverseInflateFamily HC4.Polynomial.hessianPrincipalMinor
  repeat' rw [hessian_kernelInflateHom_entry]
  simp [kernelInflateDerivativeCoefficient, map_sub, map_mul,
    kernelInflateHom_C]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- `.pr`: the binary `(2,3)` active pivot is exactly the contact pivot after
transverse inflation, multiplied by `tau^4`. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_binary_hessianPrincipalMinor_eq_X_pow_four_mul
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    HC4.Polynomial.hessianPrincipalMinor P.binaryHomogenizedFamily
        (2 : Fin 4) 3 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P.contactFamily
            (2 : Fin 4) 3) := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily]
  exact hessianPrincipalMinor_unitTransverseInflate_two_three P.contactFamily

/-- `.sp`: the binary `(1,3)` active pivot has the same exact `tau^4` factor. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_binary_hessianPrincipalMinor_eq_X_pow_four_mul
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    HC4.Polynomial.hessianPrincipalMinor P.binaryHomogenizedFamily
        (1 : Fin 4) 3 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P.contactFamily
            (1 : Fin 4) 3) := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily]
  exact hessianPrincipalMinor_unitTransverseInflate_one_three P.contactFamily

/-- `.rq`: the binary `(1,2)` active pivot has the same exact `tau^4` factor. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_binary_hessianPrincipalMinor_eq_X_pow_four_mul
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    HC4.Polynomial.hessianPrincipalMinor P.binaryHomogenizedFamily
        (1 : Fin 4) 2 =
      MvPolynomial.C ((Polynomial.X : Polynomial K) ^ 4) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessianPrincipalMinor P.contactFamily
            (1 : Fin 4) 2) := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily]
  exact hessianPrincipalMinor_unitTransverseInflate_one_two P.contactFamily

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
