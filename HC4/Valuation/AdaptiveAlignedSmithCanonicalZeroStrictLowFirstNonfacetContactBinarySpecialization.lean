import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryLongitudinalHessianCoefficients
import Mathlib.Tactic

/-!
# A19.133: specialize the binary contact family back to the represented source

A19.123 replaces the canonical contact Rees by the transversely inflated binary
homogenization whose coefficient at a source exponent `d` is

    tau^(D - profileWeight * d₀) * c_d.

At `tau = 1` this must recover the represented source exactly.  The closing
Schur adapter needs that fact at Hessian level in order to transport A19.129's
nonzero source pivots to the honest binary family used by A19.128--A19.132.

This file records only that representation bridge.  No rank, Schur, residual,
or rigidity argument is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Evaluating the binary-homogenized contact family at `tau = 1` recovers the
represented source exactly. -/
theorem QsOtherFacetContactQuadraticReesPackage.map_eval_one_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial.map (Polynomial.evalRingHom 1) P.binaryHomogenizedFamily =
      polynomialFamilySpecialFiber T.terminal.blocker.presented.family := by
  ext d
  rw [MvPolynomial.coeff_map]
  simpa using P.eval_one_coeff_binaryHomogenizedFamily d

/-- Consequently every source-Hessian entry of the binary family specializes
at `tau = 1` to the corresponding Hessian entry of the represented source. -/
theorem QsOtherFacetContactQuadraticReesPackage.map_eval_one_hessian_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i j : Fin 4) :
    MvPolynomial.map (Polynomial.evalRingHom 1)
        (HC4.Polynomial.hessian P.binaryHomogenizedFamily i j) =
      HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) i j := by
  rw [← P.map_eval_one_binaryHomogenizedFamily]
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
