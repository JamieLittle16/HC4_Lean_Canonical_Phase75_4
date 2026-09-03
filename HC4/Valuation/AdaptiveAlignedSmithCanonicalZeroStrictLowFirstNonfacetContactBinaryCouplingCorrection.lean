import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryDeterminantProfileBridge
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianEulerReduction
import Mathlib.Tactic

/-!
# A19.R18.21: exact mixed coupling correction layers

R18.20 deliberately stops before identifying the raw binary profile determinant
with the cleared Schur determinant.  The missing algebra is already owned by
`GeneralFourBlock.activeDet_mul_rawComplementDet_eq_schur_coupling_correction`.
This module freezes that identity at the exact parameter layers used by the
finite staircase.

The four correction summands remain private here.  In particular no downstream
module gets a reusable `(p*s-q*r)^2` obligation and no generic product clock is
introduced.  The only public interface from R18.21 will be the terminal-facing
contradiction once the two required correction layers have been eliminated by
the locked other-facet geometry.
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

/-- Parameter-layer form of the exact raw-complement/Schur correction identity.
Kept private so the correction decomposition cannot leak past R18.21. -/
private theorem binaryWeightedEulerShear_couplingCorrection_parameterLayer
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (q : ℕ) :
    familyParameterLayer
        ((P.binaryWeightedEulerShear rho).activeDet *
          ((P.binaryWeightedEulerShear rho).x *
              (P.binaryWeightedEulerShear rho).z -
            (P.binaryWeightedEulerShear rho).y *
              (P.binaryWeightedEulerShear rho).y)) q =
      familyParameterLayer
        ((P.binaryWeightedEulerShear rho).x *
            (P.binaryWeightedEulerShear rho).schurC +
          (P.binaryWeightedEulerShear rho).z *
            (P.binaryWeightedEulerShear rho).schurA -
          2 * (P.binaryWeightedEulerShear rho).y *
            (P.binaryWeightedEulerShear rho).schurB -
          (P.binaryWeightedEulerShear rho).determinantCore +
          ((P.binaryWeightedEulerShear rho).p *
              (P.binaryWeightedEulerShear rho).s -
            (P.binaryWeightedEulerShear rho).q *
              (P.binaryWeightedEulerShear rho).r) ^ 2) q := by
  exact congrArg
    (fun F : MvPolynomial (Fin 4) (Polynomial K) => familyParameterLayer F q)
    (GeneralFourBlock.activeDet_mul_rawComplementDet_eq_schur_coupling_correction
      (P.binaryWeightedEulerShear rho))

/-- The correction identity at an exact quadratic profile order.  This remains
private: later R18.21 code may instantiate it only at the two exposed finite-
staircase orders. -/
private theorem binaryWeightedEulerShear_couplingCorrection_profileOrder
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((P.binaryWeightedEulerShear rho).activeDet *
          ((P.binaryWeightedEulerShear rho).x *
              (P.binaryWeightedEulerShear rho).z -
            (P.binaryWeightedEulerShear rho).y *
              (P.binaryWeightedEulerShear rho).y))
        (2 * T.topFace.degree - P.profileWeight * n) =
      familyParameterLayer
        ((P.binaryWeightedEulerShear rho).x *
            (P.binaryWeightedEulerShear rho).schurC +
          (P.binaryWeightedEulerShear rho).z *
            (P.binaryWeightedEulerShear rho).schurA -
          2 * (P.binaryWeightedEulerShear rho).y *
            (P.binaryWeightedEulerShear rho).schurB -
          (P.binaryWeightedEulerShear rho).determinantCore +
          ((P.binaryWeightedEulerShear rho).p *
              (P.binaryWeightedEulerShear rho).s -
            (P.binaryWeightedEulerShear rho).q *
              (P.binaryWeightedEulerShear rho).r) ^ 2)
        (2 * T.topFace.degree - P.profileWeight * n) := by
  exact binaryWeightedEulerShear_couplingCorrection_parameterLayer P rho
    (2 * T.topFace.degree - P.profileWeight * n)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
