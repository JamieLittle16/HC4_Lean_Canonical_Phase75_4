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

/-- The three bordered Schur contributions in the correction identity. -/
private noncomputable def binaryWeightedEulerShear_borderedCorrection
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (P.binaryWeightedEulerShear rho).x *
      (P.binaryWeightedEulerShear rho).schurC +
    (P.binaryWeightedEulerShear rho).z *
      (P.binaryWeightedEulerShear rho).schurA -
    2 * (P.binaryWeightedEulerShear rho).y *
      (P.binaryWeightedEulerShear rho).schurB

/-- The final mixed active/complement coupling square. -/
private noncomputable def binaryWeightedEulerShear_mixedCouplingSquare
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  ((P.binaryWeightedEulerShear rho).p *
      (P.binaryWeightedEulerShear rho).s -
    (P.binaryWeightedEulerShear rho).q *
      (P.binaryWeightedEulerShear rho).r) ^ 2

/-- The exact remainder left after the full determinant term has been removed.
This is the only correction object the extremal terminal calculation has to
kill. -/
private noncomputable def binaryWeightedEulerShear_extremalRemainder
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  binaryWeightedEulerShear_borderedCorrection P rho +
    binaryWeightedEulerShear_mixedCouplingSquare P rho

/-- The correction identity at the active-pivot shifted profile order.  The
`+4` is the exact order used by the one-pivot finite-staircase cancellation;
the older unshifted wrapper is deliberately not exposed. -/
private theorem binaryWeightedEulerShear_couplingCorrection_profileOrder_add_four
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((P.binaryWeightedEulerShear rho).activeDet *
          ((P.binaryWeightedEulerShear rho).x *
              (P.binaryWeightedEulerShear rho).z -
            (P.binaryWeightedEulerShear rho).y *
              (P.binaryWeightedEulerShear rho).y))
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) =
      familyParameterLayer
        (binaryWeightedEulerShear_borderedCorrection P rho -
          (P.binaryWeightedEulerShear rho).determinantCore +
          binaryWeightedEulerShear_mixedCouplingSquare P rho)
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) := by
  simpa [binaryWeightedEulerShear_borderedCorrection,
    binaryWeightedEulerShear_mixedCouplingSquare] using
    binaryWeightedEulerShear_couplingCorrection_parameterLayer P rho
      ((2 * T.topFace.degree - P.profileWeight * n) + 4)

/-- **R18.21 normalized correction seam.**  At every shifted profile order the
full determinant term is already killed by the exact binary Hessian clock.
Thus the raw-complement side is equal to one explicit extremal remainder:
three bordered Schur contributions plus the mixed coupling square.

No active pivot is cancelled here, and no geometric vanishing is asserted. -/
private theorem binaryWeightedEulerShear_couplingCorrection_profileOrder_add_four_reduced
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        ((P.binaryWeightedEulerShear rho).activeDet *
          ((P.binaryWeightedEulerShear rho).x *
              (P.binaryWeightedEulerShear rho).z -
            (P.binaryWeightedEulerShear rho).y *
              (P.binaryWeightedEulerShear rho).y))
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) =
      familyParameterLayer
        (binaryWeightedEulerShear_extremalRemainder P rho)
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) := by
  let q : ℕ := (2 * T.topFace.degree - P.profileWeight * n) + 4
  have hcorr :=
    binaryWeightedEulerShear_couplingCorrection_profileOrder_add_four P rho n
  have hdet :=
    P.binaryWeightedEulerShear_determinantCore_parameterLayer_profileOrder_add_four_eq_zero
      rho n
  calc
    familyParameterLayer
        ((P.binaryWeightedEulerShear rho).activeDet *
          ((P.binaryWeightedEulerShear rho).x *
              (P.binaryWeightedEulerShear rho).z -
            (P.binaryWeightedEulerShear rho).y *
              (P.binaryWeightedEulerShear rho).y)) q =
      familyParameterLayer
        (binaryWeightedEulerShear_borderedCorrection P rho -
          (P.binaryWeightedEulerShear rho).determinantCore +
          binaryWeightedEulerShear_mixedCouplingSquare P rho) q := by
        simpa [q] using hcorr
    _ = familyParameterLayer
        (binaryWeightedEulerShear_extremalRemainder P rho) q := by
      apply MvPolynomial.ext
      intro d
      have hd := congrArg (MvPolynomial.coeff d) hdet
      rw [familyParameterLayer_coeff] at hd
      simp only [MvPolynomial.coeff_zero] at hd
      rw [familyParameterLayer_coeff, familyParameterLayer_coeff]
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
        Polynomial.coeff_add, Polynomial.coeff_sub]
      rw [hd]
      simp [binaryWeightedEulerShear_extremalRemainder]

-- CI anchor: compile the normalized R18.21 remainder after inventory refresh.

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
