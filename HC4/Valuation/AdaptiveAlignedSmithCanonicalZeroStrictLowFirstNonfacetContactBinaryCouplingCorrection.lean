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

/-- The same correction remainder before the simultaneous transverse
inflation.  It is kept private: its only purpose is to expose the exact contact
layer from which each binary source coefficient originates. -/
private noncomputable def contactWeightedEulerShear_extremalRemainder
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (P.contactWeightedEulerShear rho).x *
      (P.contactWeightedEulerShear rho).schurC +
    (P.contactWeightedEulerShear rho).z *
      (P.contactWeightedEulerShear rho).schurA -
    2 * (P.contactWeightedEulerShear rho).y *
      (P.contactWeightedEulerShear rho).schurB +
    ((P.contactWeightedEulerShear rho).p *
        (P.contactWeightedEulerShear rho).s -
      (P.contactWeightedEulerShear rho).q *
        (P.contactWeightedEulerShear rho).r) ^ 2

/-- The binary correction remainder is literally the contact correction
remainder transported through simultaneous unit transverse inflation. -/
private theorem binaryWeightedEulerShear_extremalRemainder_eq_map_contact
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    binaryWeightedEulerShear_extremalRemainder P rho =
      unitTransverseInflateRingHom (K := K)
        (contactWeightedEulerShear_extremalRemainder P rho) := by
  rw [binaryWeightedEulerShear_extremalRemainder,
    binaryWeightedEulerShear_borderedCorrection,
    binaryWeightedEulerShear_mixedCouplingSquare,
    P.binaryWeightedEulerShear_eq_map_contact rho]
  simp [contactWeightedEulerShear_extremalRemainder,
    GeneralFourBlock.map]

/-- Exact coefficient shift under simultaneous unit transverse inflation.
A contact parameter layer `q` at source exponent `d` reappears in binary layer
`q + (d₁+d₂+d₃)`, with no loss or cancellation. -/
private theorem familyParameterLayer_unitTransverseInflateFamily_coeff_add_transverse
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (q : ℕ) :
    MvPolynomial.coeff d
        (familyParameterLayer
          (unitTransverseInflateFamily (K := K) F)
          (q + (d 1 + d 2 + d 3))) =
      MvPolynomial.coeff d (familyParameterLayer F q) := by
  rw [familyParameterLayer_coeff, coeff_unitTransverseInflateFamily,
    Polynomial.coeff_X_pow_mul']
  have hle : d 1 + d 2 + d 3 ≤ q + (d 1 + d 2 + d 3) := by
    omega
  rw [if_pos hle]
  have hsub : q + (d 1 + d 2 + d 3) - (d 1 + d 2 + d 3) = q := by
    omega
  rw [hsub, familyParameterLayer_coeff]

/-- Coefficientwise contact/binary grading dictionary for the private R18.21
correction remainder.  This is the precise replacement for any claim that the
contact and binary filtrations are equal. -/
private theorem binaryWeightedEulerShear_extremalRemainder_layer_coeff_eq_contact
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (d : Fin 4 →₀ ℕ)
    (q : ℕ) :
    MvPolynomial.coeff d
        (familyParameterLayer
          (binaryWeightedEulerShear_extremalRemainder P rho)
          (q + (d 1 + d 2 + d 3))) =
      MvPolynomial.coeff d
        (familyParameterLayer
          (contactWeightedEulerShear_extremalRemainder P rho) q) := by
  rw [binaryWeightedEulerShear_extremalRemainder_eq_map_contact]
  rw [unitTransverseInflateRingHom_apply]
  exact familyParameterLayer_unitTransverseInflateFamily_coeff_add_transverse
    (contactWeightedEulerShear_extremalRemainder P rho) d q

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

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
