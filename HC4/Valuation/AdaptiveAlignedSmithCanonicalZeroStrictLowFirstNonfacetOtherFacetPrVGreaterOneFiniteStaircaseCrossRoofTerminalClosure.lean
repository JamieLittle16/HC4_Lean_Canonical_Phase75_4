import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofAffineInterpolation
import HC4.RationalRigidity.FiniteStaircaseCrossRoofMirrorTerminal
import Mathlib.Tactic

/-!
# Exposed cross-roof terminal closure

Once an honest exposed cross-roof face has been realised in both affine-line
orientations, the remaining rigidity is already completely state-free.

The forward rank-three terminal forces the high-side residual `v` to be one.
The reversed terminal forces the low-side residual `q` to be one.  The finite
staircase arithmetic then rules out the simultaneous unit residuals.

This file is deliberately only composition plumbing.  The source-honest
face-to-affine-line realisation lives in the next adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open HC4.RationalRigidity

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **Two oriented terminal certificates on one exposed cross-roof face are
impossible.**

All geometric/source information has already been compressed into `E`.  The
only remaining hypotheses are the two coefficient polynomials and the exact
terminal certificates produced by the affine-line realisation adapter. -/
theorem QsOtherFacetPrLeftVExposedCrossRoofData.impossible_of_terminalCertificates
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {phiHi phiLo : Polynomial K}
    (hdegHi : phiHi.natDegree = E.v)
    (hzeroHi : phiHi.coeff 0 ≠ 0)
    (hcertHi :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiHi)
        (E.kLo : K) (E.q : K) ((F.V * E.jLo : ℕ) : K) 1
        (((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K)
        (-((E.q : K) / (E.v : K)))
        ((F.V : K) * (((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)))
    (hdegLo : phiLo.natDegree = E.q)
    (hzeroLo : phiLo.coeff 0 ≠ 0)
    (hcertLo :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiLo)
        ((E.jHi + 1 : ℕ) : K) (E.v : K)
        ((F.V * (E.kHi - 1) : ℕ) : K) 1
        (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
        (-((E.v : K) / (E.q : K)))
        ((F.V : K) * ((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K))) :
    False := by
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hV : 0 < F.V := by
    have hVgt := F.V_gt_one
    omega

  have hvone : E.v = 1 :=
    finiteStaircase_crossRoof_highResidual_eq_one
      (K := K)
      F.highest.n_two_le hnell hV
      E.kLo_pos E.jLo_pos E.pair_lt
      E.wall_lo E.wall_hi
      E.q_eq E.q_pos E.v_eq E.v_pos
      hdegHi hzeroHi hcertHi

  have hqone : E.q = 1 :=
    finiteStaircase_crossRoof_lowResidual_eq_one
      (K := K)
      F.highest.n_two_le hnell hV
      E.kLo_pos E.pair_lt
      E.wall_lo E.wall_hi
      E.q_eq E.q_pos E.v_eq E.v_pos
      hdegLo hzeroLo hcertLo

  exact HC4.Polynomial.no_crossRoof_unit_residuals
    F.highest.n_two_le hnell E.pair_lt
    E.wall_lo E.wall_hi
    E.q_eq E.v_eq E.q_pos E.v_pos hqone hvone

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation