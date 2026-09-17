import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCrossRoofAffineInterpolation
import HC4.RationalRigidity.FiniteStaircaseCrossRoofMirrorTerminal
import Mathlib.Tactic

/-!
# Unit exposed cross-roof terminal closure

Once one honest exposed unit cross-roof face has been realised in both affine
orientations, the remaining contradiction is state-free.  Instantiate the
verified cross-roof rigidity at `V = 1`: the forward certificate forces the
high-side residual `v` to be one, the reverse certificate forces the low-side
residual `q` to be one, and the existing staircase arithmetic excludes the
simultaneous unit residuals.
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

/-- **Two oriented terminal certificates on one exposed unit cross-roof face
are impossible.** -/
theorem QsOtherFacetPrUnitLeftExposedCrossRoofData.impossible_of_terminalCertificates
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {phiHi phiLo : Polynomial K}
    (hdegHi : phiHi.natDegree = E.v)
    (hzeroHi : phiHi.coeff 0 ≠ 0)
    (hcertHi :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiHi)
        (E.kLo : K) (E.q : K) (E.jLo : K) 1
        ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
        (-((E.q : K) / (E.v : K)))
        ((((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)))
    (hdegLo : phiLo.natDegree = E.q)
    (hzeroLo : phiLo.coeff 0 ≠ 0)
    (hcertLo :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiLo)
        ((E.jHi + 1 : ℕ) : K) (E.v : K)
        ((E.kHi - 1 : ℕ) : K) 1
        (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
        (-((E.v : K) / (E.q : K)))
        (((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K))) :
    False := by
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hV : 0 < (1 : ℕ) := by norm_num

  have hcertHi' :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiHi)
        (E.kLo : K) (E.q : K) (((1 : ℕ) * E.jLo : ℕ) : K) 1
        ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
        (-((E.q : K) / (E.v : K)))
        (((1 : ℕ) : K) * ((((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K))) := by
    simpa using hcertHi

  have hvone : E.v = 1 :=
    finiteStaircase_crossRoof_highResidual_eq_one
      (K := K) (V := 1)
      F.highest.n_two_le hnell hV
      E.kLo_pos E.jLo_pos E.pair_lt
      E.wall_lo E.wall_hi
      E.q_eq E.q_pos E.v_eq E.v_pos
      hdegHi hzeroHi hcertHi'

  have hcertLo' :
      HasRankThreePolynomialTerminalCertificate
        (phi := phiLo)
        (E.jHi + 1 : K) (E.v : K)
        (((1 : ℕ) * (E.kHi - 1) : ℕ) : K) 1
        (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
        (-((E.v : K) / (E.q : K)))
        (((1 : ℕ) : K) * (((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K))) := by
    simpa [Nat.cast_add] using hcertLo

  have hqone : E.q = 1 :=
    finiteStaircase_crossRoof_lowResidual_eq_one
      (K := K) (V := 1)
      F.highest.n_two_le hnell hV
      E.kLo_pos E.pair_lt
      E.wall_lo E.wall_hi
      E.q_eq E.q_pos E.v_eq E.v_pos
      hdegLo hzeroLo hcertLo'

  exact HC4.Polynomial.no_crossRoof_unit_residuals
    F.highest.n_two_le hnell E.pair_lt
    E.wall_lo E.wall_hi
    E.q_eq E.v_eq E.q_pos E.v_pos hqone hvone

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation