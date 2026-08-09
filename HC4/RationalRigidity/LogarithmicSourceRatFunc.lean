import HC4.RationalRigidity.AutonomousRatFuncAssembly
import Mathlib.Tactic

/-!
# The regular RatFunc presentation of the logarithmic derivative

Phase 85 produced the reduced polynomial numerator

    (E N) D - N (E D)

over `D^2`, where `rho = N/D` is the canonical logarithmic source.  Here we
package that pair as an actual rational function `eta` and prove two facts
needed by the autonomous assembly:

* `eta` is regular wherever `rho` is regular;
* it is the same rational function as the raw expression
  `logarithmicEtaNumerator(phi) / phi^2` whenever `phi != 0`.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The regular rational function representing `eta = E(rho)` for the
canonical logarithmic source. -/
def logarithmicSourceEtaRatFunc (phi : Polynomial K) : RatFunc K :=
  polynomialPairRatFunc
    (logarithmicSourceEtaNumerator phi)
    ((logarithmicSourceDenominator phi) ^ 2)

/-- Its canonical denominator divides the manifest finite-chart denominator
`D^2`; hence `eta` is regular wherever the reduced source `rho=N/D` is. -/
theorem logarithmicSourceEtaRatFunc_regularAt
    (phi : Polynomial K) {x : K}
    (hD : RatFuncRegularAt x (logarithmicSourceRatFunc phi)) :
    RatFuncRegularAt x (logarithmicSourceEtaRatFunc phi) := by
  unfold RatFuncRegularAt at hD ⊢
  have hdvd :
      (logarithmicSourceEtaRatFunc phi).denom ∣
        (logarithmicSourceDenominator phi) ^ 2 := by
    simpa [logarithmicSourceEtaRatFunc, canonicalReducedDenominator] using
      (canonicalReduced_denominator_dvd
        (logarithmicSourceEtaNumerator phi)
        ((logarithmicSourceDenominator phi) ^ 2))
  apply eval_ne_zero_of_dvd hdvd
  simpa [logarithmicSourceRatFunc, logarithmicSourceDenominator,
    canonicalReducedDenominator] using pow_ne_zero 2 hD

/-- The regular reduced presentation of `eta` equals the raw
`A(phi)/phi^2` presentation as a rational function. -/
theorem logarithmicSourceEtaRatFunc_eq_raw
    (phi : Polynomial K) (hphi : phi ≠ 0) :
    logarithmicSourceEtaRatFunc phi =
      polynomialPairRatFunc
        (HC4.Polynomial.logarithmicEtaNumerator phi) (phi ^ 2) := by
  unfold logarithmicSourceEtaRatFunc polynomialPairRatFunc
  have hDpoly : (logarithmicSourceDenominator phi) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (logarithmicSource_denominator_ne_zero phi)
  have hphipow : phi ^ 2 ≠ 0 := pow_ne_zero 2 hphi
  have hDmap :
      (algebraMap (Polynomial K) (RatFunc K))
          ((logarithmicSourceDenominator phi) ^ 2) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hDpoly
  have hphimap :
      (algebraMap (Polynomial K) (RatFunc K)) (phi ^ 2) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hphipow
  apply (div_eq_div_iff hDmap hphimap).2
  have hcross := logarithmicSource_eta_cross_identity phi hphi
  simpa using
    congrArg (algebraMap (Polynomial K) (RatFunc K)) hcross

end

end HC4.RationalRigidity
