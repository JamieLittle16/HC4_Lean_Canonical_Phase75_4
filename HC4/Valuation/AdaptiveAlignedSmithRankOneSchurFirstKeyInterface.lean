import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockEarlySchurProjectiveKernel
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import Mathlib.Tactic

/-!
# First source-honest spatial key on the exact-clock early Schur branch

Stage 4A isolated the remaining projective issue cleanly: the honest special
fibre carries a nonzero polynomial full Hessian-kernel vector, and a constant
projective factorisation of that vector immediately gives an honest constant
source-kernel direction.

Before proving the genuinely new RS2 statement, this file assembles the
source-side input which is already present elsewhere in the library.

For the honest right-recentered special fibre

    F₀ = polynomialFamilySpecialFiber C.family

stationarity gives actual transverse source support.  We therefore select the
*least positive total transverse degree* `m` using the existing filtration
from `AdaptiveAlignedSmithPureLongitudinalHigherEscape` and expose

    Q = initialForm pureLongitudinalTransverseWeight (-m) F₀.

Nothing new is proved about this filtration here.  We only package the
already-green facts:

* `m > 0`;
* `Q ≠ 0`;
* `Q` is exactly weighted-homogeneous of weight `-m`;
* Hessian formation commutes entrywise with this exact initial form.

On an `earlySchurTangential` final-local constructor we then retain, in one
record, this first spatial key together with all the already-green data that
the RS2/projective theorem needs:

* the nonzero honest first actual source potential;
* the complete preclosing raw-Schur-ray prefix;
* the exact first-actual source/Hessian frontier;
* the Stage-3 nonzero denominator-cleared full polynomial kernel.

Thus the next file does not need to reconstruct any source layer, Schur ray,
initial-form lemma, or polynomial kernel lift.  Its only new mathematical job
is the provenance statement relating projective kernel motion to the first
spatial key (and hence to repair or constant projective direction).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The least positive transverse exact component of the honest special fibre,
packaged only through properties already proved by the transverse-filtration
library. -/
def HasFirstTransverseSourceKey
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∃ hpos :
      (positiveTransverseSourceSupport
        (polynomialFamilySpecialFiber C.family)).Nonempty,
    let F₀ := polynomialFamilySpecialFiber C.family
    let m := firstPositiveTransverseSourceDegree F₀ hpos
    let Q :=
      HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
        (-(m : ℤ)) F₀
    0 < m ∧
      Q ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)) ∧
      ∀ i j : Fin 4,
        HC4.Polynomial.hessian Q i j =
          HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
            (-(m : ℤ) - pureLongitudinalTransverseWeight i -
              pureLongitudinalTransverseWeight j)
            (HC4.Polynomial.hessian F₀ i j)

/-- Once positive transverse support is known, the first-key package is an
immediate assembly of the existing minimal-degree and derivative-weight
lemmas. -/
theorem hasFirstTransverseSourceKey_of_positiveSupport
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpos :
      (positiveTransverseSourceSupport
        (polynomialFamilySpecialFiber C.family)).Nonempty) :
    C.HasFirstTransverseSourceKey := by
  refine ⟨hpos, ?_⟩
  dsimp only
  let F₀ := polynomialFamilySpecialFiber C.family
  let m := firstPositiveTransverseSourceDegree F₀ hpos
  let Q :=
    HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
      (-(m : ℤ)) F₀

  have hmpos : 0 < m := by
    rcases exists_source_firstPositiveTransverseSourceDegree F₀ hpos with
      ⟨d, _hd, hdegpos, hdeg⟩
    rw [hdeg] at hdegpos
    simpa [m] using hdegpos

  have hQne : Q ≠ 0 := by
    dsimp [Q, m, F₀]
    exact firstPositiveTransverseInitialForm_ne_zero
      (polynomialFamilySpecialFiber C.family) hpos

  have hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)) := by
    dsimp [Q]
    exact HC4.Polynomial.initialForm_isWeightedHomogeneous
      pureLongitudinalTransverseWeight (-(m : ℤ)) F₀

  refine ⟨hmpos, hQne, hQhom, ?_⟩
  intro i j
  dsimp [Q]
  exact HC4.Polynomial.hessian_initialForm_entry
    pureLongitudinalTransverseWeight (-(m : ℤ)) F₀ i j

/-- The selected first actual coefficient potential is genuinely nonzero.
This is just the carrier-specialised form of
`firstPositiveActualParameterLayer_ne_zero`. -/
theorem firstActualLayerPotential_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    familyParameterLayer C.family C.firstActualLayerOrder ≠ 0 := by
  simpa [firstActualLayerOrder] using
    firstPositiveActualParameterLayer_ne_zero
      C.family C.hasPositiveActualParameterLayer

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- All already-green source/Schur data needed by the genuinely new RS2
projective theorem on one early-Schur constructor.

The record deliberately contains no repair claim and no projective-constancy
claim.  Those are exactly the next theorem boundary. -/
structure AdaptiveAlignedSmithEarlySchurFirstKeyContext
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt :
      C.firstActualLayerOrder <
        P.stationary.blocker.aligned.endpoint.defect) where
  firstSpatialKey : C.HasFirstTransverseSourceKey
  firstActualPotential_ne_zero :
    familyParameterLayer C.family C.firstActualLayerOrder ≠ 0
  rawRayPrefix :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.HasAdaptiveAlignedRawSchurRayPrefix C
  lowerHessianZero :
    ∀ n : ℕ,
      0 < n →
      n < C.firstActualLayerOrder →
      familyParameterHessianLayer C.family n = 0
  firstActualHessian :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber
          C.relativeFirstActualDeformationFamily) =
      familyParameterHessianLayer C.family C.firstActualLayerOrder
  firstActualTangential :
    C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder
  polynomialKernel :
    Nonempty C.DenominatorClearedSpecialSchurKernelData

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- Stationary all-transverse-zero geometry supplies positive transverse
support to every honest closing carrier over the same blocker. -/
theorem earlySchur_positiveTransverseSourceSupport
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker) :
    (positiveTransverseSourceSupport
      (polynomialFamilySpecialFiber C.family)).Nonempty := by
  rcases P.specialFiber_witnesses.1 with ⟨d, hd, hd1⟩
  refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using hd
  · unfold pureLongitudinalTransverseDegree
    omega

/-- **Stage 4B input assembly.**

Every exact-clock early-Schur constructor already carries the complete input
package for the remaining RS2/projective argument.  The proof is only wiring:
all substantive fields are discharged by existing theorems. -/
noncomputable def earlySchurFirstKeyContext
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt :
      C.firstActualLayerOrder <
        P.stationary.blocker.aligned.endpoint.defect) :
    AdaptiveAlignedSmithEarlySchurFirstKeyContext P C hlt := by
  have hfrontier :=
    C.relativeFirstActualDeformation_preclosing_hessianFrontier hlt
  exact {
    firstSpatialKey :=
      C.hasFirstTransverseSourceKey_of_positiveSupport
        (P.earlySchur_positiveTransverseSourceSupport C)
    firstActualPotential_ne_zero := C.firstActualLayerPotential_ne_zero
    rawRayPrefix := C.rawSchurRayPrefix
    lowerHessianZero := hfrontier.1
    firstActualHessian := hfrontier.2.1
    firstActualTangential := hfrontier.2.2
    polynomialKernel := C.exists_denominatorClearedSpecialSchurKernelData
  }

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

end

end HC4.Valuation
