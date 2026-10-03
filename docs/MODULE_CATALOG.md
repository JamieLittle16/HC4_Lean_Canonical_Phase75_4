# HC4 module catalog

This is the human-oriented module catalog. For an exhaustive row for **every Lean file**, run `python3 tools/generate_proof_inventory.py`; the generated index reads each file's own module docstring and declarations.

The catalog below explains the stable module families and the live final-assembly chains so that a filename can be placed in context before it is edited.

## Root aggregators and audits

- `HC4.lean` — cumulative root aggregator. It imports the established library plus explicit final-assembly theorem fronts so integration failures appear in CI.
- `HC4/Audit.lean` — proof/audit surface used for certification and theorem inspection.
- `HC4/MainAssembly.lean` — older classification-level assembly from already-classified gradient forms.
- `HC4/ClassifiedFamilies.lean`, `HC4/FacetRigidity.lean`, `HC4/LinearAlgebra.lean`, `HC4/MongeAmpere.lean`, `HC4/Newton.lean`, `HC4/Polynomial.lean`, `HC4/RationalRigidity.lean`, `HC4/Toric.lean` — subsystem aggregators where present.

## `HC4/Polynomial/`

This directory owns concrete polynomial representations and transformations. Look here first when a proof needs an identity about coefficients, support, initial forms, substitutions, or conversion to a one-variable model.

Important families:

- `FourExponent.lean` — four-variable exponent bridges, ordinary degree, toric facet support, `MvExponentOnBoundary`.
- `WeightedInitial.lean` and related weighted-initial modules — exact initial forms and coefficient/support identities.
- `Complementary*.lean` — complementary-line recognition, substitution, moment realization, and impossibility infrastructure.
- `RankThreeLine*.lean` / `RankThreeAffine*.lean` / `RankThreeVertical*.lean` — recognition and realization of rank-three support geometries.
- `RankThreeMv*.lean` — actual `MvPolynomial` bridges.
- `RankThreeWeighted*.lean` / `RankThreeBinomialPencilBridge.lean` / `RankThreeFractionMomentBridge.lean` — weighted pencil and moment interfaces.
- `AutonomousODERootFactorisation.lean`, `AutonomousODERootMultiplicity.lean` — univariate autonomous-ODE algebra used by RationalRigidity.

Rule of thumb: a theorem that reconstructs or recognizes the **polynomial itself** belongs here; a theorem that derives a terminal contradiction from the reconstructed data belongs in RationalRigidity.

## `HC4/Toric/`

This directory owns toric exponent arithmetic and combinatorics:

- facets and facet adjacency;
- boundary cycles and extreme rays;
- balanced exponent normal forms;
- exceptional grading arithmetic;
- symmetric Smith/toric support combinatorics.

Do not reimplement facet coordinate cases in a downstream Valuation file if a Toric or `Polynomial/FourExponent` bridge already exposes them.

## `HC4/Newton/`

This directory owns finite-support geometry, exact exposed faces, first-contact selection, boundary strata, and local Hessian/Schur geometry.

### Generic boundary/exposure layer

- `InteriorVertex.lean` — nonlinear exposed monomial of a zero-Hessian polynomial lies on the coordinate boundary.
- `FiniteSupportExposedVertex.lean` — repeated coordinate-max exact exposure.
- `FiniteSupportSingularBoundaryVertex.lean` — singular nonlinear boundary-vertex carrier.
- `MvBoundaryStrata.lean` — `MvRankThreeOnFacet` and balanced multivariate boundary strata.
- `SingularBoundaryRankSplit.lean` — balance-free rank-three/codimension-two split.
- `PositiveCoordinateSingularBoundaryVertex.lean` — force an exposed boundary exponent to retain positivity of a chosen coordinate.

### First-contact layer

- `FirstContactAffinePlane.lean`
- `FirstContactHonestSlice.lean`
- `FirstContactNonlinearSupport.lean`
- `FirstNonfacetContact.lean`
- `FirstNonfacetLowDegreeSquareSplit.lean`

These select honest support faces and expose the source conditions needed by later cross-facet geometry.

### Cross-facet layer

- `FiniteSupportCrossFacetExposure.lean` — canonical two-sided exact cross-facet carrier.
- `FirstContactCrossFacetCarrier.lean` — first-contact-specific carrier bridge.
- `FirstContactCrossFacetAffineLine.lean` — older **balanced** affine-line recognition.
- `FiniteSupportCrossFacetRay.lean` — newer **balance-free** affine-ray extraction by three finite exposures.
- `FiniteSupportCrossFacetRayAffineRR.lean` — bridge from the balance-free ray toward affine RationalRigidity data where applicable.
- `FirstContactCrossFacetEndpointStratum.lean`, `...EndpointTransition.lean`, `...Exit.lean`, `...Arithmetic.lean` — endpoint and transition adapters.

### Affine RationalRigidity adapters

The `FirstContactCrossFacetAffineRR*.lean` family progressively packages the exact affine scalar/reconstruction/two-fixed data needed by RationalRigidity:

- `FirstContactCrossFacetAffineRR.lean`
- `FirstContactCrossFacetAffineRRReconstruction.lean`
- `FirstContactCrossFacetAffineRRTerminal.lean`
- `FirstContactCrossFacetAffineRRTerminalScalarData.lean`
- `FirstContactCrossFacetAffineRRTwoFixedCertificate.lean`
- `FirstContactCrossFacetAffineRRTwoFixedElimination.lean`
- `FirstContactCrossFacetAffineRRFiniteSplit.lean`
- `FirstContactCrossFacetAffineRRTransition.lean`
- `FirstContactCrossFacetAffineRRImpossible.lean`

### General block/Schur layer

- `GeneralFourBlock.lean`
- `GeneralThreeBlockScalarSchur.lean`
- `GeneralThreeBlockSecondScalarSchur.lean`
- `ScalarPivotThreeSchur.lean`
- `ScalarPivotThreeSchurClock.lean`

These are generic local Hessian/Schur decompositions. Reuse them rather than re-expanding block determinants in an A19 adapter.

### Two-zero / planar layer

- `TwoZeroDoublingHessianSquareGeneral.lean`
- `TerminalTwoZeroDoublingForm.lean`
- `TerminalTwoZeroPlanarCollision.lean`

These bridge two-zero terminal geometry toward planar collision/JC2-style interfaces. They are separate from the balance-free cross-facet ray route.

## `HC4/RationalRigidity/`

This directory owns the deep rank-three terminal algebra. Its modules generally move from support geometry to rigid univariate/projective data and finally contradiction.

Major families:

### Balanced homogeneous route

- `RankThreeBalancedHomogeneousDirection.lean`
- `RankThreeBalancedHomogeneousEdge.lean`
- `RankThreeBalancedHomogeneousEndpoint.lean`
- `RankThreeBalancedHomogeneousEndpointFacet.lean`
- `RankThreeBalancedHomogeneousDirectionDegeneracy.lean`
- `RankThreeBalancedDegreeOneImpossible.lean`
- `RankThreeBalancedHomogeneousImpossible.lean`

### Direction / endpoint refinement

- `RankThreeHighestDirectionRelation.lean`
- `RankThreeHomogeneousDirectionFixed.lean`
- `RankThreeHomogeneousQFixedRelation.lean`
- `RankThreeHomogeneousOtherFixedRelations.lean`
- `RankThreeHomogeneousEndpointUnits.lean`
- `RankThreeEndpointNondegeneracy.lean`
- `RankThreePrimitiveEndpointShape.lean`
- `RankThreePrimitiveStep.lean`
- `RankThreeSingleDirectionRefinement.lean`

### Supported / binomial terminal route

- `RankThreeSupportedDirectionSplit.lean`
- `RankThreeSupportedSingleDirectionRefinement.lean`
- `RankThreeSupportedEndpointBoundary.lean`
- `RankThreeSupportedEndpointStratum.lean`
- `RankThreeSupportedBinomialPower.lean`
- `RankThreeSupportedEdgeTerminal.lean`
- `RankThreeTerminalBinomialNormalForm.lean`
- `RankThreeTerminalDirectionSplit.lean`
- `RankThreeTerminalFacetTransition.lean`
- `RankThreeUnshiftedBinomialForm.lean`
- `RankThreeTranslatedPurePower.lean`

### Affine route

- `RankThreeAffineLineTerminal.lean`
- `RankThreeAffineTopBoundary.lean`
- `RankThreeAffineTerminalBoundaryStratum.lean`
- `RankThreeAffineTerminalNormalForm.lean`
- `RankThreeAffineTerminalScalarData.lean`
- `RankThreeAffineTwoFixedEqualitiesImpossible.lean`
- `RankThreeAffineTwoFixedImpossible.lean`

### Autonomous-polynomial / root route

- `PolynomialAutonomousClearing.lean`
- `PolynomialAutonomousQuadraticExtraction.lean`
- `RankThreeRootMultiplicity.lean`

### Vertical route

- `RankThreeVerticalLineTerminal.lean`
- `RankThreeVerticalContradiction.lean`

Valuation and Newton assembly files should terminate by packaging the exact inputs for these modules, not by cloning their algebra.

## `HC4/Valuation/`

This is the largest subsystem. It owns the evolving scale-aware state, Smith/Schur geometry, repair state, Rees operations, global progress, provenance, and final assembly.

The filename prefixes encode the intended refinement. Read them from left to right:

```text
AdaptiveAlignedSmith
  Canonical
    [state/geometry qualifier]
      [local operation]
        [frontier/reduction/closure/terminal]
```

A `...Data` or carrier file usually retains witnesses. A `...Frontier` or `...Split` performs an exhaustive classification. A `...Reduction` turns one obligation into smaller named obligations. A `...Closure` or `...Impossible` should discharge a branch.

### Established state / Smith / restart foundation

The older Valuation tree contains the reusable state-machine foundation, including:

- `AdaptiveGeometricRestartState.lean`
- `ScaledDefect.lean`
- adaptive diagonal/rigid/rank-two/Smith wall exposure;
- degree-two kernel restart/activity/saturation;
- integral kernel restart and exact defect drop;
- parameter ramification and common-parameter-factor restart;
- Smith endpoint/minimality/first-stop machinery;
- separated/coupled wall closure;
- pointed shear continuation;
- lossless frontier and defect-retaining departure machinery.

New final-assembly files should import these owners instead of creating new “state” or “progress” notions.

### Schur / kernel-opening / stationary local machinery

Families with names such as:

- `...KernelOpening...`
- `...ZeroSchur...`
- `...ScalarZeroSchur...`
- `...StationaryPlanarCoreFinalAssembly...`
- `...PresentedKernel...`
- `...SurvivingKernel...`

encode the already-developed local rank and Schur-analysis infrastructure. Search these families before adding any new “first kernel”, “zero Schur”, “scalar pivot”, or stationary mixed-layer theorem.

### Presented blocker / rank-three closure machinery

The `AdaptiveAlignedSmithCanonicalPresented*.lean` family owns the canonical presented blocker and its geometry:

- blocker construction and first departure;
- rank-three special fibre/terminal;
- kernel and surviving branches;
- complete rank-three closure;
- lossless rank-two / positive-slope rank-two alternatives.

Terminal A19 adapters should keep the actual presented blocker rather than reproduce its facts manually.

### Global termination / trace machinery

Core files:

- `AdaptiveAlignedSmithCanonicalAlignedRankThreeOrProgress.lean`
- `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean`
- `AdaptiveAlignedSmithCanonicalRankOneGlobalSuccessor.lean`
- `AdaptiveAlignedSmithCanonicalGlobalTerminationFrontier.lean`
- `AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean`

This is the global rank-one architecture. `rawDefect` is the recursion measure.

### Positive Rees family

The `AdaptiveAlignedSmithCanonicalPositiveTransverseRees*.lean` modules own coefficient bounds, section transport, unramified restart/progress, source adaptation, low layers, and collisions.

The assembly that integrates successful Rees steps into the existing trace is:

- `AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`.

### Unrestricted/reachable HC4 reduction layer

- `AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`
- `AdaptiveAlignedSmithCanonicalCollisionAutoDegree.lean`
- `AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean`
- `AdaptiveAlignedSmithCanonicalHC4Reduction.lean`
- `AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean`
- `AdaptiveAlignedSmithCanonicalFinalResidualReduction.lean`
- `AdaptiveAlignedSmithCanonicalFinalResidualConstructorRefinement.lean`
- `AdaptiveAlignedSmithCanonicalFinalResidualConstructorReduction.lean`

These are reductions/assembly, not foundational geometry owners.

### Producer-free zero strict-low chain

The active local chain is:

```text
ZeroStrictLowBlocker
  -> ZeroStrictLowResidualNormalForm       (A19.49)
  -> ZeroStrictLowMixedDegree              (A19.50)
  -> ZeroStrictLowZeroClockPacket          (A19.51)
  -> ZeroStrictLowFirstContactHessian      (A19.52)
  -> RankOneReesZeroStrictLowTerminal      (A19.53)
  -> ZeroStrictLowSingularTerminal         (A19.54)
  -> ZeroStrictLowBoundaryFrontier         (A19.55)
  -> ZeroStrictLowBoundaryStrata           (A19.56)
  -> ZeroStrictLowRecenteredOutsideSupport (A19.57)
  -> ZeroStrictLowRankThreeFacetSplit      (A19.58)
  -> ZeroStrictLowFirstNonfacetSource      (A19.59)
  -> ZeroStrictLowRankThreeSourceSplit     (A19.60)
  -> ZeroStrictLowResidualSupport          (A19.61)
  -> ZeroStrictLowConfinementFacetElimination (A19.62)
  -> ZeroStrictLowPureResidualSupport      (A19.63)
  -> ZeroStrictLowConfinementPatternSplit  (A19.64)
  -> FirstNonfacetLowDegreeSquareSplit     (A19.65, Newton)
  -> ZeroStrictLowFirstNonfacetCrossFacet  (A19.66)
  -> FiniteSupportCrossFacetRay            (A19.67, Newton)
  -> PositiveCoordinateSingularBoundaryVertex
     + ZeroStrictLowBalanceFreeRayBoundary (A19.68)
  -> ZeroStrictLowCrossFacetBoundaryTransition (A19.69)
  -> ZeroStrictLowRankThreeBoundaryReduction   (A19.70)
```

This ordering is the quickest way to determine whether a proposed “new” lemma has already appeared under a more precise carrier name.

## `HC4/ClassifiedFamilies/`

Owns explicit classified gradient families and their inverses/conjugacies:

- branch conjugacy;
- classified equivalences;
- facet assembly;
- polynomial endpoints;
- triangular inverses.

This is downstream of obtaining a classified form; it is not the current source of the unrestricted terminal geometry.

## `HC4/FacetRigidity/`

Older facet rigidity algebra, including Euler and leading-coefficient identities. Search here before adding another Euler/leading-term calculation to a terminal adapter.

## `HC4/LinearAlgebra/`

Generic congruence/unitriangular block identities and other matrix-level infrastructure. Keep representation-independent matrix algebra here rather than in a specific Smith episode.

## `HC4/MongeAmpere/`

Owns the polynomial Monge–Ampère/Hessian determinant interfaces. A Valuation module should prove that its actual carrier satisfies the established Monge–Ampère predicate and then reuse this layer.

## `HC4/QuasiTranslation/`

Quasi-translation and gradient-map structural infrastructure retained from earlier proof layers.

## Planar / JC2 bridge modules

- `HC4/PlanarJC2HessianEmbedding.lean`
- `HC4/Newton/TerminalTwoZeroPlanarCollision.lean`
- `HC4/Valuation/AdaptiveAlignedSmithFirstContactTwoZeroJC2.lean`
- `HC4/Valuation/AdaptiveAlignedSmithCanonicalFirstContactPlanarCollision.lean`
- `...FirstContactPlanarEquivalence.lean`
- `...FinalPlanarJC2Frontier.lean`
- `...JC2HC4Assembly.lean`

These form a planar/JC2-capable route. They should not be confused with the current balance-free zero strict-low cross-facet route. Use them only when the proof has genuinely reached their two-zero/planar hypotheses.

## Historical phase status files

Root files named `FORMALISATION_STATUS_PHASE*.md`, the old `FORMALISATION_LEDGER.md`, and old `CERTIFICATION_STATUS.md` record historical snapshots. They are useful for archaeology but not for deciding current ownership or current residual obligations.

The live navigation sources are:

- this catalog;
- `PROOF_ARCHITECTURE.md`;
- `CANONICAL_OWNERS.md`;
- the generated module/declaration indexes;
- the Lean source itself.