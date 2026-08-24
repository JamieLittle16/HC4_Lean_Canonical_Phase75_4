import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurRS2ProjectiveWitnessReduction
import Mathlib.Tactic

/-!
# Stage 4B30: retain the Stage-3 Schur-kernel provenance through the first-key descent

B29 isolates the final scalar RS2 provenance theorem in terms of a particular
Stage-3 denominator-cleared Schur kernel `E`.  The source-side first-key
classification from B8--B28 is also ultimately built from such a kernel, but
the old existential assembly forgot *which* `E` was used when it chose a
source-coordinate kernel.

That loss is harmless for existence statements, but it is not harmless for
the final projective-motion theorem: a projective wedge of `E.fullVector` must
be compared with the first spatial key extracted from the source-coordinate
transport of the very same `E`.

This file restores that provenance without adding geometry.

For a fixed denominator-cleared Schur kernel `E` we transport it through the
already-green chain

    E.fullVector
      -> coordinateSpecialKernelData
      -> sourceCoordinateSpecialKernelData
      -> shifted first-key leading vector
      -> maximal homogeneous first-key kernel.

The resulting canonical RS2 assembly remembers the equality identifying its
source kernel with the transport of `E`.  Consequently the next theorem can
work with one coherent object: its projective Schur kernel, its source kernel,
and its `x₀^e L^m` first key all have literal common provenance.

No parameter order is identified with a spatial first-key order here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- The literal source-coordinate special-Hessian kernel obtained from one
specified Stage-3 denominator-cleared Schur kernel.  This merely composes the
already-green B6 and B7 coordinate transports. -/
noncomputable def sourceCoordinateData
    (E : C.DenominatorClearedSpecialSchurKernelData) :
    C.SourceCoordinateSpecialKernelData :=
  E.toCoordinateSpecialKernelData.toSourceCoordinateSpecialKernelData

end DenominatorClearedSpecialSchurKernelData

/-- Provenance-preserving form of B8.

Unlike `HasFirstTransverseSourceKey.exists_leadingTransverseKernelData`, this
statement starts from a *specified* denominator-cleared Schur kernel `E` and
records that the B8 source kernel is exactly the source-coordinate transport
of that `E`. -/
theorem HasFirstTransverseSourceKey.exists_leadingTransverseKernelData_of_schurKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey)
    (E : C.DenominatorClearedSpecialSchurKernelData) :
    ∃ L : C.FirstKeyLeadingTransverseKernelData,
      L.sourceKernel = E.sourceCoordinateData := by
  rcases hkey with ⟨hpos, hmpos, hQne, hQhom, hQhessian⟩
  let S : C.SourceCoordinateSpecialKernelData := E.sourceCoordinateData
  let V := shiftedSourceVectorLeading S.vector S.vector_ne_zero
  refine ⟨{
    hpos := hpos
    sourceKernel := S
    leadingVector := V
    leading_eq := rfl
    leading_ne_zero := ?_
    transverseKernel := ?_
  }, rfl⟩
  · simpa [V] using
      shiftedSourceVectorLeading_ne_zero S.vector S.vector_ne_zero
  · intro i
    dsimp [V]
    exact
      firstPositiveTransverseKey_transverseRows_kernel
        (polynomialFamilySpecialFiber C.family)
        hpos S.vector S.vector_ne_zero S.kernel i

/-- Complete first-key canonical assembly with the Stage-3 Schur kernel that
actually generated it retained as data. -/
structure FirstKeyCanonicalRS2ProvenanceAssemblyData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  schurKernel : C.DenominatorClearedSpecialSchurKernelData
  leading : C.FirstKeyLeadingTransverseKernelData
  sourceKernel_eq : leading.sourceKernel = schurKernel.sourceCoordinateData
  canonical : C.FirstKeyCanonicalMaximalHomogeneousKernelData leading
  factor : C.FirstKeyMaximalVectorLongitudinalFactorData leading

/-- The B28 canonical source assembly can be reconstructed from any specified
Stage-3 Schur kernel while retaining literal provenance all the way to the
source-coordinate B8 kernel. -/
theorem HasFirstTransverseSourceKey.exists_canonicalRS2ProvenanceAssemblyData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey)
    (E : C.DenominatorClearedSpecialSchurKernelData) :
    Nonempty C.FirstKeyCanonicalRS2ProvenanceAssemblyData := by
  rcases hkey.exists_leadingTransverseKernelData_of_schurKernel E with
    ⟨L, hsource⟩
  rcases L.exists_canonicalMaximalHomogeneousKernelData with ⟨D⟩
  rcases L.exists_longitudinalFactorData_unconditional with ⟨F⟩
  exact ⟨{
    schurKernel := E
    leading := L
    sourceKernel_eq := hsource
    canonical := D
    factor := F
  }⟩

/-- The total B28 source frontier remains unchanged after restoring Schur
kernel provenance. -/
theorem FirstKeyCanonicalRS2ProvenanceAssemblyData.rankTwoRepair_or_rs2Ready
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData)
    (complexity : ℕ) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData A.canonical complexity) ∨
      Nonempty (C.FirstKeyXeLmRS2ReadyData A.canonical) := by
  exact A.canonical.rankTwoRepair_or_rs2Ready A.factor complexity

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- The full early-Schur context now reaches a canonical first-key assembly
whose Stage-3 polynomial kernel is the same kernel from which its source-side
leading vector was extracted. -/
theorem AdaptiveAlignedSmithEarlySchurFirstKeyContext.exists_canonicalRS2ProvenanceAssemblyData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s}
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker}
    {hlt :
      C.firstActualLayerOrder <
        P.stationary.blocker.aligned.endpoint.defect}
    (X : AdaptiveAlignedSmithEarlySchurFirstKeyContext P C hlt) :
    Nonempty C.FirstKeyCanonicalRS2ProvenanceAssemblyData := by
  rcases X.polynomialKernel with ⟨E⟩
  exact X.firstSpatialKey.exists_canonicalRS2ProvenanceAssemblyData E

end

end HC4.Valuation
