import HC4.Valuation.ScaleAwareAdaptiveAlignedSmithEndpoint
import HC4.Valuation.CanonicalAdaptiveSmithWall

/-!
# Aligned-Smith minimal endpoint as an attained canonical wall

The one-shot aligned-Smith macro already returns a genuinely symmetric-minimal
raw special fibre.  `IsSymmetricSmithPoleMinimal` is non-vacuous: it contains
an actual projected-support witness.  Hence the zero-base, zero-level
canonical wall is attained immediately.

This file packages that fact without performing a second zero-jet
normalisation.  The remaining adapter obligation for the final classifier is
only the normalized-axis data on this raw special fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The raw special fibre carried by an aligned-Smith minimal endpoint. -/
def AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber E.family

/-- Symmetric minimality already supplies a genuine projected-support
witness; in particular the endpoint cannot be vacuously minimal. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rawProjectedSupport_nonempty
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    (smithProjectedSupport
      (1 : Fin 4) 2 3 E.rawSpecialFiber).Nonempty := by
  rcases E.symmetricMinimal with ⟨e, he, _hle⟩
  exact ⟨e, he⟩

/-- Every aligned-Smith minimal endpoint carries the canonical integral wall
on its raw special fibre, with actual attainment.

No support transport and no second normalization are used here. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.canonicalWallData
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    CanonicalAdaptiveSmithWallData E.rawSpecialFiber := by
  refine
    { minimal := ?_
      attained := ?_ }
  · simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
      E.symmetricMinimal
  · rcases E.symmetricMinimal with ⟨e, he, _hle⟩
    refine ⟨e, ?_, rfl⟩
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using he

/-- Dispatcher-facing packaging of a scale-aware aligned-Smith step:
either the macro reaches a raw special fibre carrying an attained canonical
wall, or it reaches an actual aligned section boundary.

This is still geometry-only assembly: no global progress relation is
introduced. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalWall_or_sectionBoundary
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (∃ E : AdaptiveAlignedSmithMinimalEndpoint (K := K) s.degreeCap,
        CanonicalAdaptiveSmithWallData E.rawSpecialFiber) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  rcases s.alignedSmithEndpoint with hmin | hboundary
  · left
    rcases hmin with ⟨E⟩
    exact ⟨E, E.canonicalWallData⟩
  · exact Or.inr hboundary

end

end HC4.Valuation
