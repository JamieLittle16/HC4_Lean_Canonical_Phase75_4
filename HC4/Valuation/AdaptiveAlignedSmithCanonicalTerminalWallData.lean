import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalZeroJet
import HC4.Valuation.AdaptiveAlignedSmithMinimalWall
import Mathlib.Tactic

/-!
# A18.5.20: the terminal special fibre is still the canonical Smith wall fibre

A18.5.19 showed that every normalized presented terminal retains zero source
jet and hence the normalized Smith-axis collision data.  The stronger fact
needed by the final Newton consumer is that the polynomial itself has not
changed since the canonical aligned-Smith endpoint was classified.

Both presented endpoint records carry the exact family equality

    aligned.endpoint.family = presented.family.

Therefore the terminal `specialFiber` is literally the raw special fibre of
the retained aligned endpoint.  In particular it inherits the already-proved
`CanonicalAdaptiveSmithWallData`: symmetric pole minimality, finite attainment,
and the canonical zero Smith level are not reconstructed downstream.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- The terminal polynomial is exactly the raw special fibre of the aligned
minimal endpoint retained by its blocker/surviving presentation. -/
theorem specialFiber_eq_alignedRawSpecialFiber
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    ∃ E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
        (K := K) T.presentedState.degreeCap,
      T.specialFiber = E.endpoint.rawSpecialFiber := by
  cases T with
  | blocker D geometry =>
      refine ⟨D.blocker.aligned, ?_⟩
      simp [specialFiber, presentedState,
        AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
        D.family_eq]
  | surviving D geometry =>
      refine ⟨D.wall.aligned, ?_⟩
      simp [specialFiber, presentedState,
        AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
        D.family_eq]

/-- The canonical Smith wall data survives unchanged on the actual terminal
special fibre. -/
theorem specialFiber_canonicalWallData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    CanonicalAdaptiveSmithWallData T.specialFiber := by
  cases T with
  | blocker D geometry =>
      have h := D.blocker.aligned.endpoint.canonicalWallData
      simpa [specialFiber, presentedState,
        AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
        D.family_eq] using h
  | surviving D geometry =>
      have h := D.wall.aligned.endpoint.canonicalWallData
      simpa [specialFiber, presentedState,
        AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
        D.family_eq] using h

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation
