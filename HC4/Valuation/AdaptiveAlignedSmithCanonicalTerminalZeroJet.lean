import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSpecialFiberSplit
import Mathlib.Tactic

/-!
# A18.5.19: terminal represented families retain the canonical zero jet

A18.5.18 reduces every normalized terminal to an honest polynomial special
fibre with either zero clock or zero Hessian determinant.  The next Newton
step also needs the fact that this polynomial is not arbitrary: it is exactly
the special fibre of the canonical zero-source-jet family classified by the
aligned Smith dispatcher.

Both presented terminal constructors retain the original canonical endpoint,
and their `family_eq` fields identify that endpoint family with the represented
state family.  Hence zero source jet transports definitionally to
`T.presentedState.family`.

Specialising the parameter then gives precisely the normalized Smith axis data
used throughout the canonical wall theory: zero value and zero gradient at the
origin together with the exact marked collision from `0` to `e₀`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- The actual represented terminal family still has zero source jet. -/
theorem presentedState_zeroSourceJet
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    HasZeroSourceJet T.presentedState.family := by
  cases T with
  | blocker D geometry =>
      dsimp [presentedState]
      rw [← D.family_eq]
      exact D.blocker.aligned.zeroSourceJet
  | surviving D geometry =>
      dsimp [presentedState]
      rw [← D.family_eq]
      exact D.wall.aligned.zeroSourceJet

/-- The represented terminal special fibre carries the exact normalized axis
package consumed by the canonical Smith/Newton support machinery. -/
theorem specialFiber_axisData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    HasNormalizedSmithAxisData T.specialFiber := by
  have h :=
    T.presentedState_zeroSourceJet.specialFiber_axisData
      T.presentedState.movingSection
      T.presentedState.exactCollision
      T.presentedState.sectionSpecial
  simpa [specialFiber] using h

/-- The terminal fibre has nonempty Smith-projected support.  This is retained
from the actual symmetric-minimal aligned endpoint carried by either terminal
constructor; normalized axis data alone would not exclude the zero
polynomial. -/
theorem specialFiber_projectedSupport_nonempty
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber).Nonempty := by
  cases T with
  | blocker D geometry =>
      dsimp [specialFiber, presentedState]
      rw [← D.family_eq]
      simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
        D.blocker.aligned.endpoint.rawProjectedSupport_nonempty
  | surviving D geometry =>
      dsimp [specialFiber, presentedState]
      rw [← D.family_eq]
      simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
        D.wall.aligned.endpoint.rawProjectedSupport_nonempty

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation
