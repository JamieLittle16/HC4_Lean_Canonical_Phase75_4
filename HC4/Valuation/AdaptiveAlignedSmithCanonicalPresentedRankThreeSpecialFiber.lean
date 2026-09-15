import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.2: expose the terminal presented special-fibre collision

A18.5.1 removes the artificial distinction between exact and boundary-produced
rank-three terminals.  The next terminal arguments are polynomial arguments,
so they need the actual polynomial associated to the retained presented state,
not merely a Schur/Hessian wrapper.

Every presented terminal already carries a genuine scale-aware state.  Its
fields give

* the polynomial-parameter family;
* the moving marked section;
* an exact family-gradient collision from the zero section to that section;
* reduction of the moving section to the canonical marked axis point; and
* a certified pure presentation from the terminal trace state.

Specialising the parameter to zero therefore produces an honest
`MvPolynomial (Fin 4) K` with a distinct exact gradient collision.  This file
packages that fact uniformly for blocker and surviving terminals.

No homogeneity, terminal cocharacter, exponent-line, or rank-three rational
identity is asserted here.  Those must be extracted from the retained local
rank-three geometry in subsequent files.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- The actual scale-aware presented state underlying a normalized terminal. -/
noncomputable def presentedState
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  cases T with
  | blocker D _ => exact D.presented
  | surviving D _ => exact D.presented

/-- The represented state is connected to the terminal trace state by the
certified pure ramified presentation already stored in the endpoint. -/
noncomputable def sourcePresentation
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    HasCertifiedRamifiedEpisodeInternalMove T.presentedState source := by
  cases T with
  | blocker D _ => exact D.sourcePresentation
  | surviving D _ => exact D.sourcePresentation

/-- Polynomial special fibre of the actual represented terminal state. -/
noncomputable def specialFiber
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber T.presentedState.family

/-- The retained family collision descends to the canonical marked collision
on the represented terminal special fibre. -/
theorem specialFiber_exactCollision
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    HasExactGradientCollision
      T.specialFiber
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have h :=
    polynomialFamilyZeroCollision_specialFiber
      T.presentedState.family
      T.presentedState.movingSection
      T.presentedState.exactCollision
  rw [T.presentedState.sectionSpecial] at h
  simpa [specialFiber] using h

/-- The two marked special-fibre points are genuinely distinct. -/
theorem specialFiber_markedPoints_distinct
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (_T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    (fun _ : Fin 4 => (0 : K)) ≠
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simpa [coordinateAxisPoint] using h0

/-- Honest polynomial-level carrier for the next terminal extraction.  The
local rank-three geometry remains attached through `terminal`; the special
fibre and collision are named explicitly so downstream support arguments do
not need to reconstruct them independently in every terminal constructor. -/
structure SpecialFiberCollisionData
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  terminal : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
    RR source complexity
  fibre_eq :
    terminal.specialFiber =
      polynomialFamilySpecialFiber terminal.presentedState.family
  exactCollision :
    HasExactGradientCollision
      terminal.specialFiber
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  distinct :
    (fun _ : Fin 4 => (0 : K)) ≠
      coordinateAxisPoint (K := K) (0 : Fin 4)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove terminal.presentedState source

/-- Package the polynomial terminal data without adding hypotheses. -/
noncomputable def toSpecialFiberCollisionData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    SpecialFiberCollisionData RR source complexity where
  terminal := T
  fibre_eq := rfl
  exactCollision := T.specialFiber_exactCollision
  distinct := T.specialFiber_markedPoints_distinct
  sourcePresentation := T.sourcePresentation

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- A18.4.109 followed by A18.5.1--2 reaches an honest polynomial special
fibre carrying the marked exact collision.  This keeps the well-founded trace
itself as the source of the terminal state; no repair-only successor is used. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedSpecialFiberCollision
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.SpecialFiberCollisionData
      RR T.reachedPresentedRankThree.state complexity :=
  T.reachedPresentedRankThree.terminal.toSpecialFiberCollisionData

end

end HC4.Valuation
