import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryDispatcher
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import Mathlib.Tactic

/-!
# Single local elimination interface for the final stationary blocker

The canonical dispatcher has now discharged every global alternative except
one stationary mixed-source obstruction.  This file closes the *architecture*
around that obstruction without assuming its elimination.

The stationary source already carries more than coarse mixedness.  Because it
is still the exact canonical blocker, the green exact-exponent machinery gives
one canonically minimal positive longitudinal departure over the blocker's own
unchanged projected Smith exponent.  We expose that fact directly on the
honest right-recentered family special fibre used by every surviving Schur and
rigid-packet branch.

We then package the stationary source and its local geometry tag as one
`AdaptiveAlignedSmithCanonicalStationaryLocalProblem`.  A single eliminator
for this type is sufficient to remove the final stationary constructor from
the global dispatcher.  Thus the remaining mathematical proof obligation has
one theorem boundary rather than five global branches.

No JC2, terminal-classification, homogeneity, or additional assumption is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalStationaryBlocker

/-- Exact same-Smith-exponent mixedness is still available on the stationary
blocker; it is stronger than the coarse mixed-degree pair stored for global
provenance. -/
theorem exactExponentMixedDegree
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber)
      S.blocker.exponent :=
  S.blocker.exactExponentMixedDegree

/-- Hence the stationary blocker contains a positive later longitudinal
layer over its *own unchanged* projected Smith exponent. -/
theorem positiveLongitudinalGap
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    HasExactSmithExponentPositiveLongitudinalGap
      (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber)
      S.blocker.exponent :=
  S.blocker.positiveLongitudinalGap

/-- Canonical least positive longitudinal departure retained by every
stationary blocker.  This is the strongest source-facing datum expected by
the final Schur/rigid elimination theorem. -/
theorem firstLongitudinalDeparture
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber)
      S.blocker.exponent :=
  S.blocker.firstLongitudinalDeparture

/-- The same first-departure statement on the literal special fibre of the
honest right-recentered polynomial family used by all five local geometries. -/
theorem familySpecialFiber_firstLongitudinalDeparture
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily)
      S.blocker.exponent := by
  rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
  exact S.firstLongitudinalDeparture

/-- The canonical departure supplies two actual occupied source monomials at
one exact transverse Smith exponent. -/
theorem firstLongitudinalDeparture_support_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    ∃ n q : ℕ,
      0 < q ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support :=
  S.familySpecialFiber_firstLongitudinalDeparture.support_pair

/-- The two canonical same-exponent layers have strictly different ordinary
source degree. -/
theorem firstLongitudinalDeparture_ordinaryDegree_strict
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    ∃ n q : ℕ,
      0 < q ∧
      HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) <
        HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) :=
  S.firstLongitudinalDeparture.ordinaryDegree_strict

end AdaptiveAlignedSmithCanonicalStationaryBlocker

/-- The *single* local problem left by the global adaptive proof.

All source-facing stationary data lives in `stationary`; `geometry` only
remembers which Schur/all-minors certificate is available to eliminate it. -/
structure AdaptiveAlignedSmithCanonicalStationaryLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalStationaryBlocker s
  geometry : AdaptiveAlignedSmithCanonicalStationaryGeometry stationary

namespace AdaptiveAlignedSmithCanonicalStationaryLocalProblem

/-- Every final local problem has the canonical first longitudinal departure
on its honest source special fibre. -/
theorem firstLongitudinalDeparture
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        P.stationary.blocker.aligned.endpoint.rightRecenteredFamily)
      P.stationary.blocker.exponent :=
  P.stationary.familySpecialFiber_firstLongitudinalDeparture

/-- Every final local problem also retains the all-transverse rational-zero
normal form. -/
theorem allTransverseZero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s) :
    AdaptiveRecenteredAllTransverseZeroRationalSlope P.stationary.blocker :=
  P.stationary.allTransverseZero

/-- And its honest source special fibre is genuinely nonhomogeneous. -/
theorem specialFiber_not_isHomogeneous
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s)
    (D : ℕ) :
    ¬ (polynomialFamilySpecialFiber
        P.stationary.blocker.aligned.endpoint.rightRecenteredFamily).IsHomogeneous D :=
  P.stationary.specialFiber_not_isHomogeneous D

end AdaptiveAlignedSmithCanonicalStationaryLocalProblem

/-- Fully resolved global adaptive outcome: the stationary constructor has
been removed. -/
inductive AdaptiveAlignedSmithCanonicalResolvedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

/-- Exact final local theorem interface.

Proving this proposition for a given source state is *precisely* enough to
remove every remaining Schur/rigid stationary geometry from the canonical
global dispatcher. -/
def AdaptiveAlignedSmithCanonicalStationaryElimination
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  ∀ P : AdaptiveAlignedSmithCanonicalStationaryLocalProblem s,
    AdaptiveAlignedSmithCanonicalResolvedOutcome RR s

/-- **Architecture closure theorem.**

Once the single stationary local elimination interface is supplied, the
canonical adaptive dispatcher has only strict fixed-scale progress, ordinary
adaptive re-entry, or literal zero defect.  No other global constructor
remains. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalResolvedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (helim : AdaptiveAlignedSmithCanonicalStationaryElimination RR s) :
    AdaptiveAlignedSmithCanonicalResolvedOutcome RR s := by
  rcases s.alignedSmithCanonicalStationaryDispatcher RR complexity hsrepair with
    hstrict | ⟨t⟩ | ⟨t, hzero⟩ | ⟨S, geometry⟩
  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact helim ⟨S, geometry⟩

end

end HC4.Valuation
