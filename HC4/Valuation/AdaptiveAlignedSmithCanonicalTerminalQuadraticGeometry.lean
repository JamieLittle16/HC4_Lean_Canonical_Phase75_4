import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalWallData
import HC4.Newton.MixedDegreeFirstWallCompetition
import HC4.Newton.SymmetricSmithMinimality
import Mathlib.Tactic

/-!
# A19.10: retain the full surviving geometry behind the terminal quadratic face

A18.5.21 deliberately exported only the final finite-support dichotomy needed
at that stage: a concrete blocker exponent, or a nonempty quadratic symmetric
Smith subface.  For the final JC2-facing weighted-initial argument we need one
piece of provenance which that interface intentionally forgot.

In the quadratic branch the *whole* projected support was first proved to have
the general surviving Smith-grade shape, with the `w`-linear zero-grade
pattern excluded.  Those facts imply that every supported monomial lies on
one side of the canonical symmetric Smith hyperplane.  The quadratic subface
is exactly the equality face.

This file reruns only that already-green finite classifier on the actual
terminal special fibre and retains those two certificates.  No new geometric
assumption is introduced and no polynomial is changed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Full provenance of the quadratic side of the canonical terminal Smith
classifier.  The last two fields are the A18.5.21 output; the first two retain
why that output was obtained. -/
structure AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry
    {RR : RepairRanking}
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) : Prop where
  survivingShape :
    HasGeneralSurvivingSmithFaceShape
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ))
  noWLinear :
    ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
      (fun _ : SmithSupportExponent => (0 : ℤ)) e = 0 →
        ¬ IsWLinearSmithPattern e
  balancedNonempty :
    (smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ))).Nonempty
  quadratic :
    ∀ e ∈ smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ)),
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- **Lossless terminal Smith support frontier.**

Either the actual terminal polynomial contains one of the four concrete
mixed-degree blocker patterns, or the complete surviving-face certificate is
retained together with the nonempty quadratic equality face. -/
theorem specialFiber_blocker_or_quadraticGeometry
    {RR : RepairRanking}
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome T.specialFiber e) ∨
      AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T := by
  have haxis := T.specialFiber_axisData
  have hwall := T.specialFiber_canonicalWallData
  rcases haxis with ⟨hcoll, hgrad, hvalue⟩
  rcases minimalSmithLevel_blockerOutcome_or_survivingFace
      T.specialFiber
      (fun _ : SmithSupportExponent => (0 : ℤ))
      0 hcoll hgrad hvalue with
    hblock | hsurviving
  · left
    rcases hblock with ⟨e, he, hlevel, hpattern, houtcome⟩
    exact ⟨e, he, hpattern, houtcome⟩
  · right
    rcases hsurviving with ⟨hshape, hnoW⟩
    have hquad :=
      symmetricSmithPoleMinimal_symmetricRefinement_quadratic
        (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
        0 (fun _ : SmithSupportExponent => (0 : ℤ))
        hwall.minimal hwall.lowerBound hwall.attained hshape hnoW
    exact {
      survivingShape := hshape
      noWLinear := hnoW
      balancedNonempty := hquad.1
      quadratic := hquad.2
    }

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation
