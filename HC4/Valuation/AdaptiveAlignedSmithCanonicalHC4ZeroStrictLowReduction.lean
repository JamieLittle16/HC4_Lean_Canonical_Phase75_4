import HC4.Valuation.AdaptiveAlignedSmithCanonicalCollisionAutoDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import Mathlib.Tactic

/-!
# Unrestricted HC4 reduces directly to the concrete zero-clock strict-low blocker

For the public determinant-one problem the normalized collision entry has raw
Hessian defect exactly zero.  Its A18.4.109 rank-one trace therefore cannot
take a strict raw-defect restart: the original state itself already carries the
presented rank-three terminal.

At that raw-zero terminal there are only two possibilities relevant to the
final contradiction:

* no genuinely strict-low Smith pattern occurs, in which case the existing
  conformal degree-two one-zero argument is contradictory outright; or
* one of the three strict-low Smith patterns occurs.  A surviving endpoint
  excludes those patterns, so this case is necessarily a presented blocker
  and packages exactly as
  `AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData`.

Thus unrestricted HC4 needs only the impossibility of that concrete A19 local
object.  No positive Rees re-entry, positive-terminal obstruction producer,
JC2 endpoint, or additional global termination argument is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Direct zero-clock strict-low reduction for unrestricted HC4.**

Once every actual zero-clock strict-low blocker is contradictory, an arbitrary
determinant-one polynomial has injective gradient. -/
theorem
    gradient_injective_of_hessianDeterminant_one_of_zeroStrictLowTerminal_impossible
    (hstrict :
      ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
        AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
          (K := K) state → False)
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  intro p q hgrad
  by_contra hpq
  have hcoll : HasExactGradientCollision F p q := by
    intro i
    exact congrFun hgrad i
  let E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
    zeroDefectCollisionEntry_ofExactCollision_autoDegree
      F p q hdet hpq hcoll
  let state := E.toScaleAwareState 0
  let terminal :=
    E.presentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking 0
  have hrepair : state.repair = rankOneRepairState 0 := by
    rfl
  have hzero : state.rawDefect = 0 := by
    rfl
  by_cases hlow :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 terminal.specialFiber,
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e
  · rcases hlow with ⟨e, he, hpattern⟩
    cases hterm : terminal with
    | blocker D _geometry =>
        rw [hterm] at he
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
            AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
            using he
        exact hstrict {
          repair_eq := hrepair
          blocker := D
          source_zero := hzero
          exponent := e
          mem := he'
          pattern := hpattern
        }
    | surviving D _geometry =>
        rw [hterm] at he
        have he' :
            e ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber D.presented.family) := by
          simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
            AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
            using he
        rcases D.noStrictLow_on_specialFiber e he' with
          ⟨hnotPure, hnotFirst, hnotSecond⟩
        rcases hpattern with hpure | hfirst | hsecond
        · exact (hnotPure hpure).elim
        · exact (hnotFirst hfirst).elim
        · exact (hnotSecond hsecond).elim
  · have hno : terminal.HasNoStrictLowSmithPatterns := by
      intro e he
      constructor
      · intro hpure
        exact hlow ⟨e, he, Or.inl hpure⟩
      constructor
      · intro hfirst
        exact hlow ⟨e, he, Or.inr (Or.inl hfirst)⟩
      · intro hsecond
        exact hlow ⟨e, he, Or.inr (Or.inr hsecond)⟩
    exact
      (terminal.conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
        hzero hno).elim

end

end HC4.Valuation
