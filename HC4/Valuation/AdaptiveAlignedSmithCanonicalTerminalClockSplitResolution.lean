import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableJC2Resolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeSpecialFiber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionTransport
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import HC4.MongeAmpere

/-!
# A19.10: split the final terminal resolver by the represented determinant clock

The mixed A19.7 resolver still allowed the JC2 branch to manufacture an
unrelated associated-graded polynomial.  The actual terminal geometry is
sharper.

At positive represented raw defect the presented special fibre is
Hessian-singular, so this is the unconditional A18 polynomial-obstruction
side.

At represented raw defect zero the *same* presented special fibre already has
Hessian determinant one.  A18.5.2 also gives its canonical distinct exact
collision `0 ~ e₀`.  Hence the JC2-facing branch does not need to extract a new
polynomial or new collision at all: it only has to certify this existing
Monge--Ampere fibre as one of the terminal direct-jump endpoint types.

This is a strict strengthening of the semantic reduction.  No cocharacter or
endpoint certificate is asserted here; the remaining zero-clock producer must
construct it from the retained terminal geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- Positive represented raw defect makes the actual terminal special fibre
Hessian-singular. -/
theorem specialFiber_hessian_zero_of_presentedRawDefect_pos
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hpos : 0 < T.presentedState.rawDefect) :
    HC4.Polynomial.hessianDeterminant T.specialFiber = 0 := by
  simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber] using
    T.presentedState.specialFiber_hessianDeterminant_eq_zero hpos

/-- At represented raw defect zero the actual terminal special fibre is already
an honest polynomial Monge--Ampere solution. -/
theorem specialFiber_mongeAmpere_of_presentedRawDefect_zero
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hzero : T.presentedState.rawDefect = 0) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere T.specialFiber := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
  unfold AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := T.presentedState.hessianDefect
  rw [hzero] at hdef
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  simp

/-- Once the existing zero-clock special fibre has a terminal endpoint
certificate, all remaining associated-graded collision fields are already
present in A18.5.2. -/
noncomputable def toAssociatedGradedCollisionData_of_specialFiberEndpoint
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (endpoint : CertifiedTerminalDirectJumpEndpoint T.specialFiber) :
    TerminalAssociatedGradedCollisionData K where
  fibre := T.specialFiber
  leftPoint := fun _ : Fin 4 => (0 : K)
  rightPoint := coordinateAxisPoint (K := K) (0 : Fin 4)
  distinct := T.specialFiber_markedPoints_distinct
  exactCollision := T.specialFiber_exactCollision
  endpoint := endpoint

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- Exact producer obligations after splitting by the represented terminal
clock.  JC2 is needed only on the literal zero-clock Monge--Ampere fibre;
positive-clock terminals must close by an already-verified unconditional A18
polynomial obstruction. -/
structure AdaptiveAlignedSmithCanonicalTerminalClockSplitProducer where
  positive :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpos : 0 < T.presentedState.rawDefect),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  zero :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hzero : T.presentedState.rawDefect = 0),
      CertifiedTerminalDirectJumpEndpoint T.specialFiber

/-- A clock-split producer gives the exact mixed reachable resolver of A19.7.
The zero branch uses the represented special fibre itself; no new polynomial
is selected. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalTerminalClockSplitProducer.toReachableResolution
    (P : AdaptiveAlignedSmithCanonicalTerminalClockSplitProducer (K := K)) :
    AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K) := by
  intro state hclock T
  by_cases hzero : T.presentedState.rawDefect = 0
  · let endpoint := P.zero hclock T hzero
    exact ⟨.associatedGradedCollision
      (T.toAssociatedGradedCollisionData_of_specialFiberEndpoint endpoint)⟩
  · have hpos : 0 < T.presentedState.rawDefect := Nat.pos_of_ne_zero hzero
    rcases P.positive hclock T hpos with ⟨O⟩
    exact ⟨.polynomialObstruction O⟩

/-- **Clock-split `JC2 => HC4` reduction.**

It is enough to close positive represented terminals unconditionally and to
classify only the actual zero-clock terminal special fibre by the existing JC2
endpoint library. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_terminalClockSplitProducer
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalTerminalClockSplitProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_JC2_of_reachableResolution
      hJC2 P.toReachableResolution F hdet

end

end HC4.Valuation
