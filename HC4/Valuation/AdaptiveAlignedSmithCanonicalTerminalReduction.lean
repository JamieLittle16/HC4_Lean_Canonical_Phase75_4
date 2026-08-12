import HC4.Valuation.AdaptiveAlignedSmithCanonicalProvenanceDispatcher
import HC4.Newton.TerminalAssociatedGradedEndpoint
import Mathlib.Tactic

/-!
# Final terminal reduction for the lossless adaptive Smith dispatcher

All local Smith geometry and the entire surviving-wall branch have already
been consumed by the green lossless canonical dispatcher.  The only residual
objects are blocker-originated closing/rigid endpoints carrying enough source
provenance for an actual associated-graded extraction.

This file isolates the genuinely remaining mathematics in two steps.

1. A `AdaptiveAlignedSmithCanonicalTerminalExtraction` is the exact
   polynomial-level extraction still required from each of the four residual
   blocker outputs.  It must produce an *actual* terminal associated-graded
   collision; no Schur matrix is identified with a polynomial potential.

2. Once such a polynomial terminal datum exists, JC2 is not needed in the
   scalar or strictly-positive terminal cases.  A surviving distinct exact
   collision is forced into exactly the one-zero / two-zero endpoint class.

Thus any remaining JC2 dependence is now sharply confined to those two
terminal weight types.  In particular, eliminating them from the specific
adaptive closing extraction would make the final endpoint argument JC2-free.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The two terminal endpoint families whose current injectivity theorems
still use planar JC2.  Strictly-positive and scalar terminal endpoints are
*not* included here because they are already injective unconditionally. -/
inductive CertifiedJC2SensitiveTerminalEndpoint
    (F : MvPolynomial (Fin 4) K) : Prop
  | oneZero
      (d a : ℤ)
      (ha : 0 < a)
      (had : a < d)
      (hhom :
        IsIntegralWeightedHomogeneous
          (standardOneZeroTerminalWeight d a) d F)
      (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
      CertifiedJC2SensitiveTerminalEndpoint F
  | twoZero
      (d : ℤ)
      (hd : 0 < d)
      (hhom :
        IsIntegralWeightedHomogeneous
          (standardTwoZeroTerminalWeight d) d F)
      (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
      CertifiedJC2SensitiveTerminalEndpoint F

/-- Exact collision datum for the only terminal endpoint types not yet
closed unconditionally.  The endpoint may occur after a coordinate
permutation, exactly as in `CertifiedTerminalDirectJumpEndpoint`. -/
structure JC2SensitiveTerminalCollisionData
    (K : Type*) [Field K] where
  fibre : MvPolynomial (Fin 4) K
  leftPoint : Fin 4 -> K
  rightPoint : Fin 4 -> K
  distinct : leftPoint ≠ rightPoint
  exactCollision : HasExactGradientCollision fibre leftPoint rightPoint
  rho : Equiv.Perm (Fin 4)
  endpoint :
    CertifiedJC2SensitiveTerminalEndpoint
      (MvPolynomial.rename rho fibre)

/-- A certified direct terminal jump with a surviving distinct exact
collision is either already contradictory without JC2, or belongs to the
one-zero/two-zero class.  Hence the latter class is the complete residual
terminal obstruction. -/
theorem TerminalAssociatedGradedCollisionData.exists_jc2Sensitive
    [CharZero K]
    (T : TerminalAssociatedGradedCollisionData K) :
    Nonempty (JC2SensitiveTerminalCollisionData K) := by
  cases T.endpoint with
  | scalar lambda d hscalar hnontrivial hhom hdet =>
      have hinj : Function.Injective (mvGradientMap T.fibre) :=
        scalarTerminal_actualHessian_gradient_injective
          hscalar hnontrivial hhom hdet
      exact False.elim
        (exactGradientCollision_impossible_of_injective
          T.fibre T.leftPoint T.rightPoint T.distinct
          hinj T.exactCollision)
  | permuted rho hendpoint =>
      cases hendpoint with
      | positive lambda d hface hpos =>
          have hinjRenamed :
              Function.Injective
                (mvGradientMap (MvPolynomial.rename rho T.fibre)) :=
            positiveTerminalFace_gradient_injective hface hpos
          have hinj : Function.Injective (mvGradientMap T.fibre) :=
            mvGradientMap_injective_of_rename_perm
              rho T.fibre hinjRenamed
          exact False.elim
            (exactGradientCollision_impossible_of_injective
              T.fibre T.leftPoint T.rightPoint T.distinct
              hinj T.exactCollision)
      | oneZero d a ha had hhom hMA =>
          exact ⟨{
            fibre := T.fibre
            leftPoint := T.leftPoint
            rightPoint := T.rightPoint
            distinct := T.distinct
            exactCollision := T.exactCollision
            rho := rho
            endpoint := .oneZero d a ha had hhom hMA }⟩
      | twoZero d hd hhom hMA =>
          exact ⟨{
            fibre := T.fibre
            leftPoint := T.leftPoint
            rightPoint := T.rightPoint
            distinct := T.distinct
            exactCollision := T.exactCollision
            rho := rho
            endpoint := .twoZero d hd hhom hMA }⟩

/-- Under planar JC2, even the final one-zero/two-zero residual collision is
impossible.  Notice that JC2 enters *only* here in this reduction. -/
theorem JC2SensitiveTerminalCollisionData.impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (T : JC2SensitiveTerminalCollisionData K) :
    False := by
  have hinjRenamed :
      Function.Injective
        (mvGradientMap (MvPolynomial.rename T.rho T.fibre)) := by
    cases T.endpoint with
    | oneZero d a ha had hhom hMA =>
        exact
          standardOneZero_terminal_gradient_injective_of_JC2
            hJC2 ha had hhom hMA
    | twoZero d hd hhom hMA =>
        exact
          standardTwoZero_terminal_gradient_injective_of_JC2
            hJC2 hd hhom hMA
  have hinj : Function.Injective (mvGradientMap T.fibre) :=
    mvGradientMap_injective_of_rename_perm
      T.rho T.fibre hinjRenamed
  exact
    exactGradientCollision_impossible_of_injective
      T.fibre T.leftPoint T.rightPoint T.distinct
      hinj T.exactCollision

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The rank-one closing order exhausts the entire determinant defect.
Consequently, for positive defect, the ordinary two-for-one kernel spending
`2*e` cannot fit inside the available clock.  This is why the rank-one
closing should be treated as a genuine terminal direct-jump candidate rather
than another copy of the preterminal kernel restart. -/
theorem AdaptiveAlignedExactRankOneSchurClock.kernelSpend_not_affordable_of_closing
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hdefect : 0 < E.defect)
    (hclosing : S.firstOrder = E.defect) :
    ¬ 2 * S.firstOrder ≤ E.defect := by
  rw [hclosing]
  omega

/-- By contrast, the first common order in an exact zero-Schur clock always
fits the two-for-one kernel budget.  Thus zero-Schur closing remains
restart-compatible until a genuine source integrality/zero-slope obstruction
is encountered. -/
theorem ExactZeroSchurClock.kernelSpend_affordable
    {R : Type*} [CommRing R] [IsDomain R]
    (Z : ExactZeroSchurClock R) :
    2 * Z.firstOrder ≤ Z.defect :=
  Z.twice_firstOrder_le_defect

/-- Exact polynomial-level extraction interfaces for the four residual
blocker outputs of the green lossless canonical dispatcher.

These are deliberately source-sensitive.  An implementation must construct
an actual associated-graded polynomial collision; a matrix Schur clock or an
isolated rigid packet is not sufficient by itself. -/
structure AdaptiveAlignedSmithCanonicalTerminalExtraction
    (K : Type*) [Field K] [CharZero K] where
  schur :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B),
      Nonempty (TerminalAssociatedGradedCollisionData K)

  zeroSchur :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z),
      Nonempty (TerminalAssociatedGradedCollisionData K)

  planarRigid :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet),
      Nonempty (TerminalAssociatedGradedCollisionData K)

  wSquareRigid :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet),
      Nonempty (TerminalAssociatedGradedCollisionData K)

/-- Final no-JC2 frontier after a completed polynomial-level terminal
extraction.  All scalar and strictly-positive terminal endpoints have already
been eliminated; the only terminal constructor left is explicitly
one-zero/two-zero. -/
inductive AdaptiveAlignedSmithCanonicalNoJC2Outcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)
  | reentry
      (t : AdaptiveGeometricRestartState (K := K))
  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)
  | jc2SensitiveTerminal
      (T : JC2SensitiveTerminalCollisionData K)

/-- **Mathematically sharp final adaptive dispatcher, before planar JC2.**

Assuming only the honest closing-to-associated-graded extraction, every
remaining adaptive Smith episode either makes certified well-founded
progress, re-enters through a coordinate/section boundary, reaches zero
Hessian defect, or lands in the explicit one-zero/two-zero terminal class.

No planar JC2 hypothesis is used in this theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalNoJC2Dispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hextract : AdaptiveAlignedSmithCanonicalTerminalExtraction K) :
    AdaptiveAlignedSmithCanonicalNoJC2Outcome RR s complexity := by
  rcases s.alignedSmithCanonicalProvenanceDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, source, hclose⟩ |
    ⟨B, source, Z, hclose⟩ |
    ⟨B, hall, P, hrigid⟩ |
    ⟨B, hall, P, hrigid⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · let T := Classical.choice (hextract.schur B source hclose)
    let J := Classical.choice T.exists_jc2Sensitive
    exact .jc2SensitiveTerminal J

  · let T := Classical.choice (hextract.zeroSchur B source Z hclose)
    let J := Classical.choice T.exists_jc2Sensitive
    exact .jc2SensitiveTerminal J

  · let T := Classical.choice (hextract.planarRigid B hall P hrigid)
    let J := Classical.choice T.exists_jc2Sensitive
    exact .jc2SensitiveTerminal J

  · let T := Classical.choice (hextract.wSquareRigid B hall P hrigid)
    let J := Classical.choice T.exists_jc2Sensitive
    exact .jc2SensitiveTerminal J

/-- Under planar JC2, the explicit final one-zero/two-zero constructor is
also impossible.  Hence, once polynomial terminal extraction is supplied,
the canonical adaptive episode has only progress, re-entry, or zero defect. -/
inductive AdaptiveAlignedSmithCanonicalPostTerminalOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)
  | reentry
      (t : AdaptiveGeometricRestartState (K := K))
  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

/-- JC2 is used only to remove the final explicitly-labelled sensitive
terminal endpoint. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalPostTerminalDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hextract : AdaptiveAlignedSmithCanonicalTerminalExtraction K)
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    AdaptiveAlignedSmithCanonicalPostTerminalOutcome RR s complexity := by
  rcases
      s.alignedSmithCanonicalNoJC2Dispatcher
        RR complexity hsrepair hextract with
    hstrict | ⟨t⟩ | ⟨t, hzero⟩ | ⟨T⟩
  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact False.elim (T.impossible_of_JC2 hJC2)

end

end HC4.Valuation
