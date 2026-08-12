import HC4.Valuation.AdaptiveAlignedSmithMarkedAxisTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalReduction
import Mathlib.Tactic

/-!
# Sharp planar terminal frontier for the adaptive Smith proof

The green marked-axis reduction shows that a terminal source exposure which
preserves the distinguished right-recentered collision must have longitudinal
weight zero.  The only issue left after the standard terminal classification
is therefore whether a second zero weight survives.

This file makes that last obstruction exact.

A terminal permutation is called *anchored* when it fixes the longitudinal
coordinate `0`.  Under such a permutation the canonical marked collision
`0 ~ -e₀` remains literally `0 ~ -e₀` in standard terminal coordinates.
Consequently:

* the standard one-zero terminal endpoint is impossible without JC2;
* the standard two-zero terminal endpoint produces an honest planar Keller
  map with a collision at two distinct points.

Thus, after an anchored polynomial terminal extraction, the complete adaptive
Smith dispatcher has only four outputs:

    strict episode progress | re-entry | zero defect | planar Keller collision.

No JC2 input occurs until one chooses to eliminate the final explicit planar
collision.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Exact gradient collisions transport covariantly under a simultaneous
coordinate permutation. -/
theorem HasExactGradientCollision.rename_perm
    {F : MvPolynomial (Fin 4) K}
    {p q : Fin 4 → K}
    (hcoll : HasExactGradientCollision F p q)
    (rho : Equiv.Perm (Fin 4)) :
    HasExactGradientCollision
      (MvPolynomial.rename rho F)
      (terminalPermutePoint rho p)
      (terminalPermutePoint rho q) := by
  intro j
  change
    mvGradientMap (MvPolynomial.rename rho F)
        (terminalPermutePoint rho p) j =
      mvGradientMap (MvPolynomial.rename rho F)
        (terminalPermutePoint rho q) j
  rw [mvGradientMap_rename_perm, mvGradientMap_rename_perm]
  exact hcoll (rho.symm j)

/-- The zero point is fixed by every coordinate permutation. -/
@[simp] theorem terminalPermutePoint_zeroPoint
    (rho : Equiv.Perm (Fin 4)) :
    terminalPermutePoint (K := K) rho (fun _ : Fin 4 => (0 : K)) =
      (fun _ : Fin 4 => (0 : K)) := by
  funext j
  simp [terminalPermutePoint]

/-- If a terminal permutation fixes the marked longitudinal coordinate, it
also fixes the canonical negative longitudinal axis point. -/
theorem terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero
    (rho : Equiv.Perm (Fin 4))
    (hfix : rho (0 : Fin 4) = 0) :
    terminalPermutePoint rho (negativeLongitudinalAxisPoint (K := K)) =
      negativeLongitudinalAxisPoint (K := K) := by
  have hfixSymm : rho.symm (0 : Fin 4) = 0 := by
    have h := congrArg rho.symm hfix
    simpa using h.symm
  funext j
  by_cases hj : j = 0
  · subst j
    simp [terminalPermutePoint, negativeLongitudinalAxisPoint,
      coordinateAxisPoint, hfixSymm]
  · have hsymm : rho.symm j ≠ 0 := by
      intro hzero
      apply hj
      calc
        j = rho (rho.symm j) := by simp
        _ = rho 0 := by rw [hzero]
        _ = 0 := hfix
    simp [terminalPermutePoint, negativeLongitudinalAxisPoint,
      coordinateAxisPoint, hj, hsymm]

/-- A JC2-sensitive terminal collision together with the exact marked-axis
normalisation inherited from the adaptive source exposure. -/
structure AnchoredJC2SensitiveTerminalCollisionData
    (K : Type*) [Field K] where
  terminal : JC2SensitiveTerminalCollisionData K
  leftPoint_zero :
    terminal.leftPoint = (fun _ : Fin 4 => (0 : K))
  rightPoint_negativeAxis :
    terminal.rightPoint = negativeLongitudinalAxisPoint (K := K)
  rho_fix_zero : terminal.rho (0 : Fin 4) = 0

/-- **Sharp marked-axis terminal reduction.**

Once the terminal permutation is anchored on the distinguished longitudinal
zero-weight coordinate, the one-zero endpoint is contradictory without JC2.
The only remaining endpoint is two-zero, and it yields an actual planar
Keller collision. -/
theorem AnchoredJC2SensitiveTerminalCollisionData.hasPlanarKellerCollision
    (T : AnchoredJC2SensitiveTerminalCollisionData K) :
    Nonempty (PlanarKellerCollisionData K) := by
  let J := T.terminal
  have hcollRenamed := J.exactCollision.rename_perm J.rho
  have hcollMarked :
      HasExactGradientCollision
        (MvPolynomial.rename J.rho J.fibre)
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K)) := by
    rw [T.leftPoint_zero] at hcollRenamed
    rw [terminalPermutePoint_zeroPoint] at hcollRenamed
    rw [T.rightPoint_negativeAxis] at hcollRenamed
    rw [terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero
      J.rho T.rho_fix_zero] at hcollRenamed
    exact hcollRenamed

  cases J.endpoint with
  | oneZero d a ha had hhom hMA =>
      exact False.elim
        (standardOneZero_negativeLongitudinalAxis_collision_impossible
          ha had hhom hMA hcollMarked)
  | twoZero d hd hhom hMA =>
      exact
        standardTwoZero_negativeLongitudinalAxis_hasPlanarKellerCollision
          hd hhom hMA hcollMarked

/-- A planar Keller collision is exactly the explicit contradiction consumed
by the planar JC2 injectivity interface. -/
theorem PlanarKellerCollisionData.impossible_of_JC2
    (T : PlanarKellerCollisionData K)
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    False := by
  have hinj : Function.Injective (HC4.planarPolynomialMapEval T.map) :=
    HC4.planar_injective_of_JC2 hJC2 T.map T.keller
  exact T.distinct (hinj T.collision)

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The exact remaining extraction interface, sharpened by the marked-axis
source provenance.

Compared with `AdaptiveAlignedSmithCanonicalTerminalExtraction`, every output
is already normalized to the only terminal classes which can survive the
unconditional scalar/positive classification, and it records that the
terminal permutation fixes the distinguished longitudinal zero coordinate.
The source-level associated-graded construction is still required; this
interface does not identify a Schur matrix with a polynomial potential. -/
structure AdaptiveAlignedSmithCanonicalAnchoredTerminalExtraction
    (K : Type*) [Field K] [CharZero K] where
  schur :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B),
      Nonempty (AnchoredJC2SensitiveTerminalCollisionData K)

  zeroSchur :
    ∀ {degreeCap : ℕ}
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z),
      Nonempty (AnchoredJC2SensitiveTerminalCollisionData K)

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
      Nonempty (AnchoredJC2SensitiveTerminalCollisionData K)

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
      Nonempty (AnchoredJC2SensitiveTerminalCollisionData K)

/-- Final unconditional frontier after an anchored terminal extraction.
The former generic JC2-sensitive endpoint has become one explicit planar
Keller collision. -/
inductive AdaptiveAlignedSmithCanonicalPlanarFrontierOutcome
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
  | planarCollision
      (T : PlanarKellerCollisionData K)

/-- **Sharp no-JC2 adaptive frontier.**

Once the honest associated-graded extraction respects the marked longitudinal
axis, the complete adaptive Smith episode either makes certified progress,
re-enters, reaches zero defect, or produces an explicit planar Keller
collision.  One-zero has disappeared unconditionally. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalPlanarFrontierDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hextract : AdaptiveAlignedSmithCanonicalAnchoredTerminalExtraction K) :
    AdaptiveAlignedSmithCanonicalPlanarFrontierOutcome RR s complexity := by
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

  · let A := Classical.choice (hextract.schur B source hclose)
    let T := Classical.choice A.hasPlanarKellerCollision
    exact .planarCollision T

  · let A := Classical.choice (hextract.zeroSchur B source Z hclose)
    let T := Classical.choice A.hasPlanarKellerCollision
    exact .planarCollision T

  · let A := Classical.choice (hextract.planarRigid B hall P hrigid)
    let T := Classical.choice A.hasPlanarKellerCollision
    exact .planarCollision T

  · let A := Classical.choice (hextract.wSquareRigid B hall P hrigid)
    let T := Classical.choice A.hasPlanarKellerCollision
    exact .planarCollision T

/-- Under JC2 the one remaining explicit planar collision is impossible, so
the anchored terminal extraction leaves only progress, re-entry, or zero
defect. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalPlanarFrontier_of_JC2
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hextract : AdaptiveAlignedSmithCanonicalAnchoredTerminalExtraction K)
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    AdaptiveAlignedSmithCanonicalPostTerminalOutcome RR s complexity := by
  rcases
      s.alignedSmithCanonicalPlanarFrontierDispatcher
        RR complexity hsrepair hextract with
    hstrict | ⟨t⟩ | ⟨t, hzero⟩ | ⟨T⟩
  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact False.elim (T.impossible_of_JC2 hJC2)

end

end HC4.Valuation
