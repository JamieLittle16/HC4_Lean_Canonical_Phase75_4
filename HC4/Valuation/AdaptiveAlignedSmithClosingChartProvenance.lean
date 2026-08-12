import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgameProvenance
import Mathlib.Tactic

/-!
# Lossless Hessian-chart provenance for the adaptive blocker endgame

The canonical blocker proof is already closed, but the compact Schur
interfaces forget one final piece of source information: which honest
right-recentered Hessian chart produced the exact four-block clock.

That information matters at the source-level terminal/restart interface.
The green blocker Hessian analysis uses exactly three determinant-preserving
chart types:

* the coordinate chart attached to a permutation `rho`;
* the same chart followed by the displayed `0 <-> 2` swap;
* the same chart followed by the displayed elementary `0 <- 0 + 2` shear.

This file records those origins explicitly.  It then reruns the already-green
Schur/zero-Schur split on the exact retained block and chooses a concrete
rank-one Schur clock from the retained pivot.  Consequently a closing output
is definitionally tied to an honest block of the right-recentered polynomial
family instead of merely asserting that some matrix clock exists.

The all-minors branch is unchanged and therefore still enters the already-
green pure-longitudinal / quadratic-packet endgame.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## The three honest chart origins -/

/-- The only determinant-preserving block changes used by the green
recentered blocker Hessian frontier. -/
inductive AdaptiveAlignedRightRecenteredHessianChartKind where
  | coordinate
  | swap02
  | shear02
  deriving DecidableEq

/-- The actual polynomial-series four-block represented by a chart kind and
an underlying coordinate permutation. -/
noncomputable def adaptiveAlignedRightRecenteredChartBlock
    {degreeCap : ℕ}
    (kind : AdaptiveAlignedRightRecenteredHessianChartKind)
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  match kind with
  | .coordinate =>
      adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E
  | .swap02 =>
      (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).swap02
  | .shear02 =>
      (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).shear02

/-- Every retained chart has exactly the same pure Hessian determinant clock
as the honest right-recentered family. -/
theorem adaptiveAlignedRightRecenteredChartBlock_determinantCore
    {degreeCap : ℕ}
    (kind : AdaptiveAlignedRightRecenteredHessianChartKind)
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    (adaptiveAlignedRightRecenteredChartBlock kind rho E).determinantCore =
      Polynomial.X ^ E.defect := by
  cases kind with
  | coordinate =>
      exact adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
        rho E
  | swap02 =>
      unfold adaptiveAlignedRightRecenteredChartBlock
      rw [GeneralFourBlock.swap02_determinantCore]
      exact adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
        rho E
  | shear02 =>
      unfold adaptiveAlignedRightRecenteredChartBlock
      rw [GeneralFourBlock.shear02_determinantCore]
      exact adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
        rho E

/-- An exact active chart of the honest right-recentered Hessian.  The
nonzero active determinant is stored on the actual polynomial-series block,
not merely on its finite specialisation. -/
structure AdaptiveAlignedRightRecenteredExactHessianChart
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  rho : Equiv.Perm (Fin 4)
  kind : AdaptiveAlignedRightRecenteredHessianChartKind
  activeDet_coeff_zero_ne_zero :
    (adaptiveAlignedRightRecenteredChartBlock
      kind rho B.aligned.endpoint).activeDet.coeff 0 ≠ 0

namespace AdaptiveAlignedRightRecenteredExactHessianChart

/-- The exact four-block retained by a chart. -/
noncomputable def block
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  adaptiveAlignedRightRecenteredChartBlock
    C.kind C.rho B.aligned.endpoint

/-- The retained block has the endpoint's exact determinant clock. -/
theorem determinantCore
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B) :
    C.block.determinantCore =
      Polynomial.X ^ B.aligned.endpoint.defect := by
  unfold block
  exact adaptiveAlignedRightRecenteredChartBlock_determinantCore
    C.kind C.rho B.aligned.endpoint

/-- The chart's stored active-minor certificate rewritten on `C.block`. -/
theorem block_activeDet_coeff_zero_ne_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B) :
    C.block.activeDet.coeff 0 ≠ 0 := by
  exact C.activeDet_coeff_zero_ne_zero

end AdaptiveAlignedRightRecenteredExactHessianChart

/-! ## Exact-chart discovery, before any Schur information is forgotten -/

/-- Either a determinant-preserving honest chart exposes a nonzero active
constant minor, or the complete finite right-recentered Hessian has all
`2 x 2` minors zero in every coordinate chart.

This is the lossless chart-origin version of the already-green
permutation/swap/shear frontier. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.exists_exactRightRecenteredHessianChart_or_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) :
    Nonempty (AdaptiveAlignedRightRecenteredExactHessianChart B) ∨
      (∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) := by
  classical

  by_cases hprincipal :
      ∃ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).activeDet ≠ 0
  · rcases hprincipal with ⟨rho, hactive⟩
    left
    refine ⟨{
      rho := rho
      kind := .coordinate
      activeDet_coeff_zero_ne_zero := ?_
    }⟩
    change
      (adaptiveAlignedEndpointRightRecenteredHessianFourBlock
        rho B.aligned.endpoint).activeDet.coeff 0 ≠ 0
    rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
    exact hactive

  · by_cases hsecond :
        ∃ rho : Equiv.Perm (Fin 4),
          let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
            rho B.aligned.endpoint
          H.x.coeff 0 * H.d.coeff 0 -
            H.r.coeff 0 * H.r.coeff 0 ≠ 0
    · rcases hsecond with ⟨rho, h21⟩
      left
      refine ⟨{
        rho := rho
        kind := .swap02
        activeDet_coeff_zero_ne_zero := ?_
      }⟩
      change
        ((adaptiveAlignedEndpointRightRecenteredHessianFourBlock
          rho B.aligned.endpoint).swap02).activeDet.coeff 0 ≠ 0
      rw [swap02_activeDet_coeff_zero]
      simpa using h21

    · by_cases hcross :
          ∃ rho : Equiv.Perm (Fin 4),
            let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
              rho B.aligned.endpoint
            H.p.coeff 0 * H.d.coeff 0 -
              H.b.coeff 0 * H.r.coeff 0 ≠ 0
      · rcases hcross with ⟨rho, hcrossrho⟩
        let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
          rho B.aligned.endpoint

        have h01 : H.activeDet.coeff 0 = 0 := by
          dsimp [H]
          rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
          by_contra hne
          exact hprincipal ⟨rho, hne⟩

        have h21 :
            H.x.coeff 0 * H.d.coeff 0 -
              H.r.coeff 0 * H.r.coeff 0 = 0 := by
          by_contra hne
          exact hsecond ⟨rho, by simpa [H] using hne⟩

        left
        refine ⟨{
          rho := rho
          kind := .shear02
          activeDet_coeff_zero_ne_zero := ?_
        }⟩
        change H.shear02.activeDet.coeff 0 ≠ 0
        exact shear02_activeDet_coeff_zero_ne_zero_of_cross
          H h01 h21 (by simpa [H] using hcrossrho)

      · right
        have hrank :
            HasAdaptiveAlignedRightRecenteredHessianRankOneRelations
              B.aligned.endpoint := by
          intro rho
          let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
            rho B.aligned.endpoint

          have h01 : H.activeDet.coeff 0 = 0 := by
            dsimp [H]
            rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
            by_contra hne
            exact hprincipal ⟨rho, hne⟩

          have h21 :
              H.x.coeff 0 * H.d.coeff 0 -
                H.r.coeff 0 * H.r.coeff 0 = 0 := by
            by_contra hne
            exact hsecond ⟨rho, by simpa [H] using hne⟩

          have hcross0 :
              H.p.coeff 0 * H.d.coeff 0 -
                H.b.coeff 0 * H.r.coeff 0 = 0 := by
            by_contra hne
            exact hcross ⟨rho, by simpa [H] using hne⟩

          exact ⟨h01, h21, hcross0⟩

        exact
          adaptiveAlignedRightRecenteredSpecialHessian_allTwoByTwoMinorsZero
            B.aligned.endpoint hrank

/-! ## Schur data that remains tied to the exact chart -/

/-- Rank-one Schur data together with the exact honest chart that produced
its four-block. -/
structure AdaptiveAlignedRightRecenteredRankOneSchurChartData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  chart : AdaptiveAlignedRightRecenteredExactHessianChart B
  schurData : AdaptiveAlignedExactFourBlockSchurData B.aligned.endpoint
  block_eq : schurData.block = chart.block

/-- Zero-Schur data together with the exact honest chart that produced its
four-block. -/
structure AdaptiveAlignedRightRecenteredZeroSchurChartData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  chart : AdaptiveAlignedRightRecenteredExactHessianChart B
  zeroData : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)
  block_eq : zeroData.block = chart.block

/-- The generic exact-block Schur split, strengthened so that the resulting
matrix package is explicitly tied to the retained honest chart. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.schur_or_zeroSchur_of_exactChart
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (C : AdaptiveAlignedRightRecenteredExactHessianChart B)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    Nonempty (AdaptiveAlignedRightRecenteredRankOneSchurChartData B) ∨
      Nonempty (AdaptiveAlignedRightRecenteredZeroSchurChartData B) := by
  let H := C.block

  have hfull :
      H.determinantCore = Polynomial.X ^ B.aligned.endpoint.defect := by
    dsimp [H]
    exact C.determinantCore

  have hactive : H.activeDet.coeff 0 ≠ 0 := by
    dsimp [H]
    exact C.block_activeDet_coeff_zero_ne_zero

  by_cases hzero :
      H.schurA.coeff 0 = 0 ∧
        H.schurB.coeff 0 = 0 ∧
        H.schurC.coeff 0 = 0

  · right
    let Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K) := {
      block := H
      defect := B.aligned.endpoint.defect
      fullDet := hfull
      activeDet_coeff_zero_ne_zero := hactive
      schurA_coeff_zero := hzero.1
      schurB_coeff_zero := hzero.2.1
      schurC_coeff_zero := hzero.2.2
    }
    exact ⟨{
      chart := C
      zeroData := Z
      block_eq := rfl
    }⟩

  · left
    have hnz : H.polynomialSchurSeries.ConstantBlockNonzero := by
      unfold BinarySchurPolynomialSeries.ConstantBlockNonzero
      simp only [GeneralFourBlock.polynomialSchurSeries]
      tauto

    have hdet :
        H.polynomialSchurSeries.determinant =
          H.activeDet * Polynomial.X ^ B.aligned.endpoint.defect := by
      calc
        H.polynomialSchurSeries.determinant =
            H.activeDet * H.determinantCore :=
          H.polynomialSchurSeries_determinant
        _ = H.activeDet * Polynomial.X ^ B.aligned.endpoint.defect := by
          rw [hfull]

    have hcoeff := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hdet

    have hne : B.aligned.endpoint.defect ≠ 0 := Nat.ne_of_gt hdefect

    have hdet0 :
        H.schurA.coeff 0 * H.schurC.coeff 0 -
          H.schurB.coeff 0 * H.schurB.coeff 0 = 0 := by
      simpa [GeneralFourBlock.polynomialSchurSeries,
        BinarySchurPolynomialSeries.determinant,
        Polynomial.coeff_zero_eq_eval_zero, hne] using hcoeff

    have hdetEq :
        H.polynomialSchurSeries.active.coeff 0 *
            H.polynomialSchurSeries.kernel.coeff 0 =
          H.polynomialSchurSeries.offDiag.coeff 0 *
            H.polynomialSchurSeries.offDiag.coeff 0 := by
      have heq :
          H.schurA.coeff 0 * H.schurC.coeff 0 =
            H.schurB.coeff 0 * H.schurB.coeff 0 :=
        sub_eq_zero.mp hdet0
      simpa [GeneralFourBlock.polynomialSchurSeries] using heq

    have hpivot :
        H.polynomialSchurSeries.LeftPivot ∨
          H.polynomialSchurSeries.RightAxisPivot :=
      H.polynomialSchurSeries.leftPivot_or_rightAxisPivot_of_constantBlock
        hnz hdetEq

    let D : AdaptiveAlignedExactFourBlockSchurData B.aligned.endpoint := {
      block := H
      fullDet := hfull
      activeDet_coeff_zero_ne_zero := hactive
      rigid := hpivot
    }

    exact ⟨{
      chart := C
      schurData := D
      block_eq := rfl
    }⟩

/-! ## A concrete chosen pivot and clock tied to the retained block -/

/-- Type-level pivot witness for an exact four-block.  This allows us to
choose a clock without losing the relation to the block that generated it. -/
inductive AdaptiveAlignedExactFourBlockPivot
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedExactFourBlockSchurData E) : Type _ where
  | left (h : D.block.polynomialSchurSeries.LeftPivot)
  | right (h : D.block.polynomialSchurSeries.RightAxisPivot)

/-- Every exact four-block has a type-level pivot witness. -/
theorem AdaptiveAlignedExactFourBlockSchurData.pivot_nonempty
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedExactFourBlockSchurData E) :
    Nonempty (AdaptiveAlignedExactFourBlockPivot D) := by
  rcases D.rigid with hleft | hright
  · exact ⟨.left hleft⟩
  · exact ⟨.right hright⟩

/-- Canonical classical choice of the retained pivot. -/
noncomputable def AdaptiveAlignedExactFourBlockSchurData.chosenPivot
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedExactFourBlockSchurData E) :
    AdaptiveAlignedExactFourBlockPivot D :=
  Classical.choice D.pivot_nonempty

/-- The exact adaptive Schur clock attached to the chosen pivot of this
specific four-block. -/
noncomputable def AdaptiveAlignedExactFourBlockSchurData.chosenClock
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedExactFourBlockSchurData E) :
    AdaptiveAlignedExactRankOneSchurClock E :=
  match D.chosenPivot with
  | .left h => D.toClockLeft h
  | .right h => D.toClockRight h

/-- The chosen concrete clock on a chart-provenance package. -/
noncomputable def AdaptiveAlignedRightRecenteredRankOneSchurChartData.clock
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData B) :
    AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint :=
  D.schurData.chosenClock

/-! ## Lossless chart-level blocker frontier -/

/-- Before the all-minors geometry, every positive-defect blocker is either
strict rank-two repair, a closing rank-one Schur clock attached to an honest
chart, a closing zero-Schur clock attached to an honest chart, or the full
all-minors branch. -/
inductive AdaptiveAlignedSmithBlockerChartFrontier
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (complexity : ℕ) : Prop
  | rankTwoRepair
      (h : RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity))
  | schurClosing
      (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData B)
      (hclose :
        D.clock.firstOrder = B.aligned.endpoint.defect ∧
          (D.clock.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
           D.clock.series.kernel.coeff B.aligned.endpoint.defect ≠ 0))
  | zeroSchurClosing
      (Z : AdaptiveAlignedRightRecenteredZeroSchurChartData B)
      (hclose : HasAdaptiveAlignedZeroSchurClosing Z.zeroData)
  | allMinors
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)

/-- Lossless positive-defect Hessian/Schur frontier. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.chartFrontier
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (complexity : ℕ)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    AdaptiveAlignedSmithBlockerChartFrontier B complexity := by
  rcases B.exists_exactRightRecenteredHessianChart_or_allMinors with
    hchart | hall

  · let C := Classical.choice hchart
    rcases B.schur_or_zeroSchur_of_exactChart C hdefect with hschur | hzero

    · let D := Classical.choice hschur
      rcases D.clock.rankTwoProgress_or_closing (complexity := complexity) with
        hprogress | hclose
      · exact .rankTwoRepair hprogress.1
      · exact .schurClosing D hclose

    · let Z := Classical.choice hzero
      rcases Z.zeroData.rankTwoProgress_or_closing complexity with
        hprogress | hclose
      · exact .rankTwoRepair hprogress
      · exact .zeroSchurClosing Z hclose

  · exact .allMinors hall

/-! ## Full closed blocker endgame with chart provenance -/

/-- The compact endgame, but closing branches now retain their exact honest
Hessian chart.  Rigid packet branches retain the full all-minors certificate
exactly as in the green provenance endgame. -/
inductive AdaptiveAlignedSmithBlockerEndgameWithChartProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ) : Prop
  | certifiedStrictSuccessor
      (h : HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor RR B)
  | rankTwoRepair
      (h : RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity))
  | schurClosing
      (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData B)
      (hclose :
        D.clock.firstOrder = B.aligned.endpoint.defect ∧
          (D.clock.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
           D.clock.series.kernel.coeff B.aligned.endpoint.defect ≠ 0))
  | zeroSchurClosing
      (Z : AdaptiveAlignedRightRecenteredZeroSchurChartData B)
      (hclose : HasAdaptiveAlignedZeroSchurClosing Z.zeroData)
  | planarRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)
  | wSquareRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Planar packet handoff preserving the all-minors source certificate. -/
theorem AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint.toBlockerEndgameWithChartProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameWithChartProvenance RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .planarRigidPacket hall P hrigid
  · exact .rankTwoRepair hprogress

/-- `w^2` packet handoff preserving the all-minors source certificate. -/
theorem AdaptiveAlignedSmithWSquarePacketEndpoint.toBlockerEndgameWithChartProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameWithChartProvenance RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .wSquareRigidPacket hall P hrigid
  · exact .rankTwoRepair hprogress

/-- **Closed blocker theorem with exact chart provenance.** -/
theorem AdaptiveAlignedSmithBlockerEndpoint.endgameWithChartProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    AdaptiveAlignedSmithBlockerEndgameWithChartProvenance RR B complexity := by
  rcases B.chartFrontier complexity hdefect with
    hrepair | ⟨D, hclose⟩ | ⟨Z, hclose⟩ | hall

  · exact .rankTwoRepair hrepair
  · exact .schurClosing D hclose
  · exact .zeroSchurClosing Z hclose
  · rcases B.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases B.pureLongitudinal_transverseFree_or_quadraticPacket
          hpure hall with hfree | hplanar' | hw'
      · exact .certifiedStrictSuccessor
          (B.certifiedStrictSuccessor_of_transverseFree RR hfree)
      · rcases hplanar' with ⟨P⟩
        exact P.toBlockerEndgameWithChartProvenance RR hall complexity
      · rcases hw' with ⟨P⟩
        exact P.toBlockerEndgameWithChartProvenance RR hall complexity

    · rcases hplanar with ⟨P⟩
      exact P.toBlockerEndgameWithChartProvenance RR hall complexity

    · rcases hw with ⟨P⟩
      exact P.toBlockerEndgameWithChartProvenance RR hall complexity

end

end HC4.Valuation
