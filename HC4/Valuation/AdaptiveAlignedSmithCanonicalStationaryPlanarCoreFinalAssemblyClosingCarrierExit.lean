import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostTransverseKernel
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRS2LiftRepair
import Mathlib.Tactic

/-!
# Final assembly A17.2: closing-carrier universal exit

The A17.1 frontier still records three local constructors carrying an honest
`AdaptiveAlignedSmithRankOneClosingSourceCarrier`: the canonical lossless-axis
branch and the two section-gauge branches.  The old early-Schur wrapper made
the first-key/RS2 closure look specific to a strict first-actual clock, but
its proof only used that hypothesis to obtain positive transverse support.
At the A17 terminal frontier that support is already available from the common
scale-sound stationary packet.

This file therefore exposes the stronger carrier-level statement directly.
For any retained closing carrier over the stationary blocker, the honest first
transverse source key and the raw Schur projective dichotomy give either
rank-two repair or an RS2-ready constant line.  A moving full lift is the
already-green derivative rank-two repair; a constant full source kernel is
made literal by A16, forced transverse by the common first-longitudinal
departure, and consumed by A17.1's saturated-kernel restart.

Thus no axis/staircase or gauge-specific hypothesis is needed: existence of
the source-honest closing carrier itself already forces a genuine exit.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Local copy of the scalar cancellation lemma used by A17.1. -/
private theorem mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A17.1's transverse-kernel restart only depends on the literal kernel and
its nonzero transverse coordinate.  This carrier-level form removes the
early-Schur/RS2 bookkeeping fields from the API. -/
theorem LiteralConstantSpecialSourceKernelData.exists_ramifiedSpend_of_transverse
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker}
    (D : LiteralConstantSpecialSourceKernelData C)
    (htrans : ∃ j : Fin 4, j ≠ (0 : Fin 4) ∧ D.direction j ≠ 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases htrans with ⟨ell, hell0, hvell⟩
  let F := polynomialFamilySpecialFiber C.family
  have hdir := D.directionalDerivative_eq_zero
  change constantSourceDirectionalDerivative F D.direction = 0 at hdir

  fin_cases ell
  · exact False.elim (hell0 rfl)
  · let combo :=
      MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 1) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 1) *
          MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 1) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (1 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 1) =
            MvPolynomial.C (D.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 1) =
            MvPolynomial.C (D.direction 2) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 1) =
            MvPolynomial.C (D.direction 3) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (1 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (1 : Fin 4)) *
                (MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 1) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 1) *
                    MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 1) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 0 / D.direction 1)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 2 / D.direction 1)) *
                  MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 3 / D.direction 1)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h2C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (1 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (1 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
            (D.direction 0 / D.direction 1)
            (D.direction 2 / D.direction 1)
            (D.direction 3 / D.direction 1) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
          (D.direction 0 / D.direction 1)
          (D.direction 2 / D.direction 1)
          (D.direction 3 / D.direction 1)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq C
      (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 1)
      (D.direction 2 / D.direction 1)
      (D.direction 3 / D.direction 1) hp
  · let combo :=
      MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 2) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 2) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 2) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (2 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 2) =
            MvPolynomial.C (D.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 2) =
            MvPolynomial.C (D.direction 1) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 2) =
            MvPolynomial.C (D.direction 3) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (2 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (2 : Fin 4)) *
                (MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 2) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 2) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 2) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 0 / D.direction 2)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 1 / D.direction 2)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 3 / D.direction 2)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h1C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (2 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (2 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
            (D.direction 0 / D.direction 2)
            (D.direction 1 / D.direction 2)
            (D.direction 3 / D.direction 2) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
          (D.direction 0 / D.direction 2)
          (D.direction 1 / D.direction 2)
          (D.direction 3 / D.direction 2)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq C
      (2 : Fin 4) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 2)
      (D.direction 1 / D.direction 2)
      (D.direction 3 / D.direction 2) hp
  · let combo :=
      MvPolynomial.pderiv (3 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 3) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 3) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 3) *
          MvPolynomial.pderiv (2 : Fin 4) F
    have hv : D.direction (3 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 3) =
            MvPolynomial.C (D.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 3) =
            MvPolynomial.C (D.direction 1) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 3) =
            MvPolynomial.C (D.direction 2) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (3 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (3 : Fin 4)) *
                (MvPolynomial.pderiv (3 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 3) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 3) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 3) *
                    MvPolynomial.pderiv (2 : Fin 4) F) =
              MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 0 / D.direction 3)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 1 / D.direction 3)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 2 / D.direction 3)) *
                  MvPolynomial.pderiv 2 F := by ring
          _ = MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F := by
              rw [h0C, h1C, h2C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (3 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (3 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
            (D.direction 0 / D.direction 3)
            (D.direction 1 / D.direction 3)
            (D.direction 2 / D.direction 3) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (D.direction 0 / D.direction 3)
          (D.direction 1 / D.direction 3)
          (D.direction 2 / D.direction 3)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq C
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 3)
      (D.direction 1 / D.direction 3)
      (D.direction 2 / D.direction 3) hp

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Universal closing-carrier exit -/

/-- Every honest closing carrier at the common A17 stationary frontier exits
by either a strict ramified raw-defect spend or the already-certified outer
rank-two repair macro. -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoMacro
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s) ∨
      (∃ outer target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        HasCertifiedRamifiedEpisodeInternalMove outer s ∧
        CertifiedSameScaleEpisodeProgress RR target outer) := by
  have hpos :
      (positiveTransverseSourceSupport
        (polynomialFamilySpecialFiber C.family)).Nonempty := by
    rcases S.specialFiber_witnesses.1 with ⟨d, hd, hd1⟩
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using hd
    · unfold pureLongitudinalTransverseDegree
      omega
  have hkey : C.HasFirstTransverseSourceKey :=
    C.hasFirstTransverseSourceKey_of_positiveSupport hpos

  rcases C.rawSpecialSchurProjectiveWedge_or_constantLine with hmoving | hconstant
  · rcases hmoving with ⟨k, hk⟩
    rcases C.rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
        complexity k hk with ⟨R⟩
    right
    rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
        RR s complexity hsrepair clock_eq R.progress with
      ⟨outer, target, hmove, hprogress⟩
    exact ⟨outer, target, hmove, hprogress⟩
  · rcases hconstant with ⟨L⟩
    rcases hkey.exists_constantLineCanonicalProvenance L with ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      right
      rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
          RR s complexity hsrepair clock_eq R.repairProgress with
        ⟨outer, target, hmove, hprogress⟩
      exact ⟨outer, target, hmove, hprogress⟩
    · rcases hrs2 with ⟨N⟩
      let R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData := {
        line := L
        provenance := A
        provenance_schurKernel := hAE
        rs2Ready := N
      }
      rcases R.constantSourceKernel_or_activeProjective with hkernel | hactive
      · rcases hkernel with ⟨K0⟩
        let literal := K0.toLiteralConstantSpecialSourceKernelData
        have htrans := P.exists_transverse_of_literalConstantKernel literal
        left
        exact literal.exists_ramifiedSpend_of_transverse S clock_eq htrans
      · rcases hactive with ⟨M⟩
        let E := M.toEulerMotionData
        rcases E.exists_liftDerivativeRankTwoRepairData complexity with ⟨R2⟩
        right
        rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
            RR s complexity hsrepair clock_eq R2.progress with
          ⟨outer, target, hmove, hprogress⟩
        exact ⟨outer, target, hmove, hprogress⟩

end

end HC4.Valuation
