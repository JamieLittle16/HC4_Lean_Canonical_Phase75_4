import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingRigidElimination
import HC4.Valuation.AdaptiveAlignedSmithClosingChartProvenance
import Mathlib.Tactic

/-!
# Global canonical dispatcher with exact closing-chart provenance

The surviving-wall side of the adaptive Smith episode is already closed into
strict progress, re-entry, or zero defect.  The blocker side has also been
closed geometrically, and `AdaptiveAlignedSmithClosingChartProvenance` retains
the final source datum which the terminal/kernel extraction genuinely needs:
the exact determinant-preserving Hessian chart which produced the Schur clock.

This file promotes that chart-level blocker endgame to the global canonical
episode without forgetting anything.  In particular the two closing outputs
retain simultaneously

* the honest right-recentered polynomial family and exact moving collision;
* the exact coordinate/swap/shear Hessian chart;
* the exact determinant clock on that chart; and
* the closing Schur certificate.

Thus the next source-lattice theorem no longer has to reconstruct a chart from
a matrix clock or reconstruct a family from a special fibre.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Source-complete closing carriers -/

/-- Rank-one Schur closing attached simultaneously to the honest recentered
source and to the exact Hessian chart which generated the closing clock. -/
structure AdaptiveAlignedSmithRankOneClosingSourceCarrier
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  source : AdaptiveAlignedSmithBlockerRecenteredSourceData B
  chartData : AdaptiveAlignedRightRecenteredRankOneSchurChartData B
  closing :
    chartData.clock.firstOrder = B.aligned.endpoint.defect ∧
      (chartData.clock.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
       chartData.clock.series.kernel.coeff B.aligned.endpoint.defect ≠ 0)

/-- Zero-Schur closing attached simultaneously to the honest recentered source
and to the exact Hessian chart which generated the zero-Schur block. -/
structure AdaptiveAlignedSmithZeroSchurClosingSourceCarrier
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  source : AdaptiveAlignedSmithBlockerRecenteredSourceData B
  chartData : AdaptiveAlignedRightRecenteredZeroSchurChartData B
  closing : HasAdaptiveAlignedZeroSchurClosing chartData.zeroData

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- The actual polynomial family carried by the closing source. -/
noncomputable def family
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (_C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  B.aligned.endpoint.rightRecenteredFamily

/-- The carried family has the exact endpoint Hessian clock. -/
theorem family_hessianDefect
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    HasPolynomialFamilyHessianDefect (K := K) C.family
      B.aligned.endpoint.defect := by
  exact C.source.hessianDefect

/-- The carried family retains the honest zero-left moving collision. -/
theorem family_exactCollision
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    HasPolynomialFamilyExactGradientCollision
      C.family (zeroPolynomialSection (K := K))
      B.aligned.endpoint.rightRecenteredRightSection := by
  exact C.source.exactCollision

/-- The retained chart has the same exact determinant clock as the honest
recentered family. -/
theorem chart_determinantCore
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.chartData.chart.block.determinantCore =
      Polynomial.X ^ B.aligned.endpoint.defect := by
  exact C.chartData.chart.determinantCore

/-- The Schur block is definitionally tied to the retained honest chart. -/
theorem schurBlock_eq_chartBlock
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.chartData.schurData.block = C.chartData.chart.block :=
  C.chartData.block_eq

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

namespace AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-- The actual polynomial family carried by the closing source. -/
noncomputable def family
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (_C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  B.aligned.endpoint.rightRecenteredFamily

/-- The carried family has the exact endpoint Hessian clock. -/
theorem family_hessianDefect
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :
    HasPolynomialFamilyHessianDefect (K := K) C.family
      B.aligned.endpoint.defect := by
  exact C.source.hessianDefect

/-- The carried family retains the honest zero-left moving collision. -/
theorem family_exactCollision
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :
    HasPolynomialFamilyExactGradientCollision
      C.family (zeroPolynomialSection (K := K))
      B.aligned.endpoint.rightRecenteredRightSection := by
  exact C.source.exactCollision

/-- The retained chart has the same exact determinant clock as the honest
recentered family. -/
theorem chart_determinantCore
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :
    C.chartData.chart.block.determinantCore =
      Polynomial.X ^ B.aligned.endpoint.defect := by
  exact C.chartData.chart.determinantCore

/-- The zero-Schur block is definitionally tied to the retained honest chart. -/
theorem zeroSchurBlock_eq_chartBlock
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :
    C.chartData.zeroData.block = C.chartData.chart.block :=
  C.chartData.block_eq

end AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-! ## Global chart-lossless frontier -/

/-- Final canonical frontier after all already-green surviving-wall and repair
progress has been consumed, but before the closing source-lattice extraction.
The only closing constructors now carry the exact honest Hessian chart. -/
inductive AdaptiveAlignedSmithCanonicalChartOutcome
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

  | blockerSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)

  | blockerZeroSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)

  | blockerPlanarRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | blockerWSquareRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- **Global canonical dispatcher with exact closing-chart provenance.**

Every already-solved branch is consumed exactly as in the green provenance
dispatcher.  On a blocker, however, we rerun the already-green chart-level
endgame and retain its exact source chart.  Consequently no information is
lost between the polynomial family and the final Schur clock. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalChartDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalChartOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalClosedDispatcher RR complexity with
    ⟨B, _hcompact⟩ |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨W, P, _hD, S⟩ |
    ⟨W, P, hD, R⟩ |
    ⟨W, P, _hD, R2, _M⟩

  · by_cases hz : B.aligned.endpoint.defect = 0
    · exact .zeroDefect
        (B.aligned.toAdaptiveState s)
        (by simpa using hz)
    · have hpos : 0 < B.aligned.endpoint.defect := Nat.pos_of_ne_zero hz
      rcases B.endgameWithChartProvenance RR complexity hpos with
        hstrict |
        hrepair |
        ⟨D, hclose⟩ |
        ⟨Z, hzeroClose⟩ |
        ⟨hall, P, hrigid⟩ |
        ⟨hall, P, hrigid⟩

      · unfold HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor at hstrict
        dsimp only at hstrict
        rcases hstrict with ⟨target, hprogress⟩
        exact .strict ⟨_, target, hprogress⟩

      · let a := B.aligned.toAdaptiveState s
        have hastage : a.repair = rankOneRepairState complexity := by
          simpa [a] using hsrepair
        rcases
            a.exists_certifiedRankTwoRepairSuccessor
              RR complexity hastage hrepair with
          ⟨target, hprogress⟩
        exact .strict ⟨a.toScaleAware, target.toScaleAware, hprogress⟩

      · exact .blockerSchurClosing B {
          source := B.recenteredSourceData
          chartData := D
          closing := hclose
        }

      · exact .blockerZeroSchurClosing B {
          source := B.recenteredSourceData
          chartData := Z
          closing := hzeroClose
        }

      · exact .blockerPlanarRigidPacket B hall P hrigid

      · exact .blockerWSquareRigidPacket B hall P hrigid

  · exact .reentry t

  · exact .zeroDefect t hzero

  · have hstrict :=
      AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint.exists_certifiedFixedScaleStrictSuccessor
        (K := K) RR P S
    dsimp only at hstrict
    rcases hstrict with ⟨target, hprogress, _hactive⟩
    exact .strict ⟨_, target, hprogress⟩

  · rcases R.zeroDefect_or_rankTwoProgress_or_closing s W P hD complexity with
      hzero | hrepair | hclosing

    · exact .zeroDefect (W.original.aligned.toAdaptiveState s) hzero

    · let a := W.original.aligned.toAdaptiveState s
      have hastage : a.repair = rankOneRepairState complexity := by
        simpa [a] using hsrepair
      rcases
          a.exists_certifiedRankTwoRepairSuccessor
            RR complexity hastage hrepair with
        ⟨target, hprogress⟩
      exact .strict ⟨a.toScaleAware, target.toScaleAware, hprogress⟩

    · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
          (K := K) s W P R := Classical.choice hclosing
      rcases C.exposure.canonicalSpecial_or_boundary with
        hspecial | hboundary

      · let a : AdaptiveGeometricRestartState (K := K) :=
          C.exposure.toAdaptiveState hspecial
        have hfree :
            ∀ d ∈ (polynomialFamilySpecialFiber a.family).support,
              d (3 : Fin 4) = 0 := by
          simpa [a] using C.specialFiber_free_three hspecial
        rcases
            a.exists_certifiedFixedScaleStrictSuccessor_of_specialFiber_free_three
              RR hfree with
          ⟨target, hprogress, _hactiveTarget⟩
        exact .strict ⟨_, target, hprogress⟩

      · let Bboundary : AdaptiveSmithExposureSectionBoundary C.exposure :=
          Classical.choice hboundary
        exact .reentry Bboundary.toAdaptiveState

  · rcases
      R2.exists_strictSuccessor_from_alignedState RR hsrepair with
      ⟨target, hprogress⟩
    exact .strict
      ⟨(W.original.aligned.toAdaptiveState s).toScaleAware,
        target.toScaleAware, hprogress⟩

end

end HC4.Valuation
