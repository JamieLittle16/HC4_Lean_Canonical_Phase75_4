import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyAxisStraightening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAllTransverseRationalKernelDispatcher
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroSchurOffenderDispatcher
import Mathlib.Tactic

/-!
# Final assembly A5: saturated-rational zero slope recovers integral zero slope

A4 reduces every nonlinear canonical binary wall to an exact one-variable
source after an honest determinant-one shear.  A separate residual branch is
the exact zero-Schur source.  The current scale-sound stationary packet keeps
the strongest denominator-cleared information on that source: every
transverse saturated rational kernel slope is zero.

The older first-kernel-offender closing theorem is phrased using maximal
*integral* slope zero.  The two certificates are not assumptions of the same
kind, so final assembly must connect them rather than silently replacing one
by the other.

The bridge is elementary and source-honest.  Saturated rational slope zero
provides a monomial in the special fibre with positive kernel exponent.  If a
positive integral slope divided every source coefficient, that monomial's
coefficient would be divisible by a positive power of the family parameter,
so its constant coefficient would vanish, contradicting membership in the
special-fibre support.  Hence the maximal integral slope is exactly zero.

This file packages that implication and immediately upgrades the A4
zero-Schur constructor to an explicit first-kernel offender on the actual
right-recentered source.  No progress claim is made from the offender alone.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveRecenteredKernelZeroRationalSlopeObstruction

/-- Exact zero saturated rational slope forces exact zero maximal integral
slope on the same honest right-recentered family.

The proof uses the parameter-order-zero monomial supplied by the rational
zero-slope certificate.  A positive integral blow-up slope would force the
coefficient of that monomial to contain a positive power of `τ`, contradicting
its nonzero special-fibre coefficient. -/
theorem toZeroIntegralSlope
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    {kernel : Fin 4}
    (Z : AdaptiveRecenteredKernelZeroRationalSlopeObstruction B kernel) :
    AdaptiveRecenteredKernelZeroSlopeObstruction B kernel := by
  refine ⟨Z.active, ?_⟩
  let P := B.aligned.endpoint.rightRecenteredFamily
  let q := maximalIntegralKernelSlope kernel P Z.active
  have hq0 : q = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hqpos
    rcases Z.specialFiber_witness with ⟨d, hdSpecial, hdKernel⟩
    have hspecialCoeff :
        Polynomial.constantCoeff (MvPolynomial.coeff d P) ≠ 0 := by
      have h := MvPolynomial.mem_support_iff.mp hdSpecial
      rw [coeff_polynomialFamilySpecialFiber] at h
      simpa [P] using h
    have hdFamily : d ∈ P.support := by
      rw [MvPolynomial.mem_support_iff]
      intro hzero
      apply hspecialCoeff
      rw [hzero]
      simp
    have hdiv :
        kernelCoefficientTauPower kernel q d ∣ MvPolynomial.coeff d P := by
      exact
        (maximalIntegralKernelSlope_divisibility kernel P Z.active) d hdFamily
    rcases hdiv with ⟨r, hr⟩
    have hexp : 0 < q * d kernel := Nat.mul_pos hqpos hdKernel
    have hconstZero :
        Polynomial.constantCoeff (MvPolynomial.coeff d P) = 0 := by
      rw [hr]
      change (Polynomial.X ^ (q * d kernel) * r).coeff 0 = 0
      rw [Polynomial.coeff_X_pow_mul']
      simp [Nat.not_le.mpr hexp]
    exact hspecialCoeff hconstZero
  simpa [P, q] using hq0

end AdaptiveRecenteredKernelZeroRationalSlopeObstruction

/-- Source-level information genuinely available on the scale-sound
zero-Schur branch after applying the rational-to-integral zero-slope bridge. -/
structure AdaptiveAlignedSmithZeroSchurScaleSoundSourceData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) : Prop where
  recenteredZero :
    AdaptiveRecenteredKernelZeroSlopeObstruction
      B adaptiveCanonicalCommonKernel
  firstKernelOffender :
    AdaptiveAlignedSmithZeroSchurFirstKernelOffender C
  zeroRationalWitness :
    AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C

/-- Build the exact source-level zero-Schur packet from the all-transverse
rational-zero certificate already retained by the scale-sound stationary
blocker. -/
theorem AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker.zeroSchurScaleSoundSourceData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker) :
    AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C := by
  let Zrat : AdaptiveRecenteredKernelZeroRationalSlopeObstruction
      S.blocker adaptiveCanonicalCommonKernel := by
    simpa [adaptiveCanonicalCommonKernel] using S.allTransverseZero.third
  let Zint : AdaptiveRecenteredKernelZeroSlopeObstruction
      S.blocker adaptiveCanonicalCommonKernel := Zrat.toZeroIntegralSlope
  refine ⟨Zint, C.firstKernelOffender_of_recenteredZeroSlope Zint, ?_⟩
  unfold AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness
  simpa [AdaptiveAlignedSmithZeroSchurClosingSourceCarrier.family,
    adaptiveCanonicalCommonKernel] using Zrat.specialFiber_witness

/-- A5 global frontier.  Relative to A4, the raw zero-Schur constructor has
been replaced by an exact source first-kernel offender together with both
rational and integral zero-slope certificates on the same family. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSlopeBridgedAssemblyOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | earlySchurRS2Ready
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalWallLongitudinal
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_ne_zero : face ≠ 0)
      (base_support :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsLongitudinalBaseSupport face)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

  | canonicalWallTransverseLowDegree
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent data.binaryFace D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ data.binaryFace.support, d.degree ≤ D)

  | canonicalWallTransverseNonlinearAxis
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (straight : BinarySingularHessianNonlinearAxisStraighteningData data.binaryFace)

  | zeroSchurSourceReady
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

  | planarRigid
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- A5 assembly theorem: bridge the scale-sound saturated-rational zero-slope
certificate to integral zero slope and expose an honest zero-Schur first
kernel offender. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreZeroSlopeBridgedAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSlopeBridgedAssemblyOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreAxisStraightenedAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R
  | canonicalWallLongitudinal S clock_eq clock_pos C heq D face face_ne_zero
      base_support source_collision face_linear_zero =>
      exact .canonicalWallLongitudinal S clock_eq clock_pos C heq D face
        face_ne_zero base_support source_collision face_linear_zero
  | canonicalWallTransverseLowDegree S clock_eq clock_pos C heq data D H hD
      H_eq H_ne_zero maximal =>
      exact .canonicalWallTransverseLowDegree S clock_eq clock_pos C heq data D H
        hD H_eq H_ne_zero maximal
  | canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq data straight =>
      exact .canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq data
        straight
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchurSourceReady S clock_eq clock_pos C
        (S.zeroSchurScaleSoundSourceData C)
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid
  | sectionGaugeKilled S clock_eq clock_pos C heq G hkilled =>
      exact .sectionGaugeKilled S clock_eq clock_pos C heq G hkilled
  | sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict =>
      exact .sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
