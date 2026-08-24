import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyIntegralZeroNormalForm
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryEliminationInterface
import Mathlib.Tactic

/-!
# Final assembly A11: one terminal stationary local problem

A10 puts every surviving stationary blocker in the literal all-transverse
integral-zero normal form.  The final local eliminator, however, should not
have to reconstruct the other source datum which is shared by every branch:
the canonical first positive longitudinal departure on the same honest
right-recentered special fibre.

This file packages those two facts once and, at the same time, sharpens the
canonical zero-order stationary core one last time.  Its binary transverse
part is reduced from the curved-eliminated four-way frontier to exactly:

* a nonzero degree-zero top component; or
* an exact nonlinear one-axis polynomial after the canonical determinant-one
  binary shear.

The longitudinal core is retained losslessly.

All remaining stationary geometries are then collected into one
`AdaptiveAlignedSmithCanonicalTerminalLocalProblem`.  Thus the global
frontier has only four kinds of output: zero defect, certified defect spend,
rank-two macro progress, or one exact local source problem (plus the already
identified source-equivalent internal-presentation bookkeeping case).

No local residual is declared progress here.  This is the strongest common
source-facing boundary for the final Schur/rigid/RS2/gauge elimination.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Common source data carried by *every* terminal stationary residual:
all three transverse maximal integral slopes vanish, while the honest
right-recentered special fibre still has a canonical first positive
longitudinal departure at the unchanged Smith exponent. -/
structure AdaptiveAlignedSmithCanonicalTerminalSourcePacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop where
  integralZero : AdaptiveAlignedSmithScaleSoundAllTransverseIntegralZero S
  firstDeparture :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily)
      S.blocker.exponent

/-- Every scale-sound stationary blocker supplies the common A11 source
packet without any additional hypothesis. -/
theorem AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker.toTerminalSourcePacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    AdaptiveAlignedSmithCanonicalTerminalSourcePacket S := by
  exact {
    integralZero := S.allTransverseIntegralZero
    firstDeparture := S.firstLongitudinalDeparture
  }

namespace AdaptiveAlignedSmithCanonicalTerminalSourcePacket

/-- The terminal source packet contains two *actual* occupied monomials at
one common transverse Smith exponent and at distinct longitudinal levels. -/
theorem support_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S) :
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
  P.firstDeparture.support_pair

/-- The two retained same-Smith-exponent source layers have strictly
increasing ordinary source degree. -/
theorem ordinaryDegree_strict
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S) :
    ∃ n q : ℕ,
      0 < q ∧
      HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) <
        HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) :=
  P.firstDeparture.ordinaryDegree_strict

end AdaptiveAlignedSmithCanonicalTerminalSourcePacket

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Final axis-normal form of a canonical zero-order stationary core.

The transverse binary polynomial has no residual curved/affine/locked split:
it is either genuinely degree zero, or its *entire* support is one-dimensional
after the canonical binary determinant-one shear. -/
inductive DirectClosingCanonicalSquareAxisTerminalCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_ne_zero : face ≠ 0)
      (base_support : IsLongitudinalBaseSupport face)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

  | transverseDegreeZero
      (data : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (H : MvPolynomial (Fin 2) K)
      (H_eq : H = binaryOrdinaryDegreeComponent data.binaryFace 0)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ data.binaryFace.support, d.degree ≤ 0)

  | transverseNonlinearAxis
      (data : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (straight : BinarySingularHessianNonlinearAxisStraighteningData data.binaryFace)

/-- Re-run the already-green A4/A6 terminal reductions on the zero-order core
produced by A9.  This is a local adapter: no new Hessian geometry is proved. -/
theorem DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData.toAxisTerminalCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (core : DirectClosingCanonicalSquareCurvedEliminatedStationaryCoreData C heq) :
    DirectClosingCanonicalSquareAxisTerminalCoreData C heq := by
  cases core with
  | longitudinal D face face_ne_zero base_support source_collision face_linear_zero =>
      exact .longitudinal D face face_ne_zero base_support
        source_collision face_linear_zero
  | transverse data frontier =>
      cases frontier with
      | lowDegree D H hD H_eq H_ne_zero maximal =>
          have hD0 := binaryStationaryLowDegree_zeroJet_forces_degree_zero
            data.binaryFace D H hD H_eq H_ne_zero data.binaryFace_linear_zero
          subst D
          exact .transverseDegreeZero data H H_eq H_ne_zero maximal
      | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .transverseNonlinearAxis data straight
      | nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
          R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero remainder_maximal
          G_homogeneous transverse_sq_zero =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .transverseNonlinearAxis data straight
      | nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
          R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
          G_homogeneous transverse_sq_zero transverse_first_zero =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .transverseNonlinearAxis data straight

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- Exact local geometry remaining after A11 source normalisation. -/
inductive AdaptiveAlignedSmithCanonicalTerminalLocalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop

  | earlySchurRS2Ready
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalAxisCore
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (core :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareAxisTerminalCoreData
          C heq)

  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

  | planarRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

/-- One exact local object now contains every source invariant shared by the
remaining stationary branches and exactly one terminal geometry tag. -/
structure AdaptiveAlignedSmithCanonicalTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalTerminalLocalGeometry stationary

/-- A11 global frontier: every genuinely stationary residue is now one exact
terminal local problem. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTerminalLocalOutcome
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

  | local
      (P : AdaptiveAlignedSmithCanonicalTerminalLocalProblem s)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A11 terminal source assembly.**

All A10 stationary constructors are compressed to one local problem carrying
both common source invariants.  The canonical zero-order curved-eliminated
core is additionally sharpened to degree-zero-or-one-axis terminal form. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreTerminalLocalFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTerminalLocalOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreIntegralZeroFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | earlySchurRS2Ready S clock_eq clock_pos zeros C hlt htangential R =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .earlySchurRS2Ready C hlt htangential R
      }
  | canonicalZeroOrderCurvedEliminated S clock_eq clock_pos zeros C heq core =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .canonicalAxisCore C heq core.toAxisTerminalCore
      }
  | zeroSchurSourceReady S clock_eq clock_pos zeros C source =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .zeroSchurSourceReady C source
      }
  | planarRigid S clock_eq clock_pos zeros hall P hrigid =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .planarRigid hall P hrigid
      }
  | wSquareRigid S clock_eq clock_pos zeros hall P hrigid =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .wSquareRigid hall P hrigid
      }
  | sectionGaugeKilled S clock_eq clock_pos zeros C heq G hkilled =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .sectionGaugeKilled C heq G hkilled
      }
  | sectionGaugeOrderRaised S clock_eq clock_pos zeros C heq G hnew hstrict =>
      exact .local {
        stationary := S
        clock_eq := clock_eq
        clock_pos := clock_pos
        source := S.toTerminalSourcePacket
        geometry := .sectionGaugeOrderRaised C heq G hnew hstrict
      }
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
