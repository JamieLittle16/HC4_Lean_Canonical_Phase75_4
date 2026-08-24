import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareAffineBasePlane
import HC4.Newton.TerminalOneZeroAffineRecovery
import Mathlib.Tactic

/-!
# Converge exact-clock stationary residuals to one low-dimensional packet

The canonical-square wall analysis has now consumed every hidden rank-two
curvature source.  A surviving wall face has Hessian support on either the
marked longitudinal axis or a two-dimensional base plane whose binary Hessian
determinant vanishes.

This file makes the corresponding affine structure explicit: every gradient
component in a complementary direction is a literal scalar polynomial.  It
then folds the equality-wall remainder together with the already-existing
constant-Schur, zero-Schur, and rigid stationary residuals into one lossless
stationary packet.  Rank-two equality-wall curvature is consumed before the
packet is formed.

No terminal extraction or JC2 hypothesis is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Final low-dimensional wall-face data with the affine complementary
structure made literal at the level of first derivatives. -/
inductive DirectClosingCanonicalSquareLowDimensionalGradientData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (m : ℕ)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (hessian_support :
        ∀ i j : Fin 4,
          i ≠ (0 : Fin 4) ∨ j ≠ (0 : Fin 4) →
            HC4.Polynomial.hessian face i j = 0)
      (transverse_gradient_constant :
        ∀ i : Fin 4, i ≠ (0 : Fin 4) →
          MvPolynomial.pderiv i face =
            MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)))

  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (m : ℕ)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index)
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (hessian_support :
        ∀ i j : Fin 4,
          (i ≠ (0 : Fin 4) ∧ i ≠ D.index) ∨
          (j ≠ (0 : Fin 4) ∧ j ≠ D.index) →
            HC4.Polynomial.hessian face i j = 0)
      (base_det_zero :
        binaryDirectionalHessianDet (0 : Fin 4) D.index face = 0)
      (complement_gradient_constant :
        ∀ i : Fin 4,
          i ≠ (0 : Fin 4) → i ≠ D.index →
            MvPolynomial.pderiv i face =
              MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)))

/-- Hessian support on the longitudinal axis forces every transverse gradient
component to be a scalar polynomial. -/
theorem longitudinalLowDimensional_gradient_constant
    (face : MvPolynomial (Fin 4) K)
    (hessian_support :
      ∀ i j : Fin 4,
        i ≠ (0 : Fin 4) ∨ j ≠ (0 : Fin 4) →
          HC4.Polynomial.hessian face i j = 0) :
    ∀ i : Fin 4, i ≠ (0 : Fin 4) →
      MvPolynomial.pderiv i face =
        MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)) := by
  intro i hi
  apply finFour_eq_C_of_all_pderiv_eq_zero
  · simpa [HC4.Polynomial.hessian_apply] using hessian_support i 0 (Or.inl hi)
  · simpa [HC4.Polynomial.hessian_apply] using hessian_support i 1 (Or.inl hi)
  · simpa [HC4.Polynomial.hessian_apply] using hessian_support i 2 (Or.inl hi)
  · simpa [HC4.Polynomial.hessian_apply] using hessian_support i 3 (Or.inl hi)

/-- Hessian support on `(0, ell)` forces every complementary gradient
component to be a scalar polynomial. -/
theorem transverseLowDimensional_gradient_constant
    (ell : Fin 4)
    (face : MvPolynomial (Fin 4) K)
    (hessian_support :
      ∀ i j : Fin 4,
        (i ≠ (0 : Fin 4) ∧ i ≠ ell) ∨
        (j ≠ (0 : Fin 4) ∧ j ≠ ell) →
          HC4.Polynomial.hessian face i j = 0) :
    ∀ i : Fin 4,
      i ≠ (0 : Fin 4) → i ≠ ell →
        MvPolynomial.pderiv i face =
          MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)) := by
  intro i hi0 hiell
  apply finFour_eq_C_of_all_pderiv_eq_zero
  · simpa [HC4.Polynomial.hessian_apply] using
      hessian_support i 0 (Or.inl ⟨hi0, hiell⟩)
  · simpa [HC4.Polynomial.hessian_apply] using
      hessian_support i 1 (Or.inl ⟨hi0, hiell⟩)
  · simpa [HC4.Polynomial.hessian_apply] using
      hessian_support i 2 (Or.inl ⟨hi0, hiell⟩)
  · simpa [HC4.Polynomial.hessian_apply] using
      hessian_support i 3 (Or.inl ⟨hi0, hiell⟩)

/-- Promote the rank-at-most-one Hessian support packet to a literal affine
complementary-gradient normal form. -/
theorem DirectClosingCanonicalSquareLowDimensionalWallFaceData.toGradientData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq) :
    DirectClosingCanonicalSquareLowDimensionalGradientData C heq := by
  cases L with
  | longitudinal D m hm_le face face_eq face_ne_zero hessian_support =>
      exact .longitudinal D m hm_le face face_eq face_ne_zero hessian_support
        (longitudinalLowDimensional_gradient_constant face hessian_support)
  | transverse D hindex m hm_le face face_eq face_ne_zero hessian_support base_det_zero =>
      exact .transverse D hindex m hm_le face face_eq face_ne_zero hessian_support
        base_det_zero
        (transverseLowDimensional_gradient_constant D.index face hessian_support)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## One stationary packet for the exact-clock residual geometry -/

/-- Lossless common packet for the stationary local geometries which remain
after all presently certified curvature exits have been consumed.  The wall
face constructor stores the strengthened literal affine-gradient normal form.
-/
inductive AdaptiveAlignedSmithCanonicalLowDimensionalStationaryPacket
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | earlySchurConstantRS2
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalWallLowDimensional
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareLowDimensionalGradientData
        C heq)

  | zeroSchur
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

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

/-- Residual-convergence output.  All equality-wall rank-two curvature has
already become the certified outer macro.  The historical stationary labels
are merged into one packet; only genuine continuation bookkeeping remains
separate. -/
inductive AdaptiveAlignedSmithCanonicalStationaryConvergenceOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | stationary
      (P : AdaptiveAlignedSmithCanonicalLowDimensionalStationaryPacket s)

  | sectionGauge
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **Converge the frozen exact-clock residual frontier.**

The equality wall is run through both green curvature consumers.  Its rank-two
case is therefore already a macro, while its surviving wall face is promoted
to the explicit affine-gradient normal form above.  The constant-Schur,
zero-Schur and two rigid stationary constructors are folded into the same
lossless packet.  Only section-gauge and outer continuation bookkeeping remain
separate. -/
theorem AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.toStationaryConvergenceOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (R : AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual s) :
    AdaptiveAlignedSmithCanonicalStationaryConvergenceOutcome RR s complexity := by
  cases R with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential H =>
      exact .stationary (.earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential H)

  | canonicalEarlierWall S clock_eq clock_pos C heq wall =>
      rcases
          AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.canonicalEarlierWallLowDimensionalOutcome
            RR complexity hsrepair S clock_eq clock_pos C heq wall with
        ⟨outer, target, hmove, hprogress⟩ |
        ⟨S', clock_eq', clock_pos', C', heq', L⟩ |
        ⟨S', clock_eq', clock_pos', C', heq', G⟩
      · exact .rankTwoMacro outer target hmove hprogress
      · exact .stationary
          (.canonicalWallLowDimensional S' clock_eq' clock_pos' C' heq' L.toGradientData)
      · exact .sectionGauge S' clock_eq' clock_pos' C' heq' G

  | zeroSchur S clock_eq clock_pos C =>
      exact .stationary (.zeroSchur S clock_eq clock_pos C)

  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .stationary (.planarRigid S clock_eq clock_pos hall P hrigid)

  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .stationary (.wSquareRigid S clock_eq clock_pos hall P hrigid)

  | survivingExactClock W clock_eq =>
      exact .survivingExactClock W clock_eq

  | sectionBoundaryInternal Bboundary =>
      exact .sectionBoundaryInternal Bboundary

end

end HC4.Valuation
