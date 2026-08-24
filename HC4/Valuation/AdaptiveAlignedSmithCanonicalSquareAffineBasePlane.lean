import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareWallFaceCurvature
import Mathlib.Tactic

/-!
# Base-plane reduction of an affine canonical-square wall face

After the mixed-curvature dichotomy, an affine wall face has no Hessian entry
involving a complementary direction.  In the transverse-square case there is
still one possible source of rank two: the intrinsic binary Hessian determinant
on the surviving base plane `(0, ell)`.

This file consumes that final curvature source.  If the base-plane determinant
is nonzero, the already-green rank-one to rank-two repair step is available and
is immediately upgradeable to the exact-clock outer macro.  Otherwise the face
is retained as a genuinely low-dimensional stationary object:

* longitudinal square: the Hessian is supported only on the marked axis `0`;
* transverse square: the Hessian is supported on the base plane `(0, ell)` and
  the determinant of that base block is zero.

Thus no rank-two curvature remains hidden inside the affine wall-face branch.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Source-honest rank-two certificate coming from the surviving base-plane
binary Hessian determinant of an affine wall face. -/
structure DirectClosingWallFaceBasePlaneRankTwoRepairData
    (complexity : ℕ)
    (face : MvPolynomial (Fin 4) K)
    (i j : Fin 4) : Prop where
  determinant_ne_zero :
    binaryDirectionalHessianDet i j face ≠ 0
  progress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

/-- A nonzero binary Hessian determinant is an honest source certificate for
canonical rank-one to rank-two repair progress. -/
theorem directClosingWallFaceBasePlaneRankTwoRepairData_of_det_ne_zero
    (complexity : ℕ)
    (face : MvPolynomial (Fin 4) K)
    (i j : Fin 4)
    (hdet : binaryDirectionalHessianDet i j face ≠ 0) :
    DirectClosingWallFaceBasePlaneRankTwoRepairData complexity face i j := by
  have hprogress :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) := by
    simpa [preterminalRankOneRepairState, preterminalRankTwoRepairState,
      rankOneRepairState, rankTwoRepairState] using
      (preterminal_rankOne_to_rankTwo_repairProgress complexity)
  exact {
    determinant_ne_zero := hdet
    progress := hprogress
    measure_lt := repairState_measure_lt_of_progress hprogress
  }

/-- Final low-dimensional wall-face packet after every possible rank-two
curvature source has been consumed. -/
inductive DirectClosingCanonicalSquareLowDimensionalWallFaceData
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

/-- In the longitudinal affine-face branch, every Hessian entry involving a
non-marked direction vanishes. -/
theorem longitudinalAffineWallFace_hessian_support
    (face : MvPolynomial (Fin 4) K)
    (hmixed :
      ∀ U V : Fin 4, V ≠ (0 : Fin 4) →
        directionalMixedDerivative U V face = 0) :
    ∀ i j : Fin 4,
      i ≠ (0 : Fin 4) ∨ j ≠ (0 : Fin 4) →
        HC4.Polynomial.hessian face i j = 0 := by
  intro i j hij
  rw [HC4.Polynomial.hessian_apply]
  rcases hij with hi | hj
  · exact hmixed j i hi
  · rw [← pderiv_comm_commRing i j face]
    exact hmixed i j hj

/-- In the transverse affine-face branch, every Hessian entry involving a
coordinate complementary to the base plane `(0, ell)` vanishes. -/
theorem transverseAffineWallFace_hessian_support
    (ell : Fin 4)
    (face : MvPolynomial (Fin 4) K)
    (hmixed :
      ∀ U V : Fin 4,
        V ≠ (0 : Fin 4) → V ≠ ell →
          directionalMixedDerivative U V face = 0) :
    ∀ i j : Fin 4,
      (i ≠ (0 : Fin 4) ∧ i ≠ ell) ∨
      (j ≠ (0 : Fin 4) ∧ j ≠ ell) →
        HC4.Polynomial.hessian face i j = 0 := by
  intro i j hij
  rw [HC4.Polynomial.hessian_apply]
  rcases hij with hi | hj
  · exact hmixed j i hi.1 hi.2
  · rw [← pderiv_comm_commRing i j face]
    exact hmixed i j hj.1 hj.2

/-- **Final affine-wall curvature dichotomy.**  After complementary mixed
curvature has vanished, a transverse wall face either still has nonzero
intrinsic base-plane determinant, or the whole Hessian is supported on a
rank-at-most-one base plane.  A longitudinal wall face is already of the
latter form. -/
theorem DirectClosingCanonicalSquareAffineSeparatedWallFaceData.basePlaneRepair_or_lowDimensional
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (A : DirectClosingCanonicalSquareAffineSeparatedWallFaceData C heq)
    (complexity : ℕ) :
    (∃ (face : MvPolynomial (Fin 4) K) (i j : Fin 4),
      DirectClosingWallFaceBasePlaneRankTwoRepairData complexity face i j) ∨
      DirectClosingCanonicalSquareLowDimensionalWallFaceData C heq := by
  cases A with
  | longitudinal D d hdSpecial m hm hm_le face face_eq face_ne_zero
      support_degree transverseHessian_zero mixed_zero =>
      right
      exact .longitudinal D m hm_le face face_eq face_ne_zero
        (longitudinalAffineWallFace_hessian_support face mixed_zero)

  | transverse D hindex d hdSpecial m hm hm_le face face_eq face_ne_zero
      support_degree complementHessian_zero mixed_zero =>
      by_cases hdet :
          binaryDirectionalHessianDet (0 : Fin 4) D.index face = 0
      · right
        exact .transverse D hindex m hm_le face face_eq face_ne_zero
          (transverseAffineWallFace_hessian_support D.index face mixed_zero)
          hdet
      · left
        exact ⟨face, (0 : Fin 4), D.index,
          directClosingWallFaceBasePlaneRankTwoRepairData_of_det_ne_zero
            complexity face (0 : Fin 4) D.index hdet⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Exact-clock consumption of the base-plane rank-two branch -/

/-- Equality-wall output after *all* curvature, including intrinsic base-plane
curvature, has been consumed. -/
inductive AdaptiveAlignedSmithCanonicalEarlierWallLowDimensionalOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | lowDimensionalFace
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareLowDimensionalWallFaceData
        C heq)
  | sectionGauge
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)

/-- Consume the final intrinsic base-plane determinant in the affine equality
wall.  The only non-macro equality-wall outputs left are a low-dimensional
rank-at-most-one Hessian face or the already-honest positive section gauge. -/
theorem AdaptiveAlignedSmithCanonicalEarlierWallCurvatureOutcome.toLowDimensionalOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (H : AdaptiveAlignedSmithCanonicalEarlierWallCurvatureOutcome RR s complexity) :
    AdaptiveAlignedSmithCanonicalEarlierWallLowDimensionalOutcome RR s complexity := by
  cases H with
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | affineFace S clock_eq clock_pos C heq A =>
      rcases A.basePlaneRepair_or_lowDimensional complexity with hrepair | hlow
      · rcases hrepair with ⟨face, i, j, repair⟩
        rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
            RR s complexity hsrepair clock_eq repair.progress with
          ⟨outer, target, hmove, hprogress⟩
        exact .rankTwoMacro outer target hmove hprogress
      · exact .lowDimensionalFace S clock_eq clock_pos C heq hlow
  | sectionGauge S clock_eq clock_pos C heq G =>
      exact .sectionGauge S clock_eq clock_pos C heq G

/-- Direct assembly-facing equality-wall reduction from the original residual
packet. -/
theorem AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.canonicalEarlierWallLowDimensionalOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
    (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
    (wall :
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWallNormalForm
        C heq) :
    AdaptiveAlignedSmithCanonicalEarlierWallLowDimensionalOutcome RR s complexity := by
  exact
    (AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.canonicalEarlierWallCurvatureOutcome
      RR complexity hsrepair S clock_eq clock_pos C heq wall).toLowDimensionalOutcome
      RR complexity hsrepair

end

end HC4.Valuation
