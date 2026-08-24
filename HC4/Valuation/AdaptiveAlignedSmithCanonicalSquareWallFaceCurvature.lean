import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareZeroOrderWallFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockAssemblyFrontier
import HC4.Newton.MixedDepartureAdapter
import Mathlib.Tactic

/-!
# Curvature dichotomy for the zero-order canonical square wall face

The zero-order equality-wall face is already known to be affine in the
coordinates complementary to the canonical square axis.  This file turns
that support statement into the exact curvature dichotomy needed by the
restart assembly.

For every complementary direction `V`, the pure second derivative `P_VV`
vanishes.  Hence any nonzero mixed derivative `P_UV` exposes the canonical
negative-square binary Hessian determinant

    det Hess_(U,V) P = -(P_UV)^2 != 0,

and the already-green mixed-departure adapter supplies strict rank-one to
rank-two `RepairProgress`.  If no such mixed derivative exists, the entire
face is affine/separated from all complementary directions.

The final exact-clock wrapper consumes the rank-two branch immediately via
the existing outer rank-two macro.  Thus a canonical earlier wall refines to
exactly one of:

* certified rank-two macro progress;
* a genuinely affine/separated zero-order wall face;
* the already-honest positive section-gauge step.

No new termination measure or geometric hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Exact rank-two source exposed by one mixed derivative on a wall face. -/
structure DirectClosingWallFaceMixedRepairData
    (complexity : ℕ)
    (face : MvPolynomial (Fin 4) K)
    (U V : Fin 4) : Prop where
  nullSecond : directionalSecondDerivative V face = 0
  mixed_ne_zero : directionalMixedDerivative U V face ≠ 0
  progress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  determinantSource :
    binaryDirectionalHessianDet U V face =
      -(directionalMixedDerivative U V face)^2
  determinant_ne_zero : binaryDirectionalHessianDet U V face ≠ 0
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

/-- A null pure second derivative plus a nonzero mixed derivative is already
exactly the source expected by the existing mixed-departure adapter.  We use
`b = 1`, so the preterminal linear source is literally the null second
derivative. -/
theorem directClosingWallFaceMixedRepairData_of_mixed
    (complexity : ℕ)
    (face : MvPolynomial (Fin 4) K)
    (U V : Fin 4)
    (hVV : directionalSecondDerivative V face = 0)
    (hUV : directionalMixedDerivative U V face ≠ 0) :
    DirectClosingWallFaceMixedRepairData complexity face U V := by
  have hsource :
      preterminalSchurLinearSource (1 : K) V face = 0 := by
    simp [preterminalSchurLinearSource, hVV]
  have hpacket :=
    preterminal_mixedPivot_matches_repairProgress_with_source
      (1 : K) one_ne_zero U V face complexity hsource hUV
  have hprogress :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) := by
    simpa using hpacket.1
  exact {
    nullSecond := hVV
    mixed_ne_zero := hUV
    progress := hprogress
    determinantSource := hpacket.2.1
    determinant_ne_zero := hpacket.2.2
    measure_lt := repairState_measure_lt_of_progress hprogress
  }

/-- Genuine affine/separated zero-order wall face, with all provenance
retained explicitly.  This is a proposition in its own right rather than a
proposition *computed from* the Prop-valued wall-face certificate; that avoids
large elimination from `Prop` while keeping the complete face data. -/
inductive DirectClosingCanonicalSquareAffineSeparatedWallFaceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (d : Fin 4 →₀ ℕ)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (m : ℕ)
      (hm : directClosingLongitudinalTransverseDegree d = m)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (support_degree :
        ∀ e ∈ face.support,
          directClosingLongitudinalTransverseDegree e = m)
      (transverseHessian_zero :
        ∀ j k : Fin 3,
          MvPolynomial.pderiv k.succ (MvPolynomial.pderiv j.succ face) = 0)
      (mixed_zero :
        ∀ U V : Fin 4, V ≠ (0 : Fin 4) →
          directionalMixedDerivative U V face = 0)

  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (m : ℕ)
      (hm : directClosingTransverseComplementDegree D.index d = m)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index)
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (support_degree :
        ∀ e ∈ face.support,
          directClosingTransverseComplementDegree D.index e = m)
      (complementHessian_zero :
        ∀ i j : Fin 4,
          i ≠ (0 : Fin 4) → i ≠ D.index →
          j ≠ (0 : Fin 4) → j ≠ D.index →
          MvPolynomial.pderiv j (MvPolynomial.pderiv i face) = 0)
      (mixed_zero :
        ∀ U V : Fin 4,
          V ≠ (0 : Fin 4) → V ≠ D.index →
          directionalMixedDerivative U V face = 0)

/-- In the longitudinal wall-face branch, every non-marked pure second
derivative vanishes. -/
theorem longitudinalWallFace_secondDerivative_zero
    (face : MvPolynomial (Fin 4) K)
    (hzero :
      ∀ j k : Fin 3,
        MvPolynomial.pderiv k.succ (MvPolynomial.pderiv j.succ face) = 0)
    (V : Fin 4)
    (hV : V ≠ (0 : Fin 4)) :
    directionalSecondDerivative V face = 0 := by
  unfold directionalSecondDerivative
  fin_cases V
  · exact (hV rfl).elim
  · simpa using hzero (0 : Fin 3) (0 : Fin 3)
  · simpa using hzero (1 : Fin 3) (1 : Fin 3)
  · simpa using hzero (2 : Fin 3) (2 : Fin 3)

/-- **Wall-face curvature dichotomy.**
A zero-order wall face either has a genuine mixed pivot, already packaged as
canonical rank-one to rank-two repair progress with its exact determinant
source, or it is completely affine/separated from its complementary
coordinates. -/
theorem DirectClosingCanonicalSquareZeroOrderWallFaceData.mixedRepair_or_affineSeparated
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (F : DirectClosingCanonicalSquareZeroOrderWallFaceData C heq)
    (complexity : ℕ) :
    (∃ (face : MvPolynomial (Fin 4) K) (U V : Fin 4),
      DirectClosingWallFaceMixedRepairData complexity face U V) ∨
      DirectClosingCanonicalSquareAffineSeparatedWallFaceData C heq := by
  cases F with
  | longitudinal D d hdSpecial m hm hm_le face face_eq face_ne_zero
      support_degree transverseHessian_zero =>
      by_cases hmixed :
          ∃ U V : Fin 4,
            V ≠ (0 : Fin 4) ∧
            directionalMixedDerivative U V face ≠ 0
      · rcases hmixed with ⟨U, V, hV, hUV⟩
        have hVV : directionalSecondDerivative V face = 0 :=
          longitudinalWallFace_secondDerivative_zero face
            transverseHessian_zero V hV
        left
        exact ⟨face, U, V,
          directClosingWallFaceMixedRepairData_of_mixed
            complexity face U V hVV hUV⟩
      · right
        refine .longitudinal D d hdSpecial m hm hm_le face face_eq face_ne_zero
          support_degree transverseHessian_zero ?_
        intro U V hV
        by_contra hUV
        exact hmixed ⟨U, V, hV, hUV⟩

  | transverse D hindex d hdSpecial m hm hm_le face face_eq face_ne_zero
      support_degree complementHessian_zero =>
      by_cases hmixed :
          ∃ U V : Fin 4,
            V ≠ (0 : Fin 4) ∧ V ≠ D.index ∧
            directionalMixedDerivative U V face ≠ 0
      · rcases hmixed with ⟨U, V, hV0, hVindex, hUV⟩
        have hVV : directionalSecondDerivative V face = 0 := by
          unfold directionalSecondDerivative
          exact complementHessian_zero V V
            hV0 hVindex hV0 hVindex
        left
        exact ⟨face, U, V,
          directClosingWallFaceMixedRepairData_of_mixed
            complexity face U V hVV hUV⟩
      · right
        refine .transverse D hindex d hdSpecial m hm hm_le face face_eq face_ne_zero
          support_degree complementHessian_zero ?_
        intro U V hV0 hVindex
        by_contra hUV
        exact hmixed ⟨U, V, hV0, hVindex, hUV⟩

/-- Refined equality-wall output after curvature has been consumed. -/
inductive DirectClosingCanonicalSquareEqualityCurvatureFrontier
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (complexity : ℕ) : Prop
  | rankTwo
      (face : MvPolynomial (Fin 4) K)
      (U V : Fin 4)
      (repair : DirectClosingWallFaceMixedRepairData complexity face U V)
  | affineFace
      (A : DirectClosingCanonicalSquareAffineSeparatedWallFaceData C heq)
  | sectionGauge
      (G : DirectClosingPositiveSectionGaugeStep C)

/-- Consume the curvature of the equality wall before any global assembly. -/
theorem DirectClosingCanonicalSquareEarlierWallNormalForm.toCurvatureFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (N : DirectClosingCanonicalSquareEarlierWallNormalForm C heq)
    (complexity : ℕ) :
    DirectClosingCanonicalSquareEqualityCurvatureFrontier C heq complexity := by
  cases N.toAffineFaceFrontier with
  | wallFace F =>
      rcases F.mixedRepair_or_affineSeparated complexity with hrepair | haffine
      · rcases hrepair with ⟨face, U, V, repair⟩
        exact .rankTwo face U V repair
      · exact .affineFace haffine
  | sectionGauge G =>
      exact .sectionGauge G

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Exact-clock consumption of the mixed branch -/

/-- Assembly-facing refinement of the `canonicalEarlierWall` residual.  The
mixed-curvature branch is immediately upgraded to the already-green exact
outer rank-two macro.  Only a genuinely affine wall face or an honest
positive section-gauge step remains. -/
inductive AdaptiveAlignedSmithCanonicalEarlierWallCurvatureOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | affineFace
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (A : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareAffineSeparatedWallFaceData
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

/-- Exact-clock canonical-earlier-wall refinement with the rank-two branch
fully consumed. -/
theorem AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.canonicalEarlierWallCurvatureOutcome
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
    AdaptiveAlignedSmithCanonicalEarlierWallCurvatureOutcome RR s complexity := by
  cases wall.toCurvatureFrontier complexity with
  | rankTwo face U V repair =>
      rcases S.blocker.aligned.exists_outerRankTwoRepairMacro
          RR s complexity hsrepair clock_eq repair.progress with
        ⟨outer, target, hmove, hprogress⟩
      exact .rankTwoMacro outer target hmove hprogress
  | affineFace A =>
      exact .affineFace S clock_eq clock_pos C heq A
  | sectionGauge G =>
      exact .sectionGauge S clock_eq clock_pos C heq G

end

end HC4.Valuation
