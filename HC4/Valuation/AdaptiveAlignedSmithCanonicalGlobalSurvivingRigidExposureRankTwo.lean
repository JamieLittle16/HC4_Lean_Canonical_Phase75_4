import HC4.Valuation.AdaptiveAlignedSmithRigidPacketExposureClosing
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingRankTwoAbsoluteScale
import Mathlib.Tactic

/-!
# A18.4.26: keep surviving-rigid rank-two geometry on the actual exposure family

The historical surviving-rigid closure constructs an honest adaptive Smith
exposure and then an exact zero-Schur four-block on that exposed family.  In
the preterminal residual-clock branch, however, the old interface forgets the
exposure and exports only the abstract rank-one -> rank-two `RepairProgress`.
A later dispatcher can therefore attach that repair tag to the earlier aligned
state rather than to the family on which the zero-Schur geometry was proved.

This file removes that abstraction leak.

The marked-point dichotomy is taken *before* rank promotion.  A noncanonical
exposure is returned as the genuine section-boundary event already present in
the geometry.  Only a canonical exposure is converted to an adaptive restart
state.  On that exact state we retain

* the concrete left/right rigid packet chart which produced the zero-Schur
  four-block;
* the positive residual rank-one Schur clock;
* the strict preterminal inequality; and
* the resulting nonzero off-diagonal first coefficient.

The promoted target is then the canonical exposed state, recorded at the
actual absolute exposure scale, with only its repair coordinate changed to
rank two.  Thus the recursive target family is literally the family on which
the retained zero-Schur witness was proved.

No homogeneity assumption and no repair-only relabel of the pre-exposure
family is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact chart provenance for the zero-Schur block produced by one canonical
surviving-rigid Smith exposure. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingRigidExposureZeroSchurChart
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (Z : ExactZeroSchurFourBlockData K) : Type (u + 1)

  | left
      (pivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 P.degree P.packet).LeftPivot)
      (zeroSchur_eq : Z = R.leftZeroSchurData s W P d hD pivot)

  | right
      (pivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 P.degree P.packet).RightAxisPivot)
      (zeroSchur_eq : Z = R.rightZeroSchurData s W P d hD pivot)

/-- Geometry which genuinely justifies a rank-one -> rank-two promotion on a
canonical surviving-rigid exposure.

The residual clock is tied to the concrete zero-Schur block by the final
`residualOrigin` field, so a bare repair certificate cannot inhabit this type. -/
structure AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ) : Type (u + 1) where
  exposure : AdaptiveSurvivingWallExposureData
    (W.original.aligned.toAdaptiveState s) W.wall
  canonicalSpecial :
    polynomialSectionSpecialPoint exposure.rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  zeroSchur : ExactZeroSchurFourBlockData K
  chart : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureZeroSchurChart
    R hD exposure zeroSchur
  residual : ExactRankOneSchurClockAt K
  residual_pos : 0 < zeroSchur.toClock.residualDefect
  residual_defect : residual.defect = zeroSchur.toClock.residualDefect
  residualOrigin :
    (∃ pivot : zeroSchur.toClock.tailSeries.LeftPivot,
      residual = zeroSchur.toClock.toRankOneClockLeft residual_pos pivot) ∨
    (∃ pivot : zeroSchur.toClock.tailSeries.RightAxisPivot,
      residual = zeroSchur.toClock.toRankOneClockRight residual_pos pivot)
  preterminal : residual.firstOrder < residual.defect

namespace AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry

/-- The retained residual clock has an actual nonzero mixed first coefficient. -/
theorem offDiag_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      W P R hD complexity) :
    G.residual.series.offDiag.coeff G.residual.firstOrder ≠ 0 :=
  G.residual.offDiag_coeff_firstOrder_ne_zero_of_preterminal G.preterminal

/-- The finite repair transition is derived only after the exposure geometry
has been retained. -/
theorem repairProgress
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    {complexity : ℕ}
    (_G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      W P R hD complexity) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity) :=
  rankOne_to_rankTwo_repairProgress complexity

end AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry

/-- Sound local split of one surviving rigid packet.

Relative to the historical theorem, the marked-point boundary is exposed
before any rank promotion and the rank-two branch retains the concrete
zero-Schur residual clock. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingRigidExposureGeometricOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : (W.original.aligned.toAdaptiveState s).defect = 0)

  | boundary
      (exposure : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall)
      (boundary : Nonempty (AdaptiveSmithExposureSectionBoundary exposure))

  | rankTwoGeometry
      (geometry : Nonempty
        (AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
          W P R hD complexity))

  | canonicalClosing
      (closing : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
        (K := K) s W P R)
      (canonicalSpecial :
        polynomialSectionSpecialPoint closing.exposure.rightSection =
          coordinateAxisPoint (K := K) (0 : Fin 4))

/-- **A18.4.26 local geometry retention.**

The proof deliberately repeats the small two-stage zero-Schur clock split
instead of calling `rankTwoProgress_or_closing`, because that older theorem
forgets the residual clock on its left branch. -/
theorem AdaptiveAlignedSmithRigidPacketEndpoint.geometricExposureOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalSurvivingRigidExposureGeometricOutcome
      W P R hD complexity := by
  rcases W.zeroDefect_or_exposure s with hzero | hexposure
  · exact .zeroDefect hzero
  · let d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall :=
      Classical.choice hexposure
    rcases d.canonicalSpecial_or_boundary with hspecial | hboundary
    · rcases R.pivot s W P with hpivot | hpivot
      · let Z : ExactZeroSchurFourBlockData K :=
          R.leftZeroSchurData s W P d hD hpivot
        let E := Z.toClock
        by_cases hres0 : E.residualDefect = 0
        · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
              (K := K) s W P R := {
            exposure := d
            zeroSchur := Z
            closing := Or.inl
              ⟨hres0, E.tail_constant_det_ne_zero_of_residual_zero hres0⟩
          }
          exact .canonicalClosing C (by simpa [C] using hspecial)
        · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
          rcases E.tail_pivot_of_residual_pos hres with htail | htail
          · let S := E.toRankOneClockLeft hres htail
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                chart := .left hpivot rfl
                residual := S
                residual_pos := by simpa [E] using hres
                residual_defect := rfl
                residualOrigin := Or.inl ⟨htail, rfl⟩
                preterminal := hpre
              }⟩
            · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
                  (K := K) s W P R := {
                exposure := d
                zeroSchur := Z
                closing := Or.inr ⟨S, hres, rfl, hclose,
                  S.series.transverse_nonzero_at_first S.hasTransverse |>.imp
                    (fun h => by
                      change S.series.offDiag.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)
                    (fun h => by
                      change S.series.kernel.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)⟩
              }
              exact .canonicalClosing C (by simpa [C] using hspecial)
          · let S := E.toRankOneClockRight hres htail
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                chart := .left hpivot rfl
                residual := S
                residual_pos := by simpa [E] using hres
                residual_defect := rfl
                residualOrigin := Or.inr ⟨htail, rfl⟩
                preterminal := hpre
              }⟩
            · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
                  (K := K) s W P R := {
                exposure := d
                zeroSchur := Z
                closing := Or.inr ⟨S, hres, rfl, hclose,
                  S.series.transverse_nonzero_at_first S.hasTransverse |>.imp
                    (fun h => by
                      change S.series.offDiag.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)
                    (fun h => by
                      change S.series.kernel.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)⟩
              }
              exact .canonicalClosing C (by simpa [C] using hspecial)

      · let Z : ExactZeroSchurFourBlockData K :=
          R.rightZeroSchurData s W P d hD hpivot
        let E := Z.toClock
        by_cases hres0 : E.residualDefect = 0
        · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
              (K := K) s W P R := {
            exposure := d
            zeroSchur := Z
            closing := Or.inl
              ⟨hres0, E.tail_constant_det_ne_zero_of_residual_zero hres0⟩
          }
          exact .canonicalClosing C (by simpa [C] using hspecial)
        · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
          rcases E.tail_pivot_of_residual_pos hres with htail | htail
          · let S := E.toRankOneClockLeft hres htail
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                chart := .right hpivot rfl
                residual := S
                residual_pos := by simpa [E] using hres
                residual_defect := rfl
                residualOrigin := Or.inl ⟨htail, rfl⟩
                preterminal := hpre
              }⟩
            · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
                  (K := K) s W P R := {
                exposure := d
                zeroSchur := Z
                closing := Or.inr ⟨S, hres, rfl, hclose,
                  S.series.transverse_nonzero_at_first S.hasTransverse |>.imp
                    (fun h => by
                      change S.series.offDiag.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)
                    (fun h => by
                      change S.series.kernel.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)⟩
              }
              exact .canonicalClosing C (by simpa [C] using hspecial)
          · let S := E.toRankOneClockRight hres htail
            rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
            · exact .rankTwoGeometry ⟨{
                exposure := d
                canonicalSpecial := hspecial
                zeroSchur := Z
                chart := .right hpivot rfl
                residual := S
                residual_pos := by simpa [E] using hres
                residual_defect := rfl
                residualOrigin := Or.inr ⟨htail, rfl⟩
                preterminal := hpre
              }⟩
            · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
                  (K := K) s W P R := {
                exposure := d
                zeroSchur := Z
                closing := Or.inr ⟨S, hres, rfl, hclose,
                  S.series.transverse_nonzero_at_first S.hasTransverse |>.imp
                    (fun h => by
                      change S.series.offDiag.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)
                    (fun h => by
                      change S.series.kernel.coeff S.firstOrder ≠ 0 at h
                      rw [hclose] at h
                      exact h)⟩
              }
              exact .canonicalClosing C (by simpa [C] using hspecial)
    · exact .boundary d hboundary

/-- Global rank-two continuation on the *actual canonical exposure family*.
The recursive target is recorded on the exact exposure family together with a
certified ramified presentation from the caller's source state.  The latter is
intentionally stored directly: callers may be either before the aligned
presentation or already at that presented state. -/
structure AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
    W P R hD complexity
  exposed : ScaleAwareAdaptiveGeometricRestartState (K := K)
  exposed_family : exposed.family = geometry.exposure.family
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq : target = exposed.withRepairOnly (rankTwoRepairState complexity)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove exposed s
  exposedProgress : CertifiedSameScaleEpisodeProgress RR target exposed
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- Generic clock-aware constructor.  If the retained aligned endpoint has
clock `q * s.rawDefect`, the canonical exposure is a pure presentation from
`s` with total ramification `exposure.R * q`. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometryAtClock
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (q : ℕ)
    (hq : 0 < q)
    (hclock : W.original.aligned.endpoint.defect = q * s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      W P R hD complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
      RR s W P R hD complexity := by
  let exposedOrd := G.exposure.toAdaptiveState G.canonicalSpecial
  let exposed := exposedOrd.toScaleAwareAt
    ((G.exposure.ramification.R * q) * s.scale)
    (Nat.mul_pos
      (Nat.mul_pos G.exposure.ramification.R_pos hq) s.scale_pos)
  let target := exposed.withRepairOnly (rankTwoRepairState complexity)

  have hsource : HasCertifiedRamifiedEpisodeInternalMove exposed s := by
    change Nonempty (CertifiedRamifiedEpisodeInternalMove exposed s)
    exact ⟨{
      ramification := G.exposure.ramification.R * q
      ramification_pos := Nat.mul_pos G.exposure.ramification.R_pos hq
      scale_eq := by rfl
      raw_eq := by
        change G.exposure.defect =
          (G.exposure.ramification.R * q) * s.rawDefect
        rw [G.exposure.canonical_defect_eq_ramified_aligned W, hclock]
        ac_rfl
      degreeCap_eq := by rfl
      sourceComplexity_eq := by rfl
      repair_eq := by rfl
    }⟩

  have hexposedRepair : exposed.repair = rankOneRepairState complexity := by
    change s.repair = rankOneRepairState complexity
    exact hsrepair

  have hpresented : CertifiedSameScaleEpisodeProgress RR target exposed := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
        hexposedRepair] using
        rankOne_to_rankTwo_repairProgress complexity

  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      hsrepair] using
      repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    geometry := G
    exposed := exposed
    exposed_family := rfl
    target := target
    target_eq := rfl
    sourcePresentation := hsource
    exposedProgress := hpresented
    globalProgress := hglobal
  }

/-- Direct-source constructor: the aligned endpoint is at the canonical outer
clock `alignedSmithRamificationIndex * s.rawDefect`. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock : W.original.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      W P R hD complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
      RR s W P R hD complexity :=
  AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometryAtClock
    RR W P R hD complexity hsrepair
      alignedSmithRamificationIndex alignedSmithRamificationIndex_pos hclock G

/-- Presented-source constructor: the retained aligned endpoint is already the
caller's scale-aware state, so its clock is exactly `s.rawDefect`. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofPresentedGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock : W.original.aligned.endpoint.defect = s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      W P R hD complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
      RR s W P R hD complexity :=
  AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometryAtClock
    RR W P R hD complexity hsrepair 1 (by omega) (by simpa using hclock) G

namespace AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress

/-- Regression theorem: the recursive target family is exactly the canonical
Smith-exposure family, not the earlier aligned family with a changed tag. -/
@[simp]
theorem target_family
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
      RR s W P R hD complexity) :
    D.target.family = D.geometry.exposure.family := by
  rw [D.target_eq]
  change D.exposed.family = D.geometry.exposure.family
  exact D.exposed_family

end AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress

end

end HC4.Valuation