import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingTraceReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingRigidElimination
import Mathlib.Tactic

/-!
# A18.4.10: collapse the concrete surviving packet residue

A18.4.9 exposes three concrete survivors of a leading `survivingExactClock`
provenance leaf: degree-two boundary, degree-two saturation, and a rigid packet.
The first two already arise from one actual adaptive Smith exposure.  The rigid
packet can be pushed through its already-green exposure-closing theorem:

* zero aligned defect reflects to zero raw defect on the original source;
* genuine rank-two repair is lifted to the honest aligned absolute scale and
  composed with the certified aligned presentation;
* the residual closing exposure is either a genuine marked-point boundary or
  has canonical special point and coordinate `3` absent from its special
  fibre.

Consequently all three old packet constructors collapse to just two common
source-honest exposure objects: boundary exposure and kernel-free canonical
exposure.  The aligned clock equation is retained on both objects; it is the
provenance needed by the next patch to compare the exposure clock with the
original source without resetting scale.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A genuine section-boundary event on an actual surviving-wall Smith
exposure.  No degree-two assumption remains in this packaging. -/
structure AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s
  exposure : AdaptiveSurvivingWallExposureData
    (W.original.aligned.toAdaptiveState s) W.wall
  boundary : Nonempty (AdaptiveSmithExposureSectionBoundary exposure)

/-- A canonical surviving-wall Smith exposure whose special fibre is free of
coordinate `3`.  The generic saturated-kernel theorem applies immediately to
`exposure.toAdaptiveState canonicalSpecial`; what remains globally is to
account honestly for the exposure clock relative to the incoming source. -/
structure AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s
  exposure : AdaptiveSurvivingWallExposureData
    (W.original.aligned.toAdaptiveState s) W.wall
  canonicalSpecial :
    polynomialSectionSpecialPoint exposure.rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  specialFiber_free_three :
    ∀ d ∈
        (polynomialFamilySpecialFiber
          (exposure.toAdaptiveState canonicalSpecial).family).support,
      d (3 : Fin 4) = 0

/-- The degree-two saturated endpoint was using its quadratic packet only to
prove that coordinate `3` is absent from the exposed special fibre.  Package
exactly that common geometric content. -/
noncomputable def AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint.toGlobalKernelFreeExposure
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W) :
    AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
      (K := K) s where
  W := W
  exposure := S.exposure
  canonicalSpecial := S.canonicalSpecial
  specialFiber_free_three := by
    intro d hd
    let a := W.original.aligned.toAdaptiveState s
    have hsfeq :=
      S.exposure.toAdaptiveState_specialFiber S.canonicalSpecial
    have hd' :
        d ∈
          (smithSubfacePolynomial (1 : Fin 4) 2 3
            (W.balancedSubface s) a.normalizedSpecialFiber).support := by
      have hd0 :
          d ∈
            (smithSubfacePolynomial (1 : Fin 4) 2 3
              (smithSymmetricBalancedSubface
                (smithProjectedSupport
                  (1 : Fin 4) 2 3 a.normalizedSpecialFiber)
                W.wall.level W.wall.base)
              a.normalizedSpecialFiber).support := by
        rw [← hsfeq]
        exact hd
      simpa [AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface, a] using hd0
    exact
      quadraticSmithSubface_free_three
        (W.balancedSubface s) a.normalizedSpecialFiber P.quadratic d hd'

/-- A degree-two boundary endpoint is already the generic exposure-boundary
object; forget only the degree-two packet annotation. -/
noncomputable def AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint.toGlobalExposureBoundary
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    (B : AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint (K := K) s W) :
    AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) s where
  W := W
  exposure := B.exposure
  boundary := B.boundary

/-- Final surviving-head frontier after the raw packet distinctions have been
collapsed to their common exposure geometry. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSurvivingGeometryReducedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
          RR s complexity))

  | exposureBoundary
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (clock_eq :
        E.W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | kernelFreeExposure
      (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
        (K := K) s)
      (clock_eq :
        E.W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | blockedPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR s target)

/-- **A18.4.10 surviving geometry reduction.**

The rigid packet is eliminated completely.  Its zero and genuine rank-two
repair exits are consumed at the original source scale; only the same two
exposure geometries already present in the degree-two branch survive. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalSurvivingGeometryReducedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingGeometryReducedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalSurvivingHeadReducedFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D

  | degreeTwoBoundary W P hD B clock_eq =>
      exact .exposureBoundary B.toGlobalExposureBoundary clock_eq

  | degreeTwoSaturated W P hD S clock_eq =>
      exact .kernelFreeExposure
        (S.toGlobalKernelFreeExposure P) clock_eq

  | rigidPacket W P hD R clock_eq =>
      rcases
          R.zeroDefect_or_rankTwoProgress_or_closing
            s W P hD complexity with
        hzero | hrepair | hclosing

      · have hsZero : s.rawDefect = 0 :=
          W.source_rawDefect_eq_zero_of_aligned clock_eq hzero
        exact .zeroDefectReentry hsZero
          (s.exists_globalZeroDefectReentryData hsZero)

      · let a := W.original.aligned.toAdaptiveState s
        have hastage : a.repair = rankOneRepairState complexity := by
          simpa [a] using hsrepair
        rcases
            a.exists_certifiedRankTwoRepairSuccessor
              RR complexity hastage hrepair with
          ⟨t, hfixed⟩
        let outer := W.original.aligned.toOuterScaleAwareState s
        let target := t.toScaleAwareAt outer.scale outer.scale_pos
        have hmove : HasCertifiedRamifiedEpisodeInternalMove outer s := by
          exact
            ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq
              s clock_eq⟩
        have hlift :=
          CertifiedFixedScaleEpisodeProgress.toSameScaleAt
            (K := K) RR hfixed outer.scale outer.scale_pos
        have hsource :
            a.toScaleAwareAt outer.scale outer.scale_pos = outer := by
          dsimp [a, outer]
          exact
            W.original.aligned.toAdaptiveState_toScaleAwareAt_eq_outer s
        rw [hsource] at hlift
        have hprogress :
            CertifiedSameScaleEpisodeProgress RR target outer := by
          simpa [target] using hlift
        exact .ramifiedStrictMacro (.mk outer target hmove hprogress)

      · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
            (K := K) s W P R := Classical.choice hclosing
        rcases C.exposure.canonicalSpecial_or_boundary with
          hspecial | hboundary

        · let E :
              AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
                (K := K) s :=
            {
              W := W
              exposure := C.exposure
              canonicalSpecial := hspecial
              specialFiber_free_three := by
                simpa using C.specialFiber_free_three hspecial
            }
          exact .kernelFreeExposure E clock_eq

        · let E :
              AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
                (K := K) s :=
            {
              W := W
              exposure := C.exposure
              boundary := hboundary
            }
          exact .exposureBoundary E clock_eq

  | blockedPresentation target trace =>
      exact .blockedPresentation target trace

end

end HC4.Valuation
