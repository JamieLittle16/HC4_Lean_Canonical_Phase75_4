import HC4.Valuation.AdaptiveAlignedSmithCanonicalRigidReducedDispatcher
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import HC4.Valuation.AdaptiveSectionBoundaryReentry
import Mathlib.Tactic

/-!
# Eliminate the surviving rigid closing by quadratic-face kernel freeness

The surviving rigid-packet exposure carries more information than its local
zero-Schur closing clock needs.  Its special fibre is the *complete symmetric
balanced Smith subface*, and the retained persistent-packet endpoint proves
that every projected exponent of this subface is one of the three planar
quadratic patterns.  Hence coordinate `3` is absent from the entire exposed
special fibre.

There are therefore only two geometric possibilities for the honest adaptive
exposure:

* a transverse special-point boundary appears, in which case the existing
  determinant-one boundary shear gives ordinary adaptive re-entry;
* the right special point remains `e0`, in which case the exposure is an
  ordinary adaptive state with coordinate-3-free special fibre, and the
  generic saturated-kernel theorem gives certified fixed-scale strict
  progress.

Thus the surviving rigid zero-Schur closing constructor is not terminal and
needs neither the legacy homogeneous rigid frontier nor JC2.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Canonical episode outcome after the surviving rigid branch has been
completely consumed.  No surviving-wall rigid object or rigid zero-Schur
closing remains. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingRigidEliminatedOutcome
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
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | blockerZeroSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | blockerPlanarRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | blockerWSquareRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- The special fibre of a canonical surviving-wall exposure is free of the
unmarked coordinate `3` because the whole balanced subface is planar
quadratic. -/
theorem AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint.specialFiber_free_three
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    (C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
      (K := K) s W P R)
    (hspecial :
      polynomialSectionSpecialPoint C.exposure.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∀ d ∈
        (polynomialFamilySpecialFiber
          (C.exposure.toAdaptiveState hspecial).family).support,
      d (3 : Fin 4) = 0 := by
  intro d hd
  let a := W.original.aligned.toAdaptiveState s
  have hsfeq := C.exposure.toAdaptiveState_specialFiber hspecial
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

/-- **Surviving rigid closing is completely eliminated.**

The source-honest rigid closing exposure either has a genuine section
boundary, which is normalized by the already-green determinant-one shear, or
has canonical special point and hence coordinate-3-free special fibre.  The
latter is immediate certified saturated-kernel progress. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalSurvivingRigidEliminatedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalSurvivingRigidEliminatedOutcome
      RR s complexity := by
  rcases s.alignedSmithCanonicalRigidReducedDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, hclose⟩ |
    ⟨B, Z, hzeroClose⟩ |
    ⟨B, P, hrigid⟩ |
    ⟨B, P, hrigid⟩ |
    ⟨W, P, hD, R, hclosing⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact .blockerSchurClosing B hclose
  · exact .blockerZeroSchurClosing B Z hzeroClose
  · exact .blockerPlanarRigidPacket B P hrigid
  · exact .blockerWSquareRigidPacket B P hrigid

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

end

end HC4.Valuation
