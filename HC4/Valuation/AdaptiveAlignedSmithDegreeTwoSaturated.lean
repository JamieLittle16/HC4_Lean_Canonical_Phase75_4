import HC4.Valuation.AdaptiveAlignedSmithExposureGeometry
import HC4.Valuation.AdaptiveAlignedSmithSurvivingPacket
import Mathlib.Tactic

/-!
# Degree-two aligned-Smith branch to saturated kernel restart

At this point the surviving aligned-Smith branch carries two compatible
pieces of data:

* an actual coefficientwise Smith exposure whose special fibre is exactly
  the retained balanced Smith subface; and
* a persistent packet endpoint certifying that this same balanced subface
  consists only of the three quadratic Smith patterns.

The existing theorem

`AdaptiveGeometricRestartState.degreeTwoSaturatedKernelStage_of_quadraticSmithSubface`

consumes exactly this geometry.

The only honest alternatives that must be retained are:

* the pre-exposure determinant defect is already zero;
* the exposed right marked point develops a transverse nonzero coordinate;
* otherwise the exposed family re-enters as an ordinary adaptive state and
  immediately performs the already-proved saturated degree-two first-contact
  restart.

No quotient-clock decrease is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A genuine section-boundary endpoint encountered while trying to expose
the quadratic balanced Smith face. -/
structure AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) where
  exposure :
    AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall
  boundary :
    Nonempty (AdaptiveSmithExposureSectionBoundary exposure)

/-- A canonical-point degree-two exposure together with the already-proved
saturated first-contact stage on that exact exposed family. -/
structure AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) where
  exposure :
    AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall
  canonicalSpecial :
    polynomialSectionSpecialPoint exposure.rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  stage :
    let a₂ := exposure.toAdaptiveState canonicalSpecial
    let hactive :=
      exists_kernelDependentSupport_of_hessianDefect
        (K := K) (3 : Fin 4) a₂.family a₂.defect a₂.hessianDefect
    let R :=
      kernelSlopeDenominatorClearingRamification
        (3 : Fin 4) a₂.family
    let q :=
      saturatedKernelSlope (3 : Fin 4) a₂.family hactive
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = R * a₂.defect - 2 * q ∧
      t.scale = R ∧
      0 < q ∧
      (∃ d ∈ (polynomialFamilySpecialFiber t.family).support,
        0 < d (3 : Fin 4))

/-- **Complete local degree-two branch.**

For a persistent packet of degree `2`, the aligned surviving-wall branch
has exactly three honest possibilities:

1. the retained determinant defect is already zero;
2. coefficientwise Smith exposure creates a genuine transverse section
   boundary;
3. the exposed marked point remains `e₀`, and the existing saturated-kernel
   theorem produces an `x₃`-active scale-aware first-contact state.

The quadratic-face input is not reconstructed: it is the exact balanced
subface retained by `W`, with the exact `P.quadratic` certificate already
produced by the packet refinement.
-/
theorem AdaptiveAlignedSmithPersistentPacketEndpoint.degreeTwo_zeroDefect_or_boundary_or_saturated
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (hD : P.degree = 2) :
    (W.original.aligned.toAdaptiveState s).defect = 0 ∨
      Nonempty
        (AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint
          (K := K) s W) ∨
      Nonempty
        (AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint
          (K := K) s W) := by
  let a := W.original.aligned.toAdaptiveState s

  rcases W.zeroDefect_or_exposure s with hzero | hexposure
  · exact Or.inl hzero
  · right
    rcases hexposure with ⟨E⟩
    rcases E.canonicalSpecial_or_boundary with hcanonical | hboundary
    · right

      let a₂ := E.toAdaptiveState hcanonical
      let T := W.balancedSubface s
      let F := a.normalizedSpecialFiber

      have hspecial :
          polynomialFamilySpecialFiber a₂.family =
            smithSubfacePolynomial (1 : Fin 4) 2 3 T F := by
        simpa [a₂, T, F, a,
          AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface] using
          E.toAdaptiveState_specialFiber hcanonical

      have hquad :
          ∀ e ∈ T,
            (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
            (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
            (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
        intro e he
        exact P.quadratic e (by simpa [T] using he)

      have hstage :=
        a₂.degreeTwoSaturatedKernelStage_of_quadraticSmithSubface
          T F hspecial hquad

      exact
        ⟨{
          exposure := E
          canonicalSpecial := hcanonical
          stage := by
            simpa [a₂] using hstage
        }⟩

    · left
      exact
        ⟨{
          exposure := E
          boundary := hboundary
        }⟩

end

end HC4.Valuation
