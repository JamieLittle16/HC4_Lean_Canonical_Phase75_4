import HC4.Valuation.AdaptiveAlignedSmithNoWallUnramifiedDefectDrop
import Mathlib.Tactic

/-!
# A18.4.59: retain the origin of the one-shot aligned endpoint

The coarse aligned classifier remembered only

    endpoint.defect ≤ 20 * source.rawDefect.

That inequality obscures a much sharper dichotomy already present in the
construction.

* A genuine coefficient wall has endpoint clock exactly `20 * Delta`.
* A genuine right-section wall is an actual boundary.
* With no genuine wall, let `m` be the least parameter order on zero Smith
  grade.  If `m = 0`, the primitive endpoint again has exact clock
  `20 * Delta`.  If `m > 0`, A18.4.58 supplies the lower-scale same-scale
  restart with defect `Delta - 4*m`.

This file reruns only the finite endpoint construction while retaining that
origin.  It removes the anonymous strict aligned-clock inequality from the
mathematics before the canonical wall classifier is invoked.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact-clock aligned endpoint, before blocker/surviving wall
classification. -/
structure AdaptiveAlignedSmithCanonicalExactAlignedEndpoint
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  endpoint : AdaptiveAlignedSmithMinimalZeroJetEndpoint
    (K := K) source.degreeCap
  defect_eq :
    endpoint.endpoint.defect =
      alignedSmithRamificationIndex * source.rawDefect

/-- Provenance-sharp result of the one-shot aligned Smith construction. -/
inductive AdaptiveAlignedSmithCanonicalAlignedEndpointOriginOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1)
  | exactEndpoint
      (E : AdaptiveAlignedSmithCanonicalExactAlignedEndpoint source)
  | noWallDefectDrop
      (D : AdaptiveAlignedSmithCanonicalNoWallDefectDrop RR source)
  | sectionBoundary
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)

/-- **A18.4.59 provenance-sharp aligned endpoint.** -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalEndpointOrigin
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalAlignedEndpointOriginOutcome RR source := by
  let P := zeroJetNormalizedFamily source.family
  let b := source.movingSection
  let Delta := source.rawDefect
  have hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta := by
    simpa [P, Delta] using source.normalized_hessianDefect
  have hdegree : NonlinearDegreeBound source.degreeCap P := by
    simpa [P] using source.normalized_nonlinearDegreeBound
  have hzero : HasZeroSourceJet P := by
    simpa [P] using zeroJetNormalizedFamily_hasZeroSourceJet source.family
  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b := by
    simpa [P, b] using source.normalized_exactCollision
  have hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    simpa [b] using source.sectionSpecial

  by_cases hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b
  · let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    by_cases hB : N ∈ alignedSmithSectionWalls b
    · have hcoord :=
        genuineRightSectionWall_exposes_nonzero_specialCoordinate
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hB)
      have hboundary :
          HasAlignedSmithSectionBoundary
            P (zeroPolynomialSection (K := K)) b hwall := by
        right
        rcases hcoord with ⟨i, hi0, hne⟩
        exact ⟨i, hi0, by simpa [N] using hB, hne⟩
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound source.degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) source.degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K) P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      exact .sectionBoundary {
        hwall := hwall
        boundary := hboundary
        hessianDefect := hwallDef
        nonlinearDegreeBound := hwallDegree
        exactCollision := hwallColl
      }

    · have hcases :=
        alignedSmithGenuineFirstWall_cases
          P (zeroPolynomialSection (K := K)) b hwall
      have hcoeff : N ∈ alignedSmithCoefficientWalls P := by
        rcases hcases with hcoeff | hA | hBright
        · simpa [N] using hcoeff
        · have hnotA :
              N ∉ alignedSmithSectionWalls
                (zeroPolynomialSection (K := K)) :=
            not_mem_alignedSmithSectionWalls_zeroPolynomialSection
              (K := K) N
          exact False.elim (hnotA (by simpa [N] using hA))
        · exact False.elim (hB (by simpa [N] using hBright))
      have hnotA :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls
              (zeroPolynomialSection (K := K)) :=
        not_mem_alignedSmithSectionWalls_zeroPolynomialSection
          (K := K)
          (alignedSmithGenuineFirstWall
            P (zeroPolynomialSection (K := K)) b hwall)
      have hnotB :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls b := by
        simpa [N] using hB
      have ha :
          polynomialSectionSpecialPoint
              (zeroPolynomialSection (K := K)) =
            (fun _ => (0 : K)) :=
        polynomialSectionSpecialPoint_zeroPolynomialSection
      have hpoints :=
        pureCoefficientWall_specialPoints_canonical
          P (zeroPolynomialSection (K := K)) b hwall
          hnotA hnotB ha hb
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound source.degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) source.degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K) P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      have hminimal :
          IsSymmetricSmithPoleMinimal
            (smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber
                (alignedSmithGenuineFirstWallFamily
                  P (zeroPolynomialSection (K := K)) b hwall)))
            0 (fun _ => (0 : ℤ)) :=
        genuineCoefficientWall_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hcoeff)
      let endpoint : AdaptiveAlignedSmithMinimalEndpoint
          (K := K) source.degreeCap := {
        defect := alignedSmithRamificationIndex * Delta
        family := alignedSmithGenuineFirstWallFamily
          P (zeroPolynomialSection (K := K)) b hwall
        movingSection := alignedSmithGenuineFirstWallSectionRight
          P (zeroPolynomialSection (K := K)) b hwall
        hessianDefect := hwallDef
        nonlinearDegreeBound := hwallDegree
        exactCollision := hwallColl
        sectionSpecial := hpoints.2
        symmetricMinimal := hminimal
      }
      have hEzero : HasZeroSourceJet endpoint.family := by
        dsimp [endpoint]
        exact hzero.alignedSmithGenuineFirstWallFamily
          (zeroPolynomialSection (K := K)) b hwall
      let E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
          (K := K) source.degreeCap := {
        endpoint := endpoint
        zeroSourceJet := hEzero
      }
      exact .exactEndpoint {
        endpoint := E
        defect_eq := by rfl
      }

  · let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b Delta hdef hwall
    let m := minimalZeroSmithParameterOrder P hne
    by_cases hm0 : m = 0
    · rcases
        noWallPrimitiveSmithFamily_zeroLeft_canonicalCollision
          P b Delta hdef hwall hcoll hb with
        ⟨b', hcoll', hb'⟩
      let Q :=
        noWallPrimitiveSmithFamily
          P (zeroPolynomialSection (K := K)) b Delta hdef hwall
      let Delta' :=
        alignedSmithRamificationIndex * Delta -
          4 * (alignedSmithRamificationIndex * m)
      have hQdef : HasPolynomialFamilyHessianDefect (K := K) Q Delta' := by
        dsimp [Q, Delta', hne, m]
        exact noWallPrimitiveSmithFamily_hasHessianDefect
          P (zeroPolynomialSection (K := K)) b Delta hdef hwall
      have hQdegree : NonlinearDegreeBound source.degreeCap Q := by
        dsimp [Q]
        exact nonlinearDegreeBound_noWallPrimitiveSmithFamily
          (K := K) source.degreeCap P
          (zeroPolynomialSection (K := K)) b Delta hdef hwall hdegree
      have hminimal :
          IsSymmetricSmithPoleMinimal
            (smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber Q))
            0 (fun _ => (0 : ℤ)) := by
        dsimp [Q]
        exact noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b Delta hdef hwall
      let endpoint : AdaptiveAlignedSmithMinimalEndpoint
          (K := K) source.degreeCap := {
        defect := Delta'
        family := Q
        movingSection := b'
        hessianDefect := hQdef
        nonlinearDegreeBound := hQdegree
        exactCollision := hcoll'
        sectionSpecial := hb'
        symmetricMinimal := hminimal
      }
      have hEzero : HasZeroSourceJet endpoint.family := by
        dsimp [endpoint, Q]
        exact hzero.noWallPrimitiveSmithFamily
          (zeroPolynomialSection (K := K)) b Delta hdef hwall
      let E : AdaptiveAlignedSmithMinimalZeroJetEndpoint
          (K := K) source.degreeCap := {
        endpoint := endpoint
        zeroSourceJet := hEzero
      }
      have heq :
          E.endpoint.defect =
            alignedSmithRamificationIndex * source.rawDefect := by
        dsimp [E, endpoint, Delta']
        rw [hm0]
        simp [Delta]
      exact .exactEndpoint {
        endpoint := E
        defect_eq := heq
      }

    · have hm : 0 < m := Nat.pos_of_ne_zero hm0
      have hm' :
          0 < (AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData.ofNoWall
            source.degreeCap source.rawDefect
            (zeroJetNormalizedFamily source.family) source.movingSection
            hwall source.normalized_hessianDefect
            source.normalized_nonlinearDegreeBound
            source.normalized_exactCollision source.sectionSpecial).m := by
        simpa [P, b, Delta, hne, m,
          AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData.ofNoWall] using hm
      exact .noWallDefectDrop
        (source.noWallDefectDrop RR hwall hm')

end

end HC4.Valuation
