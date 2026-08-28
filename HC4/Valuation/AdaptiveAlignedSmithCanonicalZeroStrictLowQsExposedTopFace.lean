import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit
import HC4.Newton.FiniteSupportExposedVertex
import Mathlib.Tactic

/-!
# A19.78: the canonical exposed `qs` vertex confines the maximal top face

The balance-free singular boundary vertex used in A19.55 is not an arbitrary
boundary point.  Its construction successively maximizes coordinates
`0,1,2,3`, beginning with coordinate `0`.  Consequently its coordinate `0` is
the maximum coordinate `0` occurring anywhere in the singular maximal top
face.

If that exposed vertex is rank three on `.qs`, its coordinate `0` is zero.
The maximum is therefore zero, so the entire maximal top face is supported on
`.qs`.  In particular the direct top-face cross-facet branch of A19.66 is
impossible.  Combining this with the already-proved exclusion of complete
nonlinear source confinement to `.qs` leaves only the genuine lower
first-contact carrier or the literal omitted-coordinate quadratic square.

No balance relation or new termination measure is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The canonical exposed singular vertex has source-coordinate `0` maximal
among all monomials of the retained top face. -/
theorem exposedBoundary_zeroCoordinate_maximal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∀ d ∈ T.topFace.face.support,
      d (0 : Fin 4) ≤ T.exposedSingularBoundaryVertex.exponent (0 : Fin 4) := by
  intro d hd
  let D0 := HC4.Newton.coordinateMaxInitialData
    T.topFace.face T.topFace.face_ne_zero (0 : Fin 4)
  let D1 := HC4.Newton.coordinateMaxInitialData
    D0.face D0.face_ne_zero (1 : Fin 4)
  let D2 := HC4.Newton.coordinateMaxInitialData
    D1.face D1.face_ne_zero (2 : Fin 4)
  let D3 := HC4.Newton.coordinateMaxInitialData
    D2.face D2.face_ne_zero (3 : Fin 4)
  have hd2 : D3.witness ∈ D2.face.support := D3.witness_mem
  have hd1 : D3.witness ∈ D1.face.support := D2.support_subset hd2
  have hd0 : D3.witness ∈ D0.face.support := D1.support_subset hd1
  have hcoord : D3.witness (0 : Fin 4) = D0.level :=
    D0.coordinate_eq D3.witness hd0
  have hmax : d (0 : Fin 4) ≤ D0.level := D0.maximal d hd
  have hexp :
      T.exposedSingularBoundaryVertex.exponent = D3.witness := by
    rfl
  rw [hexp, hcoord]
  exact hmax

/-- If the canonical exposed vertex is rank three on `.qs`, the whole maximal
ordinary top face is already confined to `.qs`. -/
theorem qs_exposed_topFaceOnFacet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face := by
  intro d hd
  apply (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).2
  have hmax := T.exposedBoundary_zeroCoordinate_maximal d hd
  have hexp0 : T.exposedSingularBoundaryVertex.exponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hmax0 : d (0 : Fin 4) ≤ 0 := by
    simpa [hexp0] using hmax
  have hd0 : d (0 : Fin 4) = 0 := Nat.le_zero.mp hmax0
  simpa [HC4.Polynomial.facetOmittedCoordinate] using hd0

/-- Hence the direct top-face cross-facet alternative at `.qs` is impossible. -/
theorem qs_exposed_topFaceCrossFacet_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent)
    (D : HC4.Newton.CrossFacetInitialData T.topFace.face
      (HC4.Newton.crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) : False := by
  have htop := T.qs_exposed_topFaceOnFacet hthree
  have hon := htop D.outsideExponent D.outside_mem
  have hz : D.outsideExponent (0 : Fin 4) = 0 := by
    have := (HC4.Polynomial.onFacet_toToricExponent_iff .qs
      D.outsideExponent).1 hon
    simpa [HC4.Polynomial.facetOmittedCoordinate] using this
  omega

/-- **A19.78 `qs` exposed-rank-three reduction.**  Once the direct maximal
face crossing and impossible `.qs` source confinement are removed, only the
actual lower first-contact carrier or a literal quadratic square remains. -/
theorem qs_rankThree_firstNonfacetCrossFacet_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T .qs) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
        d (HC4.Polynomial.facetOmittedCoordinate .qs) = 2 ∧
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate .qs → d i = 0) := by
  rcases T.rankThree_crossFacet_or_firstNonfacetCrossFacet_or_quadraticSquare_or_nonlinearConfined
      .qs hthree with htop | hlower | hsquare | hconfined
  · rcases htop with ⟨D⟩
    exact (T.qs_exposed_topFaceCrossFacet_impossible hthree D).elim
  · exact Or.inl hlower
  · exact Or.inr hsquare
  · exact (T.nonlinearConfined_facet_ne_qs .qs hconfined rfl).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
