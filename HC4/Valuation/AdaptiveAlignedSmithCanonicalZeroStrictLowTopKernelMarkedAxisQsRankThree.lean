import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsBoundaryClosure
import Mathlib.Tactic

/-!
# E1: the marked-axis face in the exposed `.qs` rank-three branch

The marked-axis first-contact fibre is the exact `(0,1,1,1)` initial form of
the represented source, and its support is exactly the zero-longitudinal slice
of the singular maximal ordinary top face.

When the canonical exposed top-face vertex is rank three on `.qs`, A19.78
already proves that the *whole* maximal top face is supported on `.qs`.
Consequently the marked-axis slice loses nothing: it is literally the same
polynomial as the retained singular top face.  The distinct marked collision
therefore lives on that actual top face.

The square-free `.qs` boundary closure can then be attached without any new
balance assumption: the same branch has a genuine lower first-contact carrier
whose retained ray reaches the already-green lower-boundary frontier.

This is an E-stage adapter only.  It introduces no new Rees clock, repair
transition, torus balance, or terminal endpoint certificate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- In the exposed `.qs` rank-three branch, every top-face exponent has
longitudinal exponent zero. -/
theorem qs_rankThree_topFace_exponent_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ T.topFace.face.support) :
    d (0 : Fin 4) = 0 := by
  have hon := T.qs_exposed_topFaceOnFacet hthree d hd
  have htoric :=
    (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).1 hon
  simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric

/-- Hence the marked-axis first-contact fibre and the singular top face have
exactly the same finite support in the exposed `.qs` rank-three branch. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_support_eq_topFace_of_qsRankThree
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support =
      T.topFace.face.support := by
  ext d
  rw [T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero]
  constructor
  · rintro ⟨hd, _hzero⟩
    exact hd
  · intro hd
    exact ⟨hd, T.qs_rankThree_topFace_exponent_zero hthree hd⟩

/-- **Exact marked-face identification in the canonical `.qs` branch.**

Because the whole top face already has longitudinal exponent zero, the
`(0,1,1,1)` initial form retains every top-face coefficient and no others.
Thus the actual collision-bearing marked fibre is literally the singular
maximal ordinary top face, not merely a support-equivalent surrogate. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_eq_topFace_of_qsRankThree
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily =
      T.topFace.face := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ T.topFace.face.support
  · have hzero : d (0 : Fin 4) = 0 :=
      T.qs_rankThree_topFace_exponent_zero hthree hd
    have hdeg :
        HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree :=
      T.topFace.ordinaryDegree_eq_of_mem_support hd
    have htrans :
        d 1 + d 2 + d 3 = T.topFace.degree := by
      unfold HC4.Polynomial.ordinaryDegree4 at hdeg
      omega
    have hw :
        Finsupp.weight
            (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
          (T.topFace.degree : ℤ) := by
      rw [weight_topKernelMarkedAxisIntWeight]
      exact_mod_cast htrans
    rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
      HC4.Polynomial.coeff_initialForm, if_pos hw,
      T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    rfl
  · have hsupport :=
      T.topKernelMarkedAxisFirstContact_specialFiber_support_eq_topFace_of_qsRankThree
        hthree
    have hnotMarked :
        d ∉ (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support := by
      intro hmarked
      apply hd
      rw [← hsupport]
      exact hmarked
    rw [MvPolynomial.notMem_support_iff.mp hnotMarked,
      MvPolynomial.notMem_support_iff.mp hd]

/-- E1 packet for the canonical `.qs` rank-three branch.  It retains the
actual marked collision-bearing face, identifies it with the true singular
top face, and simultaneously keeps the already-green square-free lower
boundary carrier. -/
structure TopKernelMarkedAxisQsRankThreeRefinementData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  rankThree :
    MvRankThreeOnFacet .qs T.exposedSingularBoundaryVertex.exponent
  markedFace : T.TopKernelMarkedAxisFirstContactFaceData
  markedFace_eq_topFace :
    markedFace.fibre = T.topFace.face
  lowerContact :
    AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      (K := K) T .qs
  lowerBoundary : QsLowerBoundaryOutcome lowerContact

/-- Every exposed `.qs` rank-three branch has the exact E1 refinement packet
above. -/
theorem topKernelMarkedAxis_qsRankThreeRefinement
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    Nonempty T.TopKernelMarkedAxisQsRankThreeRefinementData := by
  rcases T.qs_rankThree_lowerBoundary hthree with ⟨C, hC⟩
  refine ⟨{
    rankThree := hthree
    markedFace := T.topKernelMarkedAxisFirstContactFaceData
    markedFace_eq_topFace := ?_
    lowerContact := C
    lowerBoundary := hC
  }⟩
  change
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily =
      T.topFace.face
  exact
    T.topKernelMarkedAxisFirstContact_specialFiber_eq_topFace_of_qsRankThree
      hthree

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
