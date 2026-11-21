import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import HC4.Newton.FiniteSupportCrossFacetExposure
import Mathlib.Tactic

/-!
# E1: exact support frontier for the marked-axis first-contact slice

The marked-axis first-contact fibre has already been identified exactly with
the zero-longitudinal slice of the genuine singular maximal ordinary top face:

```
d ∈ fibre.support ↔ d ∈ T.topFace.face.support ∧ d 0 = 0.
```

This file turns that identity into the finite support trichotomy needed by the
final-resolution stage.

There are exactly three possibilities.

* The top face has no exponent with longitudinal coordinate zero.  Then the
  marked-axis fibre is literally the zero polynomial.
* The top face has no exponent with positive longitudinal coordinate.  Then
  the whole top face is supported on the marked `.qs` facet, and the
  marked-axis fibre has exactly the same support as the top face.
* Both support slices are nonempty.  Then the top face itself carries the
  honest coordinate-zero `CrossFacetInitialData` already consumed by the
  mature A19 finite-support machinery.

No balance, terminal cocharacter, Hessian-rank promotion, or repair conclusion
is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Exact finite support classification of the marked-axis first-contact
slice.

The `empty` constructor records a literal polynomial equality.  The `full`
constructor records the actual `.qs` support confinement together with exact
support equality.  The `crossFacet` constructor retains the genuine
two-sided top-face carrier. -/
inductive TopKernelMarkedAxisSupportFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | empty
      (fibre_eq_zero :
        polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily = 0)
  | full
      (topFaceOnMarkedFacet :
        HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face)
      (support_eq :
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support =
            T.topFace.face.support)
  | crossFacet
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))

/-- If the top face has no zero-longitudinal support, the marked-axis
first-contact special fibre is literally zero. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_eq_zero_of_noZeroSupport
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hzero :
      ¬ (zeroCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0 := by
  apply MvPolynomial.ext
  intro d
  have hcoeff :
      MvPolynomial.coeff d
          (polynomialFamilySpecialFiber
            T.topKernelMarkedAxisFirstContactFamily) = 0 := by
    by_contra hne
    have hmem :
        d ∈ (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hs :=
      (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero d).1
        hmem
    exact hzero
      ⟨d, mem_zeroCoordinateSupport.mpr hs⟩
  simpa using hcoeff

/-- If the top face has no positive longitudinal support, every top-face
exponent lies on the marked `.qs` facet. -/
theorem topFaceOnMarkedFacet_of_noPositiveZeroCoordinateSupport
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hpos :
      ¬ (positiveCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty) :
    HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face := by
  intro d hd
  apply (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).2
  have hd0 : d (0 : Fin 4) = 0 := by
    by_contra hne
    have hdpos : 0 < d (0 : Fin 4) := Nat.pos_of_ne_zero hne
    exact hpos
      ⟨d, mem_positiveCoordinateSupport.mpr ⟨hd, hdpos⟩⟩
  simpa [HC4.Polynomial.facetOmittedCoordinate] using hd0

/-- In the fully marked-facet branch, the marked-axis fibre has exactly the
same support as the singular top face. -/
theorem topKernelMarkedAxisFirstContact_support_eq_topFace_of_noPositive
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hpos :
      ¬ (positiveCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty) :
    (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support =
      T.topFace.face.support := by
  apply Finset.ext
  intro d
  rw [T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero]
  constructor
  · rintro ⟨hd, _⟩
    exact hd
  · intro hd
    refine ⟨hd, ?_⟩
    by_contra hne
    have hdpos : 0 < d (0 : Fin 4) := Nat.pos_of_ne_zero hne
    exact hpos
      ⟨d, mem_positiveCoordinateSupport.mpr ⟨hd, hdpos⟩⟩

/-- In the genuine crossing branch, the marked-axis fibre is nonzero: the
facet endpoint of the retained top-face cross-facet carrier belongs to the
exact zero-longitudinal slice. -/
theorem TopKernelMarkedAxisSupportFrontier.crossFacet_fibre_support_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : CrossFacetInitialData T.topFace.face
      (crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) :
    (polynomialFamilySpecialFiber
      T.topKernelMarkedAxisFirstContactFamily).support.Nonempty := by
  refine ⟨D.facetExponent, ?_⟩
  apply
    (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
      D.facetExponent).2
  exact ⟨D.facet_mem, D.facet_coordinate_zero⟩

/-- **E1 marked-axis support frontier.**

The exact zero-longitudinal support identity yields a finite, provenance-honest
trichotomy: empty marked slice, complete `.qs` top-face confinement, or a
genuine coordinate-zero cross-facet carrier on the actual singular top face. -/
theorem topKernelMarkedAxisSupportFrontier_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.TopKernelMarkedAxisSupportFrontier := by
  by_cases hzero :
      (zeroCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty
  · by_cases hpos :
        (positiveCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty
    · exact ⟨.crossFacet
        (crossFacetInitialData
          (i := crossFacetOppositeCoordinate (0 : Fin 4))
          hzero hpos)⟩
    · exact ⟨.full
        (T.topFaceOnMarkedFacet_of_noPositiveZeroCoordinateSupport hpos)
        (T.topKernelMarkedAxisFirstContact_support_eq_topFace_of_noPositive hpos)⟩
  · exact ⟨.empty
      (T.topKernelMarkedAxisFirstContact_specialFiber_eq_zero_of_noZeroSupport
        hzero)⟩

/-- Canonical Type-valued E1 support frontier. -/
noncomputable def topKernelMarkedAxisSupportFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.TopKernelMarkedAxisSupportFrontier :=
  Classical.choice (T.topKernelMarkedAxisSupportFrontier_nonempty)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
