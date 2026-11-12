import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3AllMinorSourceLift
import Mathlib.Tactic

/-!
# Non-principal Hessian minor transport through the canonical three-step opening chain

The canonical codimension-two singular-boundary construction starts with a
source F and takes consecutive coordinate-maximal exact initial forms
in coordinates 0, 1, and 2.  A nonzero arbitrary Hessian two-by-two
minor on *any* of these three faces therefore lifts all the way to F.

This is a source-honest transport theorem: it uses the actual
coordinate-max initial-form identities and their upper weight bounds,
not just containment of supports.

The second theorem accepts an arbitrary stored opening packet only
when its child is explicitly identified with one of the three canonical
faces.  The current `CanonicalCoordinateMaxKernelOpeningData` record
stores support containment but does not itself store that chain identity,
so obtaining this provenance from the canonical selector remains a
distinct obligation.  No unproved universal child-to-source implication
is asserted here.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero non-principal or principal Hessian two-by-two minor on any
of the three genuine coordinate-max faces of the canonical singular
boundary chain lifts to the unchanged source. -/
theorem canonicalThreeCoordinateMaxFaces_minor_source
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (i j k l : Fin 4)
    (hface :
      let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
      let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
      let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
      hessianTwoByTwoMinor D0.face i j k l ≠ 0 ∨
        hessianTwoByTwoMinor D1.face i j k l ≠ 0 ∨
        hessianTwoByTwoMinor D2.face i j k l ≠ 0) :
    hessianTwoByTwoMinor F i j k l ≠ 0 := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  change hessianTwoByTwoMinor D0.face i j k l ≠ 0 ∨
      hessianTwoByTwoMinor D1.face i j k l ≠ 0 ∨
      hessianTwoByTwoMinor D2.face i j k l ≠ 0 at hface
  have lift (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0)
      (a : Fin 4)
      (hm :
        hessianTwoByTwoMinor
          (coordinateMaxInitialData G hG a).face i j k l ≠ 0) :
      hessianTwoByTwoMinor G i j k l ≠ 0 := by
    exact e3HessianTwoByTwoMinor_ne_zero_of_initialForm_ne_zero
      (coordinateMaxInitialData G hG a).weight_bound i j k l
      (by
        simpa only [(coordinateMaxInitialData G hG a).face_eq] using hm)
  rcases hface with h0 | h1 | h2
  · exact lift F hF (0 : Fin 4) h0
  · exact lift F hF (0 : Fin 4)
      (lift D0.face D0.face_ne_zero (1 : Fin 4) h1)
  · exact lift F hF (0 : Fin 4)
      (lift D0.face D0.face_ne_zero (1 : Fin 4)
        (lift D1.face D1.face_ne_zero (2 : Fin 4) h2))

/-- If the stored child of an opening is *certified* to belong to the
canonical three-face chain, its rank-two Hessian witness lifts
to the original source.  The explicit provenance is necessary:
support containment alone cannot transport nonlinear Hessian minors. -/
theorem canonicalOpeningRankTwo_source_of_threeFaceProvenance
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (O : CanonicalCoordinateMaxKernelOpeningData F)
    (hprovenance :
      let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
      let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
      let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
      O.child = D0.face ∨ O.child = D1.face ∨ O.child = D2.face)
    (htwo : O.ChildHessianRankTwoWitness) :
    ∃ i j k l : Fin 4,
      hessianTwoByTwoMinor F i j k l ≠ 0 := by
  rcases htwo with ⟨i, j, k, l, hminor⟩
  have hchild : hessianTwoByTwoMinor O.child i k j l ≠ 0 :=
    hminor
  have hface :
      let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
      let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
      let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
      hessianTwoByTwoMinor D0.face i k j l ≠ 0 ∨
        hessianTwoByTwoMinor D1.face i k j l ≠ 0 ∨
        hessianTwoByTwoMinor D2.face i k j l ≠ 0 := by
    dsimp only at hprovenance ⊢
    rcases hprovenance with h0 | h1 | h2
    · exact Or.inl (by rw [← h0]; exact hchild)
    · exact Or.inr (Or.inl (by rw [← h1]; exact hchild))
    · exact Or.inr (Or.inr (by rw [← h2]; exact hchild))
  exact ⟨i, k, j, l,
    canonicalThreeCoordinateMaxFaces_minor_source F hF i k j l hface⟩

end
end HC4.Valuation
