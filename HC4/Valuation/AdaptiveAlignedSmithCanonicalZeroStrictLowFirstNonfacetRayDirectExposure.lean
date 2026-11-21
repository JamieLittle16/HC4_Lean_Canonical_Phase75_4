import HC4.Newton.FiniteSupportExposedFaceRefinement
import HC4.Newton.FiniteSupportCrossFacetRay
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import Mathlib.Tactic

/-!
# A19.103: collapse the balance-free ray to one direct source exposure

`CrossFacetRayData` is constructed by three successive exact cross-facet
initial forms.  For the final reverse-Rees step we do not want to remember a
nested tower of faces: we want one source weight whose exact maximal face is
the same final ray.

Finite-support exposed-face refinement already gives the required
lexicographic collapse.  This file applies it to the actual A19 first-nonfacet
carrier.  The result is still completely state-free on the algebraic side: no
balance equation, homogeneity, planar terminal, or progress assertion is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

-- CI anchor: compile the direct A19.103 ray exposure.

/-- Finsupp weight is linear in a linear combination of two coordinate
weights.  We record the `Fin 4` form used by the collapsed ray exposure. -/
theorem fin4_finsupp_weight_linear_combination
    (M : ℤ) (w v : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => M * w i + v i) e =
      M * Finsupp.weight w e + Finsupp.weight v e := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · rw [Finsupp.weight_apply, Finsupp.sum_fintype]
      · rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
        push_cast
        ring
      · intro i
        simp
    · intro i
      simp
  · intro i
    simp

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {facet : ToricFacet}

/-- **A19.103 direct ray exposure.**  The three finite secondary exposures
used to define `C.ray` can be collapsed into one integer coordinate weight on
the original represented source.  In particular the final balance-free ray is
not merely a face of a face: it is an honest exposed face of the determinant-one
source itself. -/
theorem ray_support_directly_exposed_in_represented_source
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    ∃ W : Fin 4 → ℤ, ∃ level : ℤ,
      HC4.Newton.IsExposedFace
        (↑(polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W e) level := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let j : Fin 4 := HC4.Polynomial.facetOmittedCoordinate facet
  let w0 : Fin 4 → ℤ :=
    HC4.Newton.scaledContactWeight j C.scale C.bump
  let level0 : ℤ := ((C.scale * T.topFace.degree : ℕ) : ℤ)

  have hcontact :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight w0 e) level0 := by
    rw [C.face_eq]
    exact HC4.Newton.initialForm_support_isExposedFace
      w0 level0 F (by simpa [F, w0, level0] using C.source_weight_le)

  have hsourceNonempty : F.support.Nonempty := by
    have hfaceSet :
        C.crossFacet.facetExponent ∈
          (↑C.face.support : Set (Fin 4 →₀ ℕ)) := by
      simpa using C.crossFacet.facet_mem
    have hsrcSet := hcontact.subset hfaceSet
    exact ⟨C.crossFacet.facetExponent, by simpa using hsrcSet⟩

  have hfacet0 := C.zero_and_positive_support_nonempty.1
  have hout0 := C.zero_and_positive_support_nonempty.2
  let D0 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux0 j) (j := j) hfacet0 hout0
  have hfacet1 :
      (HC4.Newton.zeroCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.facetExponent,
      HC4.Newton.mem_zeroCoordinateSupport.mpr
        ⟨D0.facet_mem_face, D0.facet_coordinate_zero⟩⟩
  have hout1 :
      (HC4.Newton.positiveCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D0.outside_mem_face, D0.outside_coordinate_pos⟩⟩
  let D1 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux1 j) (j := j) hfacet1 hout1
  have hfacet2 :
      (HC4.Newton.zeroCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.facetExponent,
      HC4.Newton.mem_zeroCoordinateSupport.mpr
        ⟨D1.facet_mem_face, D1.facet_coordinate_zero⟩⟩
  have hout2 :
      (HC4.Newton.positiveCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D1.outside_mem_face, D1.outside_coordinate_pos⟩⟩
  let D2 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux2 j) (j := j) hfacet2 hout2

  have hrayFace : C.ray.face = D2.face := by
    rfl

  let v0 : Fin 4 → ℤ :=
    HC4.Newton.crossFacetWeight
      (HC4.Newton.crossFacetRayAux0 j) j D0.scale D0.bump
  let v1 : Fin 4 → ℤ :=
    HC4.Newton.crossFacetWeight
      (HC4.Newton.crossFacetRayAux1 j) j D1.scale D1.bump
  let v2 : Fin 4 → ℤ :=
    HC4.Newton.crossFacetWeight
      (HC4.Newton.crossFacetRayAux2 j) j D2.scale D2.bump

  have hD0 :
      HC4.Newton.IsExposedFace
        (↑C.face.support : Set (Fin 4 →₀ ℕ))
        (↑D0.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight v0 e) D0.level := by
    simpa [v0] using D0.support_isExposedFace
  rcases HC4.Newton.exists_nat_refine_exposed_face
      F.support hsourceNonempty hcontact hD0 with
    ⟨M0, hM0, hE0raw⟩
  let W1 : Fin 4 → ℤ := fun i => (M0 : ℤ) * w0 i + v0 i
  let L1 : ℤ := (M0 : ℤ) * level0 + D0.level
  have hE0 :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑D0.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W1 e) L1 := by
    simpa only [W1, L1, fin4_finsupp_weight_linear_combination] using hE0raw

  have hD1 :
      HC4.Newton.IsExposedFace
        (↑D0.face.support : Set (Fin 4 →₀ ℕ))
        (↑D1.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight v1 e) D1.level := by
    simpa [v1] using D1.support_isExposedFace
  rcases HC4.Newton.exists_nat_refine_exposed_face
      F.support hsourceNonempty hE0 hD1 with
    ⟨M1, hM1, hE1raw⟩
  let W2 : Fin 4 → ℤ := fun i => (M1 : ℤ) * W1 i + v1 i
  let L2 : ℤ := (M1 : ℤ) * L1 + D1.level
  have hE1 :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑D1.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W2 e) L2 := by
    simpa only [W2, L2, fin4_finsupp_weight_linear_combination] using hE1raw

  have hD2 :
      HC4.Newton.IsExposedFace
        (↑D1.face.support : Set (Fin 4 →₀ ℕ))
        (↑D2.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight v2 e) D2.level := by
    simpa [v2] using D2.support_isExposedFace
  rcases HC4.Newton.exists_nat_refine_exposed_face
      F.support hsourceNonempty hE1 hD2 with
    ⟨M2, hM2, hE2raw⟩
  let W3 : Fin 4 → ℤ := fun i => (M2 : ℤ) * W2 i + v2 i
  let L3 : ℤ := (M2 : ℤ) * L2 + D2.level
  have hE2 :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑D2.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W3 e) L3 := by
    simpa only [W3, L3, fin4_finsupp_weight_linear_combination] using hE2raw

  refine ⟨W3, L3, ?_⟩
  simpa [F, hrayFace] using hE2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
