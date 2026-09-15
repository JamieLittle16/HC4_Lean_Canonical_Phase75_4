import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectExposure
import HC4.Newton.FiniteSupportExposedFaceRefinement
import Mathlib.Tactic

/-!
# A19.104a: the directly exposed balance-free ray is an exact source initial form

A19.103 collapses the three finite secondary ray exposures to one integer
weight on the represented determinant-one source, but states the result at the
support level.  Exact initial forms retain their source coefficients, so the
same weight actually reconstructs the literal ray polynomial.

This file performs only that coefficient bookkeeping.  No positivity,
ramification, Rees family, balance relation, or terminal contradiction is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

-- CI anchor: compile A19.104a together with the positive refinement layer.

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {facet : ToricFacet}

/-- Every coefficient retained by the final balance-free ray is literally the
coefficient of the represented source at the same exponent.  This follows by
chaining coefficient preservation through the three deterministic
cross-facet initial forms and then through the original contact initial form. -/
theorem ray_coeff_eq_represented_source_of_mem
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ C.ray.face.support) :
    MvPolynomial.coeff e C.ray.face =
      MvPolynomial.coeff e
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) := by
  let j : Fin 4 := HC4.Polynomial.facetOmittedCoordinate facet
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
  have he2 : e ∈ D2.face.support := by
    rw [← hrayFace]
    exact he
  have he1 : e ∈ D1.face.support := D2.support_subset he2
  have he0 : e ∈ D0.face.support := D1.support_subset he1
  have heC : e ∈ C.face.support := D0.support_subset he0

  have h2 : MvPolynomial.coeff e D2.face = MvPolynomial.coeff e D1.face :=
    D2.coeff_face_eq_source_of_mem he2
  have h1 : MvPolynomial.coeff e D1.face = MvPolynomial.coeff e D0.face :=
    D1.coeff_face_eq_source_of_mem he1
  have h0 : MvPolynomial.coeff e D0.face = MvPolynomial.coeff e C.face :=
    D0.coeff_face_eq_source_of_mem he0
  have hcontact :
      MvPolynomial.coeff e C.face =
        MvPolynomial.coeff e
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) := by
    rw [C.face_eq] at heC ⊢
    exact HC4.Newton.initialForm_coeff_eq_source_of_mem
      (HC4.Newton.scaledContactWeight
        (HC4.Polynomial.facetOmittedCoordinate facet) C.scale C.bump)
      ((C.scale * T.topFace.degree : ℕ) : ℤ)
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      heC

  calc
    MvPolynomial.coeff e C.ray.face = MvPolynomial.coeff e D2.face := by
      rw [hrayFace]
    _ = MvPolynomial.coeff e D1.face := h2
    _ = MvPolynomial.coeff e D0.face := h1
    _ = MvPolynomial.coeff e C.face := h0
    _ = MvPolynomial.coeff e
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) := hcontact

/-- **A19.104a exact direct-ray package.**  The same integer weight supplied by
A19.103 exposes the final ray and its exact initial form is literally
`C.ray.face`. -/
theorem ray_direct_initialForm_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    ∃ W : Fin 4 → ℤ, ∃ level : ℤ,
      HC4.Newton.IsExposedFace
        (↑(polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W e) level ∧
      HC4.Polynomial.initialForm W level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) = C.ray.face := by
  rcases C.ray_support_directly_exposed_in_represented_source with
    ⟨W, level, hface⟩
  refine ⟨W, level, hface, ?_⟩
  exact HC4.Newton.initialForm_eq_of_exposedSupport_and_coeff
    W level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    C.ray.face hface
    (fun d hd => C.ray_coeff_eq_represented_source_of_mem hd)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
