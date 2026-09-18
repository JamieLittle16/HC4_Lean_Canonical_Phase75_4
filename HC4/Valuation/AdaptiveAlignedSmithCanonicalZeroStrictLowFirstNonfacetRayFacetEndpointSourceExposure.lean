import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointRankTwo
import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import Mathlib.Tactic

/-!
# Positive direct source exposure of the lower-ray facet endpoint

The lower first-contact ray is already an exact exposed face of the represented
source, but its direct exposing weight is signed.  For reverse-Rees covariance
we need a positive source weight and a positive four-dimensional Hessian clock.

The represented zero-defect source has a genuine maximal ordinary top face of
degree at least three.  That top-face exposure has strictly positive coordinate
weight `(1,1,1,1)`, positive level, and positive Hessian clock `4D-8`.
Inside the top face, the direct ray weight exposes exactly the stored ray facet
endpoint: any top-degree ray point has contact coordinate zero, and the affine
ray has a unique zero-coordinate point.

Finite lexicographic refinement therefore collapses the two exposures to one
direct positive source exposure of that endpoint, preserving a positive
Hessian clock.  No auxiliary clock is identified with the zero blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Honest positive source exposure of the stored lower `.qs` ray facet
endpoint. -/
structure QsRayFacetEndpointSourceExposure
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  weight : Fin 4 → ℤ
  level : ℤ
  exposed :
    HC4.Newton.IsExposedFace
      (↑(polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
      ({C.ray.facetExponent} : Set (Fin 4 →₀ ℕ))
      (fun e => Finsupp.weight weight e) level
  weight_pos : ∀ i : Fin 4, 0 < weight i
  level_pos : 0 < level
  hessianClock_pos :
    0 < 4 * level - 2 * ∑ i : Fin 4, weight i
  initialForm_eq :
    HC4.Polynomial.initialForm weight level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) =
      MvPolynomial.monomial C.ray.facetExponent
        (MvPolynomial.coeff C.ray.facetExponent
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))

namespace QsRayFacetEndpointSourceExposure

/-- Global source weight bound exported by the direct exposed-face package. -/
theorem source_bound
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (E : QsRayFacetEndpointSourceExposure C) :
    HC4.Polynomial.IsWeightLE E.weight E.level
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro e he
  exact E.exposed.weight_le (by simpa using he)

end QsRayFacetEndpointSourceExposure

/-- A lower ray facet endpoint lies on the represented maximal ordinary top
face: its contact coordinate is zero, so the exact first-contact equation
forces ordinary degree equal to the top degree. -/
theorem qs_ray_facetEndpoint_degree_eq_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent = T.topFace.degree := by
  have hcontact :=
    C.ray_contact_eq C.ray.facetExponent C.ray.facet_mem_face
  have hcontact' :
      HC4.Newton.scaledContactExponentWeight
          (0 : Fin 4) C.scale C.bump C.ray.facetExponent =
        ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hcontact
  unfold HC4.Newton.scaledContactExponentWeight at hcontact'
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  rw [hfacet0] at hcontact'
  simp only [Nat.cast_zero, mul_zero, add_zero] at hcontact'
  have hscale : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  push_cast at hcontact'
  nlinarith

/-- The endpoint is literal support of the maximal ordinary top face. -/
theorem qs_ray_facetEndpoint_mem_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    C.ray.facetExponent ∈ T.topFace.face.support := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  rcases C.ray_direct_initialForm_package with
    ⟨W, level, hRay, _hinit⟩
  have hdF : C.ray.facetExponent ∈ F.support := by
    have hset := hRay.subset (show C.ray.facetExponent ∈
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) by
        simpa using C.ray.facet_mem_face)
    simpa [F] using hset
  rw [T.topFace.face_eq]
  apply MvPolynomial.mem_support_iff.mpr
  rw [HC4.Polynomial.coeff_initialForm]
  have hw :
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) C.ray.facetExponent =
        (T.topFace.degree : ℤ) := by
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast C.qs_ray_facetEndpoint_degree_eq_topFace
  split_ifs with hweight
  · exact MvPolynomial.mem_support_iff.mp (by simpa [F] using hdF)
  · exfalso
    apply hweight
    change
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) C.ray.facetExponent =
        (T.topFace.degree : ℤ)
    exact hw

/-- **Positive direct endpoint exposure.**  The maximal ordinary top-face
weight is used as the positive primary exposure and the exact direct-ray weight
as the secondary exposure. -/
theorem exists_qs_ray_facetEndpoint_sourceExposure
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    Nonempty (QsRayFacetEndpointSourceExposure C) := by
  classical
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let D : ℕ := T.topFace.degree
  let wTop : Fin 4 → ℤ := fun _ => 1

  rcases C.ray_direct_initialForm_package with
    ⟨W, rayLevel, hRay, _hRayInitial⟩

  have hTopBound : HC4.Polynomial.IsWeightLE wTop (D : ℤ) F := by
    intro e he
    change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) e ≤ (D : ℤ)
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast T.topFace.maximal e (by simpa [F] using he)

  have hTopFaceEq :
      T.topFace.face =
        HC4.Polynomial.initialForm wTop (D : ℤ) F := by
    have h := T.topFace.face_eq
    change
      T.topFace.face =
        HC4.Polynomial.initialForm
          (fun _ : Fin 4 => (1 : ℤ))
          (T.topFace.degree : ℤ)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) at h
    simpa [F, D, wTop] using h
  have hTop :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑T.topFace.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight wTop e) (D : ℤ) := by
    have h := HC4.Newton.initialForm_support_isExposedFace
      wTop (D : ℤ) F hTopBound
    rw [← hTopFaceEq] at h
    exact h

  have hEndpoint :
      HC4.Newton.IsExposedFace
        (↑T.topFace.face.support : Set (Fin 4 →₀ ℕ))
        ({C.ray.facetExponent} : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W e) rayLevel := by
    constructor
    · ext e
      constructor
      · intro he
        have hed : e = C.ray.facetExponent := by simpa using he
        subst e
        refine ⟨?_, ?_⟩
        · exact C.qs_ray_facetEndpoint_mem_topFace
        · exact hRay.weight_eq (by simpa using C.ray.facet_mem_face)
      · rintro ⟨heTop, heWeight⟩
        have heFset := hTop.subset (show e ∈
          (↑T.topFace.face.support : Set (Fin 4 →₀ ℕ)) by simpa using heTop)
        have heRaySet := hRay.mem_iff.mpr ⟨heFset, heWeight⟩
        have heRay : e ∈ C.ray.face.support := by simpa using heRaySet
        have heDeg : HC4.Polynomial.ordinaryDegree4 e = T.topFace.degree :=
          T.topFace.face_support_ordinaryDegree_eq heTop
        have hcontact := C.ray_contact_eq e heRay
        have hcontact' :
            HC4.Newton.scaledContactExponentWeight
                (0 : Fin 4) C.scale C.bump e =
              ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
          simpa [HC4.Polynomial.facetOmittedCoordinate] using hcontact
        unfold HC4.Newton.scaledContactExponentWeight at hcontact'
        rw [heDeg] at hcontact'
        push_cast at hcontact'
        have hbump : (0 : ℤ) < (C.bump : ℤ) := by
          exact_mod_cast C.bump_pos
        have he0Z : (e (0 : Fin 4) : ℤ) = 0 := by
          nlinarith
        have he0 : e (0 : Fin 4) = 0 := by exact_mod_cast he0Z
        have heq := C.qs_ray_facetEndpoint_unique_zeroCoordinate heRay he0
        simpa [heq]
    · intro e heTop
      have heFset := hTop.subset heTop
      exact hRay.weight_le heFset

  have hsourceNonempty : F.support.Nonempty := by
    exact ⟨T.topFace.witness, by simpa [F] using T.topFace.witness_mem⟩
  have hwTopPos : ∀ i : Fin 4, 0 < wTop i := by
    intro i
    simp [wTop]
  have hDpos : (0 : ℤ) < (D : ℤ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) T.topFace.degree_ge_three)
  have hclockTop :
      0 < 4 * (D : ℤ) - 2 * ∑ i : Fin 4, wTop i := by
    rw [Fin.sum_univ_four]
    simp [wTop]
    have hD3 : (3 : ℤ) ≤ (D : ℤ) := by
      exact_mod_cast T.topFace.degree_ge_three
    omega

  rcases HC4.Newton.exists_nat_refine_exposed_face_fin4_positive_clock
      F.support hsourceNonempty hTop hEndpoint
      hwTopPos hDpos hclockTop with
    ⟨M, hM, hface, hweightPos, hlevelPos, hclockPos⟩

  let finalWeight : Fin 4 → ℤ := fun i => (M : ℤ) * wTop i + W i
  let finalLevel : ℤ := (M : ℤ) * (D : ℤ) + rayLevel

  have hface' :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        ({C.ray.facetExponent} : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight finalWeight e) finalLevel := by
    simpa [finalWeight, finalLevel] using hface

  have hdF : C.ray.facetExponent ∈ F.support := by
    have hset := hface'.subset (by simp)
    simpa using hset
  have hdWeight :
      Finsupp.weight finalWeight C.ray.facetExponent = finalLevel :=
    hface'.weight_eq (by simp)
  have hbound : HC4.Polynomial.IsWeightLE finalWeight finalLevel F := by
    intro e he
    exact hface'.weight_le (by simpa using he)
  have huniq :
      ∀ e ∈ F.support,
        Finsupp.weight finalWeight e = finalLevel →
          e = C.ray.facetExponent := by
    intro e he hew
    have hmem :
        e ∈ ({C.ray.facetExponent} : Set (Fin 4 →₀ ℕ)) :=
      (HC4.Newton.IsExposedFace.mem_iff hface' (x := e)).2
        ⟨(by simpa using he), hew⟩
    exact Set.mem_singleton_iff.mp hmem
  have hinit :
      HC4.Polynomial.initialForm finalWeight finalLevel F =
        MvPolynomial.monomial C.ray.facetExponent
          (MvPolynomial.coeff C.ray.facetExponent F) := by
    exact HC4.Polynomial.initialForm_eq_monomial_of_unique_max
      finalWeight finalLevel F C.ray.facetExponent hdF hdWeight hbound huniq

  exact ⟨{
    weight := finalWeight
    level := finalLevel
    exposed := by simpa [F] using hface'
    weight_pos := by simpa [finalWeight] using hweightPos
    level_pos := by simpa [finalLevel] using hlevelPos
    hessianClock_pos := by
      simpa [finalWeight, finalLevel] using hclockPos
    initialForm_eq := by simpa [F] using hinit
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
