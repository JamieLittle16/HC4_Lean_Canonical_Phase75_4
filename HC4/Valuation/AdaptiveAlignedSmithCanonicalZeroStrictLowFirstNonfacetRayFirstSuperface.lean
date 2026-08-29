import HC4.Newton.FiniteSupportExposedSuperface
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayHigherLongitudinalLayer
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectInitialForm
import Mathlib.Tactic

/-!
# A19.117: first strict source superface above the locked ray

The ray-leading reverse Rees weight from A19.104b and the independent direct
ray weight from A19.104a both expose exactly the same final balance-free ray in
the represented source support.  A19.109 supplies an actual represented-source
monomial with longitudinal exponent at least two, hence it is not on the
degree-one ray.

Consequently that higher-longitudinal monomial lies strictly below the second
ray exposure.  The generic finite first-superface theorem can therefore move
between the two ray normals until another source point first joins the ray.
The result is an honest strict exposed superface of the represented source.

We deliberately do not call this superface a plane and do not assert that the
selected new point is the higher-longitudinal witness.  Those are subsequent
geometric statements, not consequences of finite exposed-face selection alone.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Support-level first strict superface, retaining the concrete
higher-longitudinal source point which certifies that the ray is not the whole
source carrier. -/
structure QsOtherFacetRayFirstSuperfacePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (R : QsOtherFacetRayReverseReesPackage C) where
  secondaryWeight : Fin 4 → ℤ
  secondaryLevel : ℤ
  secondaryExposure :
    HC4.Newton.IsExposedFace
      (↑(polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
      (fun e => Finsupp.weight secondaryWeight e) secondaryLevel
  higherExponent : Fin 4 →₀ ℕ
  higher_source :
    higherExponent ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support
  higher_longitudinal_two_le : 2 ≤ higherExponent (0 : Fin 4)
  higher_not_ray : higherExponent ∉ C.ray.face.support
  higher_secondary_lt :
    Finsupp.weight secondaryWeight higherExponent < secondaryLevel
  A : ℤ
  B : ℤ
  A_pos : 0 < A
  B_pos : 0 < B
  superface : Set (Fin 4 →₀ ℕ)
  superface_exposed :
    HC4.Newton.IsExposedFace
      (↑(polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
      superface
      (fun e =>
        A * Finsupp.weight (fun i : Fin 4 => (R.weight i : ℤ)) e -
          B * Finsupp.weight secondaryWeight e)
      (A * (R.level : ℤ) - B * secondaryLevel)
  ray_subset_superface :
    (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆ superface
  strict : ∃ e, e ∈ superface ∧ e ∉ C.ray.face.support

/-- **A19.117 first strict superface.** -/
theorem QsOtherFacetRayReverseReesPackage.firstSuperfacePackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    Nonempty (QsOtherFacetRayFirstSuperfacePackage C R) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let wR : Fin 4 → ℤ := fun i => (R.weight i : ℤ)

  have hRbound : HC4.Polynomial.IsWeightLE wR (R.level : ℤ) F := by
    intro e he
    have h := R.bound e he
    rw [show Finsupp.weight wR e = (Finsupp.weight R.weight e : ℤ) by
      exact weight_natCast_eq R.weight e] 
    exact_mod_cast h
  have hRexposed :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight wR e) (R.level : ℤ) := by
    have h := HC4.Newton.initialForm_support_isExposedFace
      wR (R.level : ℤ) F hRbound
    rw [R.initialForm_eq_ray] at h
    exact h

  rcases C.ray_direct_initialForm_package with
    ⟨v, d, hvExposure, _hvExact⟩
  rcases R.higherLongitudinalLayerWitness hthree with ⟨H⟩

  have hHnot : H.exponent ∉ C.ray.face.support := by
    intro heRay
    have hidx :
        H.exponent (0 : Fin 4) ∈ C.ray.zeroCoefficientPolynomial.support :=
      C.ray.zeroCoefficientPolynomial_mem_of_face_mem heRay
    have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
      C.qs_ray_terminal_degreeOne hthree
    have hle : H.exponent (0 : Fin 4) ≤ 1 := by
      rw [← hdeg]
      exact Polynomial.le_natDegree_of_mem_supp _ hidx
    omega

  have hHsourceSet : H.exponent ∈ (↑F.support : Set (Fin 4 →₀ ℕ)) := by
    simpa [F] using H.exponent_source
  have hHvle : Finsupp.weight v H.exponent ≤ d :=
    hvExposure.weight_le hHsourceSet
  have hHvne : Finsupp.weight v H.exponent ≠ d := by
    intro heq
    apply hHnot
    have hmem := hvExposure.mem_iff.mpr ⟨hHsourceSet, heq⟩
    simpa using hmem
  have hHvlt : Finsupp.weight v H.exponent < d :=
    lt_of_le_of_ne hHvle hHvne

  have hexit :
      ∃ e ∈ F.support,
        e ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ∧
          Finsupp.weight v e < d := by
    refine ⟨H.exponent, ?_, ?_, hHvlt⟩
    · simpa [F] using H.exponent_source
    · simpa using hHnot

  rcases HC4.Newton.exists_first_exposed_superface
      F.support hRexposed
      (fun e he => hvExposure.weight_eq he)
      hexit with
    ⟨A, B, G, hA, hB, hG, hsub, hstrict⟩

  exact ⟨{
    secondaryWeight := v
    secondaryLevel := d
    secondaryExposure := by simpa [F] using hvExposure
    higherExponent := H.exponent
    higher_source := H.exponent_source
    higher_longitudinal_two_le := H.longitudinal_two_le
    higher_not_ray := hHnot
    higher_secondary_lt := hHvlt
    A := A
    B := B
    A_pos := hA
    B_pos := hB
    superface := G
    superface_exposed := by simpa [F, wR] using hG
    ray_subset_superface := hsub
    strict := hstrict
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
