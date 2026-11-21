import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectInitialForm
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceClosure
import HC4.Polynomial.UniqueMaximalInitialMonomial
import Mathlib.Tactic

/-!
# Lower first-contact ray facet endpoint: rank two or pure axis

The remaining exposed-`qs` frontier retains one awkward branch in which the
final balance-free lower ray starts at a codimension-two endpoint.  The ray
itself is already an exact integer-weight initial form of the represented
source.  Inside that ray, however, the stored facet endpoint is the unique
supported exponent with omitted coordinate `0`: affine proportionality and
the positive outside coordinate force every other zero-coordinate point to
coincide with it.

Thus the endpoint can be exposed once more by the elementary weight `-e₀`.
If two transverse coordinates are positive, the resulting monomial has a
nonzero Hessian principal minor; two applications of weighted-initial minor
transport lift that minor to the represented determinant-one source.  The only
remaining endpoint shape is therefore a pure power in one transverse
coordinate.

This is a source-honest reduction.  It does not identify any auxiliary clock,
use repair-only progress, or invoke generic JC2.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Integer weight exposing the zero-`qs` endpoint of a lower affine ray. -/
def qsRayFacetEndpointWeight (i : Fin 4) : ℤ :=
  if i = (0 : Fin 4) then -1 else 0

@[simp] theorem qsRayFacetEndpointWeight_zero :
    qsRayFacetEndpointWeight (0 : Fin 4) = -1 := by
  simp [qsRayFacetEndpointWeight]

@[simp] theorem qsRayFacetEndpointWeight_one :
    qsRayFacetEndpointWeight (1 : Fin 4) = 0 := by
  simp [qsRayFacetEndpointWeight]

@[simp] theorem qsRayFacetEndpointWeight_two :
    qsRayFacetEndpointWeight (2 : Fin 4) = 0 := by
  simp [qsRayFacetEndpointWeight]

@[simp] theorem qsRayFacetEndpointWeight_three :
    qsRayFacetEndpointWeight (3 : Fin 4) = 0 := by
  simp [qsRayFacetEndpointWeight]

/-- The endpoint weight is just minus the omitted-coordinate exponent. -/
theorem qsRayFacetEndpointWeight_finsupp (d : Fin 4 →₀ ℕ) :
    Finsupp.weight qsRayFacetEndpointWeight d = -(d (0 : Fin 4) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [qsRayFacetEndpointWeight]
  · intro i
    simp

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- On the final lower `.qs` ray the stored facet endpoint is the unique point
with omitted coordinate zero. -/
theorem qs_ray_facetEndpoint_unique_zeroCoordinate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ C.ray.face.support)
    (he0 : e (0 : Fin 4) = 0) :
    e = C.ray.facetExponent := by
  apply Finsupp.ext
  intro k
  have hprop := C.ray.affine_proportional e he k
  simp only [HC4.Polynomial.facetOmittedCoordinate] at hprop
  have hout0 :
      (C.ray.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.ray.outside_coordinate_pos)
  rw [he0] at hprop
  simp only [Nat.cast_zero, zero_mul] at hprop
  have hdiff :
      (e k : ℤ) - (C.ray.facetExponent k : ℤ) = 0 := by
    exact (mul_eq_zero.mp hprop).resolve_left hout0
  have hkZ : (e k : ℤ) = (C.ray.facetExponent k : ℤ) := sub_eq_zero.mp hdiff
  exact_mod_cast hkZ

/-- The zero-coordinate endpoint is a literal monomial initial form of the
final lower ray. -/
theorem qs_ray_facetEndpoint_initialForm_eq_monomial
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    HC4.Polynomial.initialForm qsRayFacetEndpointWeight 0 C.ray.face =
      MvPolynomial.monomial C.ray.facetExponent
        (MvPolynomial.coeff C.ray.facetExponent C.ray.face) := by
  apply HC4.Polynomial.initialForm_eq_monomial_of_unique_max
  · exact C.ray.facet_mem_face
  · have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
      simpa [HC4.Polynomial.facetOmittedCoordinate] using
        C.ray.facet_coordinate_zero
    rw [qsRayFacetEndpointWeight_finsupp, hfacet0]
    simp
  · intro e he
    rw [qsRayFacetEndpointWeight_finsupp]
    omega
  · intro e he hweight
    have he0 : e (0 : Fin 4) = 0 := by
      rw [qsRayFacetEndpointWeight_finsupp] at hweight
      omega
    exact C.qs_ray_facetEndpoint_unique_zeroCoordinate he he0

/-- If the lower-ray facet endpoint has two positive coordinates, its
principal Hessian minor lifts all the way to the represented source. -/
theorem qs_ray_facetEndpoint_sourceMinor_of_two_positive
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    {i j : Fin 4}
    (hij : i ≠ j)
    (hi : 0 < C.ray.facetExponent i)
    (hj : 0 < C.ray.facetExponent j) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        i j ≠ 0 := by
  have hcoeff :
      MvPolynomial.coeff C.ray.facetExponent C.ray.face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face
  have hmono :
      HC4.Polynomial.hessianPrincipalMinor
        (MvPolynomial.monomial C.ray.facetExponent
          (MvPolynomial.coeff C.ray.facetExponent C.ray.face)) i j ≠ 0 :=
    HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      hcoeff hij hi hj
  have hrayBound :
      HC4.Polynomial.IsWeightLE qsRayFacetEndpointWeight 0 C.ray.face := by
    intro e he
    rw [qsRayFacetEndpointWeight_finsupp]
    omega
  have hray :
      HC4.Polynomial.hessianPrincipalMinor C.ray.face i j ≠ 0 := by
    apply HC4.Valuation.hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      hrayBound i j
    rw [C.qs_ray_facetEndpoint_initialForm_eq_monomial]
    exact hmono
  rcases C.ray_direct_initialForm_package with
    ⟨W, level, hface, hinitial⟩
  have hsourceBound :
      HC4.Polynomial.IsWeightLE W level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
    intro e he
    exact hface.weight_le (by simpa using he)
  apply HC4.Valuation.hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    hsourceBound i j
  rw [hinitial]
  exact hray

private noncomputable def actualRankTwoChart12
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (1 : Fin 4) (2 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart13
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (1 : Fin 4) (3 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart23
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (2 : Fin 4) (3 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

/-- **Lower-ray start reduction.**  A nonlinear `.qs` facet endpoint either
already gives an actual rank-two Hessian chart on the represented state or is
a pure power in one of the three transverse coordinates. -/
theorem qs_ray_facetEndpoint_actualRankTwo_or_pureAxis
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      ((1 < C.ray.facetExponent 1 ∧
          C.ray.facetExponent 0 = 0 ∧
          C.ray.facetExponent 2 = 0 ∧ C.ray.facetExponent 3 = 0) ∨
       (1 < C.ray.facetExponent 2 ∧
          C.ray.facetExponent 0 = 0 ∧
          C.ray.facetExponent 1 = 0 ∧ C.ray.facetExponent 3 = 0) ∨
       (1 < C.ray.facetExponent 3 ∧
          C.ray.facetExponent 0 = 0 ∧
          C.ray.facetExponent 1 = 0 ∧ C.ray.facetExponent 2 = 0)) := by
  have hdeg :
      3 ≤ HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent :=
    C.ray_support_degree_ge_three C.ray.facetExponent C.ray.facet_mem_face
  have h0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    C.ray.facet_coordinate_zero
  by_cases h1 : 0 < C.ray.facetExponent (1 : Fin 4)
  · by_cases h2 : 0 < C.ray.facetExponent (2 : Fin 4)
    · have hm := C.qs_ray_facetEndpoint_sourceMinor_of_two_positive
        (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide) h1 h2
      exact Or.inl ⟨actualRankTwoChart12 hm⟩
    · have h2z : C.ray.facetExponent (2 : Fin 4) = 0 :=
        Nat.eq_zero_of_not_pos h2
      by_cases h3 : 0 < C.ray.facetExponent (3 : Fin 4)
      · have hm := C.qs_ray_facetEndpoint_sourceMinor_of_two_positive
          (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide) h1 h3
        exact Or.inl ⟨actualRankTwoChart13 hm⟩
      · have h3z : C.ray.facetExponent (3 : Fin 4) = 0 :=
          Nat.eq_zero_of_not_pos h3
        have h1gt : 1 < C.ray.facetExponent (1 : Fin 4) := by
          simp [HC4.Polynomial.ordinaryDegree4, h0, h2z, h3z] at hdeg
          omega
        exact Or.inr (Or.inl ⟨h1gt, h0, h2z, h3z⟩)
  · have h1z : C.ray.facetExponent (1 : Fin 4) = 0 :=
      Nat.eq_zero_of_not_pos h1
    by_cases h2 : 0 < C.ray.facetExponent (2 : Fin 4)
    · by_cases h3 : 0 < C.ray.facetExponent (3 : Fin 4)
      · have hm := C.qs_ray_facetEndpoint_sourceMinor_of_two_positive
          (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide) h2 h3
        exact Or.inl ⟨actualRankTwoChart23 hm⟩
      · have h3z : C.ray.facetExponent (3 : Fin 4) = 0 :=
          Nat.eq_zero_of_not_pos h3
        have h2gt : 1 < C.ray.facetExponent (2 : Fin 4) := by
          simp [HC4.Polynomial.ordinaryDegree4, h0, h1z, h3z] at hdeg
          omega
        exact Or.inr (Or.inr (Or.inl ⟨h2gt, h0, h1z, h3z⟩))
    · have h2z : C.ray.facetExponent (2 : Fin 4) = 0 :=
        Nat.eq_zero_of_not_pos h2
      have h3gt : 1 < C.ray.facetExponent (3 : Fin 4) := by
        simp [HC4.Polynomial.ordinaryDegree4, h0, h1z, h2z] at hdeg
        omega
      exact Or.inr (Or.inr (Or.inr ⟨h3gt, h0, h1z, h2z⟩))

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
