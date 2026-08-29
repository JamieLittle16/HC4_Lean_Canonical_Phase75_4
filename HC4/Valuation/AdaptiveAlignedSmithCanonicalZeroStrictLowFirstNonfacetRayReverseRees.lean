import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectInitialForm
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactRees
import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# A19.104b: honest reverse Rees family with the locked ray as special fibre

A19.104a makes the final balance-free ray an exact integer-weight initial form
of the represented determinant-one source.  The signed direct weight need not
itself be suitable for reverse Rees covariance.  We therefore restrict it back
to the integral contact face and use that contact as a positive primary
exposure.  A sufficiently large lexicographic multiple keeps the same ray
while making all four final coordinate weights, the final source level, and
the four-dimensional Hessian clock positive.

Casting those positive integers to naturals gives an honest bounded reverse
Rees family.  Its special fibre is literally `C.ray.face`, its determinant is a
positive pure parameter power, and consequently it has an actual positive
parameter layer.  No lower source monomial is asserted to lie on the static
ray: later layers are retained as genuine deformations of this ray-leading
family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Exact ray-leading reverse-Rees package used by the remaining local
staircase/Schur argument. -/
structure QsOtherFacetRayReverseReesPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  weight : Fin 4 → ℕ
  level : ℕ
  weight_pos : ∀ i : Fin 4, 0 < weight i
  level_pos : 0 < level
  bound : HasReverseWeightBound weight level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  initialForm_eq_ray :
    HC4.Polynomial.initialForm (fun i => (weight i : ℤ)) (level : ℤ)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) = C.ray.face
  specialFiber_eq_ray :
    polynomialFamilySpecialFiber
        (reverseWeightedReesFamily weight level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) bound) = C.ray.face
  special_hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber
        (reverseWeightedReesFamily weight level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) bound)) = 0
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      (reverseWeightedReesFamily weight level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)
      (4 * level - 2 * ∑ i : Fin 4, weight i)
  defect_pos : 0 < 4 * level - 2 * ∑ i : Fin 4, weight i
  positiveLayer :
    HasPositiveActualParameterLayer
      (reverseWeightedReesFamily weight level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)

/-- **A19.104b ray-leading Rees construction.**  The surviving `.qs`
other-facet endpoint admits a positive natural source weight whose exact
maximal face is the already-locked affine ray, with a positive determinant
clock and hence a genuine later source layer. -/
theorem qs_ray_otherFacet_rayReverseRees_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    Nonempty (QsOtherFacetRayReverseReesPackage C) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let j : Fin 4 := HC4.Polynomial.facetOmittedCoordinate .qs
  let w0 : Fin 4 → ℤ :=
    HC4.Newton.scaledContactWeight j C.scale C.bump
  let c0 : ℤ := ((C.scale * T.topFace.degree : ℕ) : ℤ)

  rcases C.qs_ray_otherFacet_contactRees_package hthree hne houtThree with
    ⟨r, _contactBound, hr, hbump, _hsource, _contactSpecial,
      _contactZero, _contactDefect, contactDeltaPos, _contactPositive⟩

  have hcontact :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight w0 e) c0 := by
    rw [C.face_eq]
    exact HC4.Newton.initialForm_support_isExposedFace
      w0 c0 F (by simpa [F, w0, c0, j] using C.source_weight_le)

  rcases C.ray_direct_initialForm_package with
    ⟨v, d, hdirect, _hdirectEq⟩
  have hraySubset :
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
        (↑C.face.support : Set (Fin 4 →₀ ℕ)) := by
    intro e he
    have he' : e ∈ C.ray.face.support := by simpa using he
    have hsub := C.ray.support_subset he'
    simpa using hsub
  have hfaceSubset :
      (↑C.face.support : Set (Fin 4 →₀ ℕ)) ⊆
        (↑F.support : Set (Fin 4 →₀ ℕ)) :=
    hcontact.subset
  have hsecondary :
      HC4.Newton.IsExposedFace
        (↑C.face.support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight v e) d :=
    hdirect.restrict_ambient hraySubset hfaceSubset

  have hsourceNonempty : F.support.Nonempty := by
    have hfaceSet :
        C.crossFacet.facetExponent ∈
          (↑C.face.support : Set (Fin 4 →₀ ℕ)) := by
      simpa using C.crossFacet.facet_mem
    have hsrcSet := hcontact.subset hfaceSet
    exact ⟨C.crossFacet.facetExponent, by simpa using hsrcSet⟩

  have hscaleZ : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  have hbumpZ : (0 : ℤ) < (C.bump : ℤ) := by
    exact_mod_cast C.bump_pos
  have hw0pos : ∀ i : Fin 4, 0 < w0 i := by
    intro i
    by_cases hi : i = j
    · simp [w0, HC4.Newton.scaledContactWeight, hi]
      omega
    · simp [w0, HC4.Newton.scaledContactWeight, hi]
      exact hscaleZ
  have hDpos : 0 < T.topFace.degree := by
    omega
  have hc0pos : 0 < c0 := by
    dsimp [c0]
    exact_mod_cast Nat.mul_pos C.scale_pos hDpos

  have hinnerNat :
      2 * (r + 4) < 4 * T.topFace.degree :=
    Nat.sub_pos_iff_lt.mp contactDeltaPos
  have hinnerZ :
      (2 : ℤ) * ((r : ℤ) + 4) <
        4 * (T.topFace.degree : ℤ) := by
    exact_mod_cast hinnerNat
  have hinner :
      0 < 4 * (T.topFace.degree : ℤ) -
        2 * ((r : ℤ) + 4) := by
    omega
  have hclockEq :
      4 * c0 - 2 * ∑ i : Fin 4, w0 i =
        (C.scale : ℤ) *
          (4 * (T.topFace.degree : ℤ) - 2 * ((r : ℤ) + 4)) := by
    dsimp [c0, w0]
    rw [HC4.Newton.sum_scaledContactWeight]
    rw [hbump]
    push_cast
    ring
  have hclock0 :
      0 < 4 * c0 - 2 * ∑ i : Fin 4, w0 i := by
    rw [hclockEq]
    exact mul_pos hscaleZ hinner

  rcases HC4.Newton.exists_nat_refine_exposed_face_fin4_positive_clock
      F.support hsourceNonempty hcontact hsecondary hw0pos hc0pos hclock0 with
    ⟨M, _hM, hfinalRaw, hweightPosRaw, hlevelPosRaw, hclockPosRaw⟩

  let Wz : Fin 4 → ℤ := fun i => (M : ℤ) * w0 i + v i
  let Lz : ℤ := (M : ℤ) * c0 + d
  have hfinal :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight Wz e) Lz := by
    simpa [Wz, Lz] using hfinalRaw
  have hWzpos : ∀ i : Fin 4, 0 < Wz i := by
    simpa [Wz] using hweightPosRaw
  have hLzpos : 0 < Lz := by
    simpa [Lz] using hlevelPosRaw
  have hclockZ :
      0 < 4 * Lz - 2 * ∑ i : Fin 4, Wz i := by
    simpa [Wz, Lz] using hclockPosRaw
  have hExactZ :
      HC4.Polynomial.initialForm Wz Lz F = C.ray.face :=
    HC4.Newton.initialForm_eq_of_exposedSupport_and_coeff
      Wz Lz F C.ray.face hfinal
      (fun e he => C.ray_coeff_eq_represented_source_of_mem he)

  let W : Fin 4 → ℕ := fun i => Int.toNat (Wz i)
  let D : ℕ := Int.toNat Lz
  have hcastW : (fun i : Fin 4 => (W i : ℤ)) = Wz := by
    funext i
    dsimp [W]
    exact Int.toNat_of_nonneg (le_of_lt (hWzpos i))
  have hcastD : (D : ℤ) = Lz := by
    dsimp [D]
    exact Int.toNat_of_nonneg (le_of_lt hLzpos)
  have hWpos : ∀ i : Fin 4, 0 < W i := by
    intro i
    have h := hWzpos i
    rw [← congrFun hcastW i] at h
    exact_mod_cast h
  have hDpos' : 0 < D := by
    have h := hLzpos
    rw [← hcastD] at h
    exact_mod_cast h

  have hbound : HasReverseWeightBound W D F := by
    intro e he
    have hz := hfinal.weight_le (show e ∈ (↑F.support : Set (Fin 4 →₀ ℕ)) by
      simpa using he)
    rw [← hcastW, ← hcastD] at hz
    rw [weight_natCast_eq W e] at hz
    exact_mod_cast hz

  have hExact :
      HC4.Polynomial.initialForm (fun i => (W i : ℤ)) (D : ℤ) F =
        C.ray.face := by
    rw [hcastW, hcastD]
    exact hExactZ

  have hclockLtZ :
      2 * ∑ i : Fin 4, Wz i < 4 * Lz := by
    omega
  rw [← hcastW, ← hcastD] at hclockLtZ
  have hclockLt :
      2 * ∑ i : Fin 4, W i < 4 * D := by
    exact_mod_cast hclockLtZ
  have hnonneg :
      2 * ∑ i : Fin 4, W i ≤ 4 * D :=
    Nat.le_of_lt hclockLt
  have hDelta :
      0 < 4 * D - 2 * ∑ i : Fin 4, W i :=
    Nat.sub_pos_iff_lt.mpr hclockLt

  have hdetF : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hdef :
      HasPolynomialFamilyHessianDefect (K := K)
        (reverseWeightedReesFamily W D F hbound)
        (4 * D - 2 * ∑ i : Fin 4, W i) :=
    reverseWeightedReesFamily_hasHessianDefect
      (K := K) W D F hbound hdetF hnonneg
  have hspecial :
      polynomialFamilySpecialFiber
          (reverseWeightedReesFamily W D F hbound) = C.ray.face := by
    calc
      polynomialFamilySpecialFiber
          (reverseWeightedReesFamily W D F hbound) =
        HC4.Polynomial.initialForm (fun i => (W i : ℤ)) (D : ℤ) F :=
          polynomialFamilySpecialFiber_reverseWeightedReesFamily W D F hbound
      _ = C.ray.face := hExact
  have hspecialZero :
      HC4.Polynomial.hessianDeterminant
        (polynomialFamilySpecialFiber
          (reverseWeightedReesFamily W D F hbound)) = 0 := by
    rw [hspecial]
    exact C.ray_hessian_zero
  have hpositive :
      HasPositiveActualParameterLayer
        (reverseWeightedReesFamily W D F hbound) :=
    hasPositiveActualParameterLayer_of_hessianDefect_pos _ hdef hDelta

  exact ⟨{
    weight := W
    level := D
    weight_pos := hWpos
    level_pos := hDpos'
    bound := hbound
    initialForm_eq_ray := by simpa [F] using hExact
    specialFiber_eq_ray := by simpa [F] using hspecial
    special_hessian_zero := by simpa [F] using hspecialZero
    hessianDefect := by simpa [F] using hdef
    defect_pos := hDelta
    positiveLayer := by simpa [F] using hpositive
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
