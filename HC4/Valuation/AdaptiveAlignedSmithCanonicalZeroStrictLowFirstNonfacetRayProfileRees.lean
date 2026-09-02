import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayQuadraticPreclosing
import Mathlib.Tactic

/-!
# A19.116: profile-ready doubled ray Rees

The A19.110 ray-leading Rees already has the exact rank-three ray as special
fibre and a quadratic clock margin.  For the final binary weighted profile we
also need the distinguished longitudinal source weight to be at least two.
Rather than strengthen the lexicographic-refinement implementation, simply
multiply every source weight and the source level by two.

This preserves the exact exposed face.  The resulting reverse Rees is just a
quadratically reparameterised version of the same filtration: every parameter
order is doubled, the Hessian clock is doubled, and the inequality
`2 * level < defect` is preserved.  In particular its longitudinal profile
weight is `2 * W₀ >= 2` with no further geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Uniform doubling of a natural four-variable source weight. -/
def doubleFin4Weight (w : Fin 4 → ℕ) : Fin 4 → ℕ :=
  fun i => 2 * w i

@[simp] theorem doubleFin4Weight_apply (w : Fin 4 → ℕ) (i : Fin 4) :
    doubleFin4Weight w i = 2 * w i := rfl

/-- Finsupp weight scales exactly under uniform doubling. -/
theorem finsupp_weight_doubleFin4Weight
    (w : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (doubleFin4Weight w) d =
      2 * Finsupp.weight w d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype] <;>
    try { intro i; simp }
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [doubleFin4Weight]
  ring

/-- The integer initial form is unchanged when both a positive weight and its
level are doubled. -/
theorem initialForm_doubleFin4Weight
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.initialForm
        (fun i => (doubleFin4Weight w i : ℤ)) (2 * D : ℤ) F =
      HC4.Polynomial.initialForm
        (fun i => (w i : ℤ)) (D : ℤ) F := by
  classical
  ext d
  rw [HC4.Polynomial.coeff_initialForm, HC4.Polynomial.coeff_initialForm]
  have hweight :
      Finsupp.weight (fun i => (doubleFin4Weight w i : ℤ)) d =
        2 * Finsupp.weight (fun i => (w i : ℤ)) d := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply]
    rw [Finsupp.sum_fintype, Finsupp.sum_fintype] <;>
      try { intro i; simp }
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    simp [doubleFin4Weight]
    ring
  rw [hweight]
  have heq :
      (2 * Finsupp.weight (fun i => (w i : ℤ)) d = (2 * D : ℕ)) ↔
        Finsupp.weight (fun i => (w i : ℤ)) d = (D : ℤ) := by
    push_cast
    constructor <;> intro h <;> nlinarith
  by_cases h : Finsupp.weight (fun i => (w i : ℤ)) d = (D : ℤ)
  · rw [if_pos h]
    apply if_pos
    exact heq.mpr h
  · rw [if_neg h]
    apply if_neg
    intro hs
    exact h (heq.mp hs)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The final ray filtration, uniformly doubled so its longitudinal binary
profile weight is automatically at least two. -/
structure QsOtherFacetRayProfileReesPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (R : QsOtherFacetRayReverseReesPackage C) where
  weight : Fin 4 → ℕ
  weight_eq : weight = doubleFin4Weight R.weight
  level : ℕ
  level_eq : level = 2 * R.level
  bound : HasReverseWeightBound weight level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  profileWeight : ℕ
  profileWeight_eq : profileWeight = weight (0 : Fin 4)
  profileWeight_two_le : 2 ≤ profileWeight
  specialFiber_eq_ray :
    polynomialFamilySpecialFiber
        (reverseWeightedReesFamily weight level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) bound) = C.ray.face
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      (reverseWeightedReesFamily weight level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)
      (4 * level - 2 * ∑ i : Fin 4, weight i)
  two_level_lt_defect :
    2 * level < 4 * level - 2 * ∑ i : Fin 4, weight i
  positiveLayer :
    HasPositiveActualParameterLayer
      (reverseWeightedReesFamily weight level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)

/-- **A19.116 profile-ready ray Rees.** -/
theorem QsOtherFacetRayReverseReesPackage.profileReesPackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C) :
    Nonempty (QsOtherFacetRayProfileReesPackage C R) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let W : Fin 4 → ℕ := doubleFin4Weight R.weight
  let D : ℕ := 2 * R.level
  have hbound : HasReverseWeightBound W D F := by
    intro d hd
    rw [finsupp_weight_doubleFin4Weight]
    have h := R.bound d (by simpa [F] using hd)
    dsimp [D]
    omega
  have hsum :
      ∑ i : Fin 4, W i = 2 * ∑ i : Fin 4, R.weight i := by
    dsimp [W]
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    ring
  have hnonneg :
      2 * ∑ i : Fin 4, W i ≤ 4 * D := by
    rw [hsum]
    dsimp [D]
    have h := R.defect_pos
    omega
  have htwo :
      2 * D < 4 * D - 2 * ∑ i : Fin 4, W i := by
    rw [hsum]
    dsimp [D]
    have h := R.two_level_lt_defect
    omega
  have hdelta :
      0 < 4 * D - 2 * ∑ i : Fin 4, W i := by
    omega
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
  have hinit :
      HC4.Polynomial.initialForm (fun i => (W i : ℤ)) (D : ℤ) F =
        C.ray.face := by
    change HC4.Polynomial.initialForm
        (fun i => (doubleFin4Weight R.weight i : ℤ))
        ((2 * R.level : ℕ) : ℤ) F = C.ray.face
    calc
      HC4.Polynomial.initialForm
          (fun i => (doubleFin4Weight R.weight i : ℤ))
          ((2 * R.level : ℕ) : ℤ) F =
          HC4.Polynomial.initialForm
            (fun i => (doubleFin4Weight R.weight i : ℤ))
            (2 * (R.level : ℤ)) F := by rw [Nat.cast_mul, Nat.cast_ofNat]
      _ = HC4.Polynomial.initialForm
            (fun i => (R.weight i : ℤ)) (R.level : ℤ) F :=
        initialForm_doubleFin4Weight R.weight R.level F
      _ = C.ray.face := by simpa [F] using R.initialForm_eq_ray
  have hspecial :
      polynomialFamilySpecialFiber
          (reverseWeightedReesFamily W D F hbound) = C.ray.face := by
    rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
    exact hinit
  have hpositive :
      HasPositiveActualParameterLayer
        (reverseWeightedReesFamily W D F hbound) :=
    hasPositiveActualParameterLayer_of_hessianDefect_pos _ hdef hdelta
  have hprofile : 2 ≤ W (0 : Fin 4) := by
    dsimp [W, doubleFin4Weight]
    have h := R.weight_pos (0 : Fin 4)
    omega
  exact ⟨{
    weight := W
    weight_eq := rfl
    level := D
    level_eq := rfl
    bound := hbound
    profileWeight := W (0 : Fin 4)
    profileWeight_eq := rfl
    profileWeight_two_le := hprofile
    specialFiber_eq_ray := by simpa [F] using hspecial
    hessianDefect := by simpa [F] using hdef
    two_level_lt_defect := htwo
    positiveLayer := by simpa [F] using hpositive
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
