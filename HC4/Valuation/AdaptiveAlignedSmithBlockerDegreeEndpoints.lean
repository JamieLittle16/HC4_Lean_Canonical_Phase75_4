import HC4.Valuation.AdaptiveAlignedSmithCanonicalBlockerCompetition
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# Explicit degree endpoints for the canonical blocker competition

On the canonical scalar Smith wall the ordering functional is identically
zero.  Consequently

    IsOrdinaryDegreePureOnSmithLevel F canonicalZeroSmithBase 0

is not merely purity on a proper subset of the support: every support
monomial lies on that scalar level, so the whole polynomial `F` is ordinary
homogeneous of one degree.

The complementary tied mixed-degree branch already supplies two actual
support monomials of different ordinary degrees.  We retain those witnesses
explicitly and expose the two nonzero homogeneous wall components furnished
by `MixedDegreeWallRefinement`.

This turns the canonical blocker dispatcher into an interface carrying
concrete degrees rather than opaque purity/mixedness predicates.

No progress claim is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Zero-base purity is literal homogeneity -/

/-- Since the canonical scalar functional is constantly zero, purity on its
level `0` is exactly ordinary homogeneity of the whole polynomial. -/
theorem zeroBaseDegreePure_exists_homogeneous
    (F : MvPolynomial (Fin 4) K)
    (h :
      IsOrdinaryDegreePureOnSmithLevel
        F canonicalZeroSmithBase 0) :
    ∃ D : ℕ, F.IsHomogeneous D := by
  rcases h with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro d hd
  have hordinary :
      HC4.Polynomial.ordinaryDegree4 d = D :=
    hD d (MvPolynomial.mem_support_iff.mpr hd) (by rfl)
  have hweight :
      Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  exact
    hweight.trans
      ((finsuppDegree_eq_ordinaryDegree4 d).trans hordinary)

/-- Explicit degree-pure blocker endpoint.

The polynomial recorded here is the genuine longitudinally recentered raw
special fibre from the blocker competition, not an unrelated homogeneous
component.
-/
structure AdaptiveAlignedSmithDegreePureBlockerEndpoint
    (degreeCap : ℕ) where
  blocker :
    AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap
  degree : ℕ
  recentered_homogeneous :
    (longitudinalRightRecenterHom
      (K := K) blocker.aligned.endpoint.rawSpecialFiber).IsHomogeneous
        degree

/-- Build the explicit degree-pure endpoint from the canonical tie
predicate. -/
def AdaptiveAlignedSmithBlockerEndpoint.toDegreePureEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (h :
      IsOrdinaryDegreePureOnSmithLevel
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        canonicalZeroSmithBase 0) :
    Nonempty
      (AdaptiveAlignedSmithDegreePureBlockerEndpoint
        (K := K) degreeCap) := by
  rcases
      zeroBaseDegreePure_exists_homogeneous
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber) h with
    ⟨D, hhom⟩
  exact
    ⟨{
      blocker := B
      degree := D
      recentered_homogeneous := hhom
    }⟩

/-! ## Explicit mixed-degree endpoint -/

/-- A tied mixed-degree blocker retaining two actual support monomials of
different ordinary degrees. -/
structure AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
    (degreeCap : ℕ) where
  blocker :
    AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap
  d₀ : Fin 4 →₀ ℕ
  d₁ : Fin 4 →₀ ℕ
  d₀_mem :
    d₀ ∈
      (longitudinalRightRecenterHom
        (K := K) blocker.aligned.endpoint.rawSpecialFiber).support
  d₁_mem :
    d₁ ∈
      (longitudinalRightRecenterHom
        (K := K) blocker.aligned.endpoint.rawSpecialFiber).support
  degree_ne :
    HC4.Polynomial.ordinaryDegree4 d₀ ≠
      HC4.Polynomial.ordinaryDegree4 d₁

/-- Build the explicit mixed-degree endpoint from the canonical tie
witnesses. -/
def AdaptiveAlignedSmithBlockerEndpoint.toMixedDegreeEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (h :
      ∃ d₀ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
        ∃ d₁ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
          HC4.Polynomial.ordinaryDegree4 d₀ ≠
            HC4.Polynomial.ordinaryDegree4 d₁) :
    Nonempty
      (AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
        (K := K) degreeCap) := by
  rcases h with ⟨d₀, hd₀, d₁, hd₁, hdegree⟩
  exact
    ⟨{
      blocker := B
      d₀ := d₀
      d₁ := d₁
      d₀_mem := hd₀
      d₁_mem := hd₁
      degree_ne := hdegree
    }⟩

/-- The two witness degrees of a mixed endpoint give two distinct, nonzero,
ordinary-homogeneous components of the canonical zero scalar wall.

This is the exact finite refinement datum needed by the downstream
mixed-degree machinery.
-/
theorem AdaptiveAlignedSmithMixedDegreeBlockerEndpoint.two_nonzeroHomogeneousComponents
    {degreeCap : ℕ}
    (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
      (K := K) degreeCap) :
    let F :=
      longitudinalRightRecenterHom
        (K := K) M.blocker.aligned.endpoint.rawSpecialFiber
    let D₀ := HC4.Polynomial.ordinaryDegree4 M.d₀
    let D₁ := HC4.Polynomial.ordinaryDegree4 M.d₁
    D₀ ≠ D₁ ∧
      smithScalarLevelDegreeComponent
        F canonicalZeroSmithBase 0 D₀ ≠ 0 ∧
      smithScalarLevelDegreeComponent
        F canonicalZeroSmithBase 0 D₁ ≠ 0 ∧
      (smithScalarLevelDegreeComponent
        F canonicalZeroSmithBase 0 D₀).IsHomogeneous D₀ ∧
      (smithScalarLevelDegreeComponent
        F canonicalZeroSmithBase 0 D₁).IsHomogeneous D₁ := by
  dsimp only
  exact
    tiedMixedDegreeWall_has_two_nonzeroHomogeneousComponents
      (longitudinalRightRecenterHom
        (K := K) M.blocker.aligned.endpoint.rawSpecialFiber)
      canonicalZeroSmithBase 0
      M.d₀ M.d₁
      M.d₀_mem M.d₁_mem
      (by rfl) (by rfl) M.degree_ne

/-! ## Dispatcher-facing explicit trichotomy -/

/-- Canonical blockers now expose actual finite degree data:

* an already-surviving Smith-grade shape;
* one explicit homogeneous recentered endpoint;
* or one explicit mixed-degree endpoint.

The arbitrary scalar wall and the anonymous degree-purity predicate have
both disappeared from this interface.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_degreePureEndpoint_or_mixedDegreeEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      Nonempty
        (AdaptiveAlignedSmithDegreePureBlockerEndpoint
          (K := K) degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
          (K := K) degreeCap) := by
  rcases
      B.survivingShape_or_zeroBaseDegreePure_or_mixedPair with
    hshape | hpure | hmixed
  · exact Or.inl hshape
  · exact Or.inr (Or.inl (B.toDegreePureEndpoint hpure))
  · exact Or.inr (Or.inr (B.toMixedDegreeEndpoint hmixed))

end

end HC4.Valuation
