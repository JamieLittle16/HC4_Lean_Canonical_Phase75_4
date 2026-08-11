import HC4.Newton.MixedDegreeAxisCollision
import HC4.Newton.SmithFirstWallGradeClassification
import HC4.Polynomial.FourExponent
import Mathlib.Tactic

/-!
# Mixed-degree first-wall competition

The Smith grade is pair-valued and is not itself the scalar order selecting
the old first wall.  The actual restart machinery carries a scalar
valuation `base : SmithSupportExponent → ℤ`.  This file compares the
concrete recentered blocker witness against a genuine finite minimum of that
scalar valuation, and keeps ordinary-degree purity as an explicit extra
condition on a tied wall.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Exhaustive mixed-degree classification of an actual Smith support
exponent after zero-jet normalization.  The four old blocker cases retain
their geometric residual data; the last constructor is exactly the
arithmetic surviving-grade interface already proved by the fixed-degree
development. -/
inductive MixedDegreeSmithExponentOutcome
    (F : MvPolynomial (Fin 4) K) (e : SmithSupportExponent) : Prop
  | pureLongitudinal
      (A C : Polynomial K)
      (hpattern : IsPureLongitudinalSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalAxisRestriction F)
      (hC : C ≠ 0)
      (hfactor : A.derivative =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * C)
      (hdegree : C.natDegree < A.derivative.natDegree)
  | lowNegativeFirst
      (A B : Polynomial K)
      (hpattern : IsLowNegativeFirstSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalCoefficientPolynomial e.b e.c e.d F)
      (hB : B ≠ 0)
      (hfactor : A =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
      (hdegree : B.natDegree + 2 = A.natDegree)
  | lowNegativeSecond
      (A B : Polynomial K)
      (hpattern : IsLowNegativeSecondSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalCoefficientPolynomial e.b e.c e.d F)
      (hB : B ≠ 0)
      (hfactor : A =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
      (hdegree : B.natDegree + 2 = A.natDegree)
  | wLinear
      (A B : Polynomial K)
      (hpattern : IsWLinearSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalCoefficientPolynomial e.b e.c e.d F)
      (hB : B ≠ 0)
      (hfactor : A =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
      (hdegree : B.natDegree + 2 = A.natDegree)
  | surviving
      (hshape : HasGeneralSurvivingSmithGradeShape e)

/-- Every actual projected exponent of a zero-jet-normalized collision is
either one of the four old blockers with concrete residual data, or has the
existing general surviving Smith-grade shape. -/
theorem projectedSmithExponent_mixedDegreeOutcome
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0) :
    MixedDegreeSmithExponentOutcome F e := by
  by_cases hpure : IsPureLongitudinalSmithPattern e
  · rcases projectedSupport_pureLongitudinal_twoEndpointResidualData
        F e he hpure hcoll hzero hvalue with
      ⟨A, C, hA, hAeq, hC, hfactor, hdegree⟩
    exact .pureLongitudinal A C hpure hA hAeq hC hfactor hdegree
  by_cases hfirst : IsLowNegativeFirstSmithPattern e
  · rcases projectedSupport_transverseLinear_twoEndpointResidualData
        F e he 1
        (smithTransverseExponent_eq_single_one_of_lowNegativeFirst e hfirst)
        hcoll hzero with ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩
    exact .lowNegativeFirst A B hfirst hA hAeq hB hfactor hdegree
  by_cases hsecond : IsLowNegativeSecondSmithPattern e
  · rcases projectedSupport_transverseLinear_twoEndpointResidualData
        F e he 0
        (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond e hsecond)
        hcoll hzero with ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩
    exact .lowNegativeSecond A B hsecond hA hAeq hB hfactor hdegree
  by_cases hw : IsWLinearSmithPattern e
  · rcases projectedSupport_transverseLinear_twoEndpointResidualData
        F e he 2
        (smithTransverseExponent_eq_single_two_of_wLinear e hw)
        hcoll hzero with ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩
    exact .wLinear A B hw hA hAeq hB hfactor hdegree
  · exact .surviving
      (generalSurvivingSmithGradeShape_of_noNegativeLowPatterns
        e ⟨hpure, hfirst, hsecond⟩)

/-- Projected-support invariance transfers every exponent found after
right-endpoint recentering back to the original zero-jet-normalized
collision, where the exhaustive mixed-degree blocker classification
applies.  This is the adapter used by the strict-earlier-wall branch. -/
theorem recenteredProjectedSmithExponent_mixedDegreeOutcome
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (longitudinalRightRecenterHom (K := K) F))
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0) :
    MixedDegreeSmithExponentOutcome F e := by
  have heOriginal : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F := by
    rw [← smithProjectedSupport_longitudinalRightRecenterHom F]
    exact he
  exact projectedSmithExponent_mixedDegreeOutcome
    F e heOriginal hcoll hzero hvalue

/-- Face-level wiring for the existing symmetric Smith geometry.  On an
actual scalar level of the projected support, either one exponent is an old
blocker (and its full mixed-degree residual outcome is retained), or every
exponent on that level has the general surviving shape and the `w`-linear
pattern is absent.  The latter pair is precisely the arithmetic interface
consumed by the existing symmetric refinement theorems. -/
theorem minimalSmithLevel_blockerOutcome_or_survivingFace
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      (HasGeneralSurvivingSmithFaceShape
          (smithProjectedSupport (1 : Fin 4) 2 3 F) level base ∧
       ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
         base e = level → ¬ IsWLinearSmithPattern e) := by
  by_cases hblocker :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e)
  · rcases hblocker with ⟨e, he, helevel, hpattern⟩
    exact Or.inl ⟨e, he, helevel, hpattern,
      projectedSmithExponent_mixedDegreeOutcome
        F e he hcoll hzero hvalue⟩
  · right
    constructor
    · intro e he helevel
      apply generalSurvivingSmithGradeShape_of_noNegativeLowPatterns
      refine ⟨?_, ?_, ?_⟩
      · intro hpure
        exact hblocker ⟨e, he, helevel, Or.inl hpure⟩
      · intro hfirst
        exact hblocker ⟨e, he, helevel, Or.inr (Or.inl hfirst)⟩
      · intro hsecond
        exact hblocker ⟨e, he, helevel,
          Or.inr (Or.inr (Or.inl hsecond))⟩
    · intro e he helevel hw
      exact hblocker ⟨e, he, helevel, Or.inr (Or.inr (Or.inr hw))⟩

/-- Under the symmetric pole-minimality hypotheses already carried by the
Smith wall machinery, the face-level surviving branch immediately enters
the existing nonempty quadratic refinement.  Thus no further mixed-degree
algebra is needed for this branch before homogeneous packet extraction. -/
theorem minimalSmithLevel_blockerOutcome_or_symmetricQuadraticRefinement
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport (1 : Fin 4) 2 3 F) level base)
    (hmin :
      ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      ((smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 F) level base).Nonempty ∧
       ∀ e ∈ smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 F) level base,
         (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
         (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
         (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) := by
  rcases minimalSmithLevel_blockerOutcome_or_survivingFace
      F base level hcoll hzero hvalue with hblocker | ⟨hshape, hnoW⟩
  · exact Or.inl hblocker
  · exact Or.inr
      (symmetricSmithPoleMinimal_symmetricRefinement_quadratic
        (smithProjectedSupport (1 : Fin 4) 2 3 F) level base
        hpole hmin hattain hshape hnoW)

/-! ## Integral combined weight on the surviving adaptive wall -/

/-- Geometric realizability of an abstract scalar Smith grade.  The
classifier remains polymorphic in `base`; an actual Rees exposure must carry
this additional certificate saying that `base` is induced by nonnegative
integral transverse source weights. -/
structure HasIntegralAdaptiveSmithWallWeight
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ) where
  transverseWeight : Fin 3 → ℕ
  offset : ℤ
  realizes :
    ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      base e = offset +
        (transverseWeight 0 : ℤ) * (e.b : ℤ) +
        (transverseWeight 1 : ℤ) * (e.c : ℤ) +
        (transverseWeight 2 : ℤ) * (e.d : ℤ)

/-- The geometry-bearing version of a surviving adaptive wall.  This is a
wrapper around, not a replacement for, the abstract mixed-degree
classifier interface. -/
structure IntegralAdaptiveSurvivingSmithWall
    (F : MvPolynomial (Fin 4) K) where
  base : SmithSupportExponent → ℤ
  level : ℤ
  realization : HasIntegralAdaptiveSmithWallWeight F base
  symmetricMinimal :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport (1 : Fin 4) 2 3 F) level base
  minimal :
    ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      level ≤ base e
  attained :
    ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      base e = level
  survivingShape :
    HasGeneralSurvivingSmithFaceShape
      (smithProjectedSupport (1 : Fin 4) 2 3 F) level base

/-- Explicit transverse source weight for the combined primary/symmetric
exposure.  Coordinate `0` is left unweighted, while the three transverse
weights are `5w₁+2`, `5w₂+2`, and `5w₃+4`. -/
def HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight
    {F : MvPolynomial (Fin 4) K}
    {base : SmithSupportExponent → ℤ}
    (h : HasIntegralAdaptiveSmithWallWeight F base) : Fin 4 → ℕ :=
  ![0,
    5 * h.transverseWeight 0 + 2,
    5 * h.transverseWeight 1 + 2,
    5 * h.transverseWeight 2 + 4]

@[simp] theorem HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight_zero
    {F : MvPolynomial (Fin 4) K}
    {base : SmithSupportExponent → ℤ}
    (h : HasIntegralAdaptiveSmithWallWeight F base) :
    h.combinedSourceWeight 0 = 0 := by
  simp [HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight]

/-- Affine source-weight level corresponding to the zero value of the
combined adaptive Smith weight. -/
def HasIntegralAdaptiveSmithWallWeight.combinedSourceLevel
    {F : MvPolynomial (Fin 4) K}
    {base : SmithSupportExponent → ℤ}
    (h : HasIntegralAdaptiveSmithWallWeight F base)
    (level : ℤ) : ℤ :=
  5 * (level - h.offset) + 4

/-- The integral weight which first selects the scalar wall and then the
canonical symmetric Smith balance.  The multiplier `5` is one larger than
the absolute universal lower bound `-4` for the symmetric separator. -/
def adaptiveCombinedSmithWeight
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (e : SmithSupportExponent) : ℤ :=
  5 * (base e - level) + smithSeparatorDelta 1 1 e

/-- The abstract combined Smith weight is literally source weighted degree
minus one fixed affine level whenever `base` has an integral geometric
realization. -/
theorem combinedSourceWeight_degree_sub_level_eq
    {F : MvPolynomial (Fin 4) K}
    {base : SmithSupportExponent → ℤ}
    (h : HasIntegralAdaptiveSmithWallWeight F base)
    (level : ℤ)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ F.support) :
    Finsupp.weight (fun i ↦ (h.combinedSourceWeight i : ℤ)) d -
        h.combinedSourceLevel level =
      adaptiveCombinedSmithWeight base level
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
        smithProjectedSupport (1 : Fin 4) 2 3 F := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hreal := h.realizes _ hproj
  have hdelta : smithSeparatorDelta 1 1
      (smithSupportExponentOf (1 : Fin 4) 2 3 d) =
        2 * (((d 1 : ℕ) : ℤ) + ((d 2 : ℕ) : ℤ) +
          2 * ((d 3 : ℕ) : ℤ) - 2) := by
    unfold smithSeparatorDelta SmithSupportExponent.grade smithGradeDot
      smithGrade smithGradeFirst smithGradeSecond smithExtremeSeparator
    simp only [smithSupportExponentOf_b, smithSupportExponentOf_c,
      smithSupportExponentOf_d]
    push_cast
    ring
  simp only [smithSupportExponentOf_b, smithSupportExponentOf_c,
    smithSupportExponentOf_d] at hreal
  rw [Finsupp.weight_apply]
  simp [HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight,
    HasIntegralAdaptiveSmithWallWeight.combinedSourceLevel,
    adaptiveCombinedSmithWeight, Finsupp.sum_fintype,
    Fin.sum_univ_four, hdelta]
  rw [hreal]
  ring

/-- The actual blocker/surviving split preserves geometric wall
realizability instead of manufacturing it after classification. -/
theorem adaptiveWall_blocker_or_integralSurvivingWall
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hreal : HasIntegralAdaptiveSmithWallWeight F base)
    (hmin :
      ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport (1 : Fin 4) 2 3 F) level base)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 ↦ 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 ↦ 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 ↦ 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 ↦ 0)) F = 0) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      Nonempty (IntegralAdaptiveSurvivingSmithWall F) := by
  rcases minimalSmithLevel_blockerOutcome_or_survivingFace
      F base level hcoll hzero hvalue with hblocker | ⟨hshape, _hnoW⟩
  · exact Or.inl hblocker
  · exact Or.inr ⟨
      { base := base
        level := level
        realization := hreal
        symmetricMinimal := hpole
        minimal := hmin
        attained := hattain
        survivingShape := hshape }⟩

/-- On the non-blocker surviving branch, the combined adaptive weight is
nonnegative on every projected support exponent.  At the primary minimum
this uses the surviving-shape sign theorem; strictly above the minimum the
factor `5` dominates the universal separator lower bound `-4`. -/
theorem adaptiveCombinedSmithWeight_nonnegative
    (S : Finset SmithSupportExponent)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hmin : ∀ e ∈ S, level ≤ base e)
    (hshape : HasGeneralSurvivingSmithFaceShape S level base)
    {e : SmithSupportExponent}
    (he : e ∈ S) :
    0 ≤ adaptiveCombinedSmithWeight base level e := by
  have hbase := hmin e he
  by_cases hlevel : base e = level
  · have hdelta : 0 ≤ smithSeparatorDelta 1 1 e :=
      smithSeparatorDelta_one_one_nonnegative_of_generalShape
        e (hshape e he hlevel)
    simp [adaptiveCombinedSmithWeight, hlevel, hdelta]
  · have hgap : level + 1 ≤ base e := by omega
    have hlower : (-4 : ℤ) ≤ smithSeparatorDelta 1 1 e :=
      smithSeparatorDelta_lower_bound 1 1 e
    unfold adaptiveCombinedSmithWeight
    omega

/-- Exact zero set of the combined weight on the surviving adaptive wall.
This is the arithmetic statement required for an honest one-parameter Rees
exposure of `smithSymmetricBalancedSubface`. -/
theorem adaptiveCombinedSmithWeight_eq_zero_iff
    (S : Finset SmithSupportExponent)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hmin : ∀ e ∈ S, level ≤ base e)
    {e : SmithSupportExponent}
    (he : e ∈ S) :
    adaptiveCombinedSmithWeight base level e = 0 ↔
      base e = level ∧ smithSeparatorDelta 1 1 e = 0 := by
  constructor
  · intro hzero
    have hbase := hmin e he
    have hlower : (-4 : ℤ) ≤ smithSeparatorDelta 1 1 e :=
      smithSeparatorDelta_lower_bound 1 1 e
    have hlevel : base e = level := by
      by_contra hne
      have hgap : level + 1 ≤ base e := by omega
      unfold adaptiveCombinedSmithWeight at hzero
      omega
    have hdelta : smithSeparatorDelta 1 1 e = 0 := by
      unfold adaptiveCombinedSmithWeight at hzero
      omega
    exact ⟨hlevel, hdelta⟩
  · rintro ⟨hlevel, hdelta⟩
    simp [adaptiveCombinedSmithWeight, hlevel, hdelta]

/-- Membership in the balanced subface is exactly vanishing of the combined
integral exposure weight, among exponents of the ambient support. -/
theorem adaptiveCombinedSmithWeight_eq_zero_iff_mem_balancedSubface
    (S : Finset SmithSupportExponent)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hmin : ∀ e ∈ S, level ≤ base e)
    {e : SmithSupportExponent}
    (he : e ∈ S) :
    adaptiveCombinedSmithWeight base level e = 0 ↔
      e ∈ smithSymmetricBalancedSubface S level base := by
  rw [adaptiveCombinedSmithWeight_eq_zero_iff S base level hmin he]
  simp [he]

/-- Ordinary source-degree purity on one scalar Smith wall. -/
def IsOrdinaryDegreePureOnSmithLevel
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ) : Prop :=
  ∃ D : ℕ,
    ∀ d ∈ F.support,
      base (smithSupportExponentOf (1 : Fin 4) 2 3 d) = level →
        HC4.Polynomial.ordinaryDegree4 d = D

/-- Every concrete source-support point contributes its Smith projection to
the projected support. -/
theorem smithSupportExponentOf_mem_projectedSupport
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support) :
    smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
      smithProjectedSupport (1 : Fin 4) 2 3 F := by
  classical
  unfold smithProjectedSupport
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- The exact-first-order branch gives an actual projected support element
whose pair-valued Smith grade is exactly the original blocker grade. -/
theorem recenteredCandidate_mem_projectedSupport_and_grade
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (B : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hBfirst : Polynomial.eval 1 B ≠ 0) :
    ∃ ecand ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom (K := K) F),
      ecand.grade = e.grade := by
  let d := (smithTransverseExponent e.b e.c e.d).cons 1
  rcases twoEndpointResidual_exactFirst_recenteredSupportWitness
      F e B hfactor hBfirst with ⟨hd, hb, hc, hw⟩
  let ecand := smithSupportExponentOf (1 : Fin 4) 2 3 d
  refine ⟨ecand,
    smithSupportExponentOf_mem_projectedSupport
      (longitudinalRightRecenterHom (K := K) F) d hd, ?_⟩
  unfold ecand SmithSupportExponent.grade smithSupportExponentOf smithGrade
  dsimp only
  rw [hb, hc, hw]

/-- After the inner residual recursion terminates, its exact layer is still
an actual recentered projected-support candidate with the original blocker
grade. -/
theorem recenteredTerminalResidualCandidate_mem_projectedSupport_and_grade
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (B : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hnormal : EndpointResidualNormalForm B) :
    ∃ ecand ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom (K := K) F),
      ecand.grade = e.grade := by
  let n := hnormal.multiplicity + 1
  let d := (smithTransverseExponent e.b e.c e.d).cons n
  rcases endpointResidualNormalForm_recenteredSupportWitness
      F e B hfactor hnormal with ⟨hd, hb, hc, hw⟩
  let ecand := smithSupportExponentOf (1 : Fin 4) 2 3 d
  refine ⟨ecand,
    smithSupportExponentOf_mem_projectedSupport
      (longitudinalRightRecenterHom (K := K) F) d hd, ?_⟩
  unfold ecand SmithSupportExponent.grade smithSupportExponentOf smithGrade
  dsimp only
  rw [hb, hc, hw]

/-- A nonempty finite projected support has a genuine minimum for every
scalar wall valuation. -/
theorem exists_scalarMinimalSmithExponent
    (S : Finset SmithSupportExponent)
    (base : SmithSupportExponent → ℤ)
    (hS : S.Nonempty) :
    ∃ emin ∈ S, ∀ e ∈ S, base emin ≤ base e := by
  exact Finset.exists_min_image S base hS

/-- Compare a concrete candidate with a true scalar minimum, separating a
strictly earlier wall from a tied wall. -/
theorem scalarMinimal_strictEarlier_or_tied
    (S : Finset SmithSupportExponent)
    (base : SmithSupportExponent → ℤ)
    (ecand : SmithSupportExponent)
    (hcand : ecand ∈ S) :
    ∃ emin ∈ S,
      (∀ e ∈ S, base emin ≤ base e) ∧
      (base emin < base ecand ∨ base emin = base ecand) := by
  rcases exists_scalarMinimalSmithExponent S base ⟨ecand, hcand⟩ with
    ⟨emin, hemin, hleast⟩
  refine ⟨emin, hemin, hleast, ?_⟩
  have hle := hleast ecand hcand
  omega

/-- If a nonempty scalar wall is not ordinary-degree pure, it contains two
actual source monomials of different ordinary degrees. -/
theorem mixedDegreePair_of_not_degreePure
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hlevel :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level)
    (hnot : ¬ IsOrdinaryDegreePureOnSmithLevel F base level) :
    ∃ d₀ ∈ F.support, ∃ d₁ ∈ F.support,
      base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = level ∧
      base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) = level ∧
      HC4.Polynomial.ordinaryDegree4 d₀ ≠
        HC4.Polynomial.ordinaryDegree4 d₁ := by
  rcases hlevel with ⟨e, he, helevel⟩
  rcases smithProjectedSupport_realised (1 : Fin 4) 2 3 F e he with
    ⟨d₀, hd₀, hd₀e⟩
  have hd₀level :
      base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = level := by
    rw [hd₀e, helevel]
  by_contra hnoPair
  apply hnot
  refine ⟨HC4.Polynomial.ordinaryDegree4 d₀, ?_⟩
  intro d hd hdlevel
  by_contra hdegree
  apply hnoPair
  exact ⟨d₀, MvPolynomial.mem_support_iff.mpr hd₀,
    d, hd, hd₀level, hdlevel, Ne.symm hdegree⟩

/-- Complete finite competition at a tied scalar wall: either the minimum
wall is degree-pure, or it contains an explicit equal-level mixed-degree
pair. -/
theorem scalarSmithLevel_degreePure_or_mixedPair
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hlevel :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level) :
    IsOrdinaryDegreePureOnSmithLevel F base level ∨
      ∃ d₀ ∈ F.support, ∃ d₁ ∈ F.support,
        base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = level ∧
        base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) = level ∧
        HC4.Polynomial.ordinaryDegree4 d₀ ≠
          HC4.Polynomial.ordinaryDegree4 d₁ := by
  by_cases hpure : IsOrdinaryDegreePureOnSmithLevel F base level
  · exact Or.inl hpure
  · exact Or.inr (mixedDegreePair_of_not_degreePure
      F base level hlevel hpure)

/-- The complete first-wall competition generated by an exact recentered
blocker.  Besides retaining the candidate's pair grade, the conclusion
separates a strictly earlier scalar wall from the two tied possibilities:
ordinary-degree purity and an explicit mixed-degree pair.  In particular,
the tied branch cannot be passed silently to a fixed-degree classifier. -/
theorem recenteredBlocker_firstWallCompetition
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (B : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hBfirst : Polynomial.eval 1 B ≠ 0)
    (base : SmithSupportExponent → ℤ) :
    ∃ ecand ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom (K := K) F),
      ecand.grade = e.grade ∧
      ((∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (longitudinalRightRecenterHom (K := K) F),
            base emin ≤ base q) ∧
          base emin < base ecand) ∨
       (∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (longitudinalRightRecenterHom (K := K) F),
            base emin ≤ base q) ∧
          base emin = base ecand ∧
          (IsOrdinaryDegreePureOnSmithLevel
              (longitudinalRightRecenterHom (K := K) F) base (base emin) ∨
           ∃ d₀ ∈ (longitudinalRightRecenterHom (K := K) F).support,
             ∃ d₁ ∈ (longitudinalRightRecenterHom (K := K) F).support,
               base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = base emin ∧
               base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) = base emin ∧
               HC4.Polynomial.ordinaryDegree4 d₀ ≠
                 HC4.Polynomial.ordinaryDegree4 d₁))) := by
  let Frec := longitudinalRightRecenterHom (K := K) F
  rcases recenteredCandidate_mem_projectedSupport_and_grade
      F e B hfactor hBfirst with ⟨ecand, hecand, hgrade⟩
  refine ⟨ecand, hecand, hgrade, ?_⟩
  rcases scalarMinimal_strictEarlier_or_tied
      (smithProjectedSupport (1 : Fin 4) 2 3 Frec) base ecand hecand with
    ⟨emin, hemin, hleast, hstrict | htied⟩
  · exact Or.inl ⟨emin, hemin, hleast, hstrict⟩
  · refine Or.inr ⟨emin, hemin, hleast, htied, ?_⟩
    apply scalarSmithLevel_degreePure_or_mixedPair Frec base (base emin)
    exact ⟨emin, hemin, rfl⟩

/-- Wall-level interpretation of the terminal inner residual.  The exact
layer at order `q+1` enters the same exhaustive scalar first-wall
competition as the old first-order residual branch. -/
theorem recenteredTerminalResidual_firstWallCompetition
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (B : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hnormal : EndpointResidualNormalForm B)
    (base : SmithSupportExponent → ℤ) :
    ∃ ecand ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom (K := K) F),
      ecand.grade = e.grade ∧
      ((∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (longitudinalRightRecenterHom (K := K) F),
            base emin ≤ base q) ∧
          base emin < base ecand) ∨
       (∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
              (longitudinalRightRecenterHom (K := K) F),
            base emin ≤ base q) ∧
          base emin = base ecand ∧
          (IsOrdinaryDegreePureOnSmithLevel
              (longitudinalRightRecenterHom (K := K) F) base (base emin) ∨
           ∃ d₀ ∈ (longitudinalRightRecenterHom (K := K) F).support,
             ∃ d₁ ∈ (longitudinalRightRecenterHom (K := K) F).support,
               base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = base emin ∧
               base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) = base emin ∧
               HC4.Polynomial.ordinaryDegree4 d₀ ≠
                 HC4.Polynomial.ordinaryDegree4 d₁))) := by
  let Frec := longitudinalRightRecenterHom (K := K) F
  rcases recenteredTerminalResidualCandidate_mem_projectedSupport_and_grade
      F e B hfactor hnormal with ⟨ecand, hecand, hgrade⟩
  refine ⟨ecand, hecand, hgrade, ?_⟩
  rcases scalarMinimal_strictEarlier_or_tied
      (smithProjectedSupport (1 : Fin 4) 2 3 Frec) base ecand hecand with
    ⟨emin, hemin, hleast, hstrict | htied⟩
  · exact Or.inl ⟨emin, hemin, hleast, hstrict⟩
  · refine Or.inr ⟨emin, hemin, hleast, htied, ?_⟩
    apply scalarSmithLevel_degreePure_or_mixedPair Frec base (base emin)
    exact ⟨emin, hemin, rfl⟩

end

end HC4.Newton
