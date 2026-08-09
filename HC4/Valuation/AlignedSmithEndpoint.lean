import HC4.Valuation.AlignedSmithFirstStop
import Mathlib.Tactic

/-!
# Genuine aligned Smith endpoint

Phase 93.67 constructed a finite first-stop transform using an auxiliary
sentinel cap.  The cap was useful for proving the transformation algebra,
but it should not appear in the mathematical endpoint classification.

This file removes it.

We form the finite set consisting only of genuine walls:

* negative-derivative coefficient walls;
* left marked-section walls;
* right marked-section walls.

If this set is nonempty, its minimum is the genuine first wall.  The
Phase 93.67 arithmetic immediately proves that every coefficient and both
marked sections remain integral up to that minimum.  The endpoint is
therefore an actual coefficient or section wall.

If the genuine wall set is empty, the situation is rigid:

* no source coefficient has negative symmetric Smith derivative;
* every transverse coordinate of both moving sections is identically zero.

The main new argument is that the coefficient derivatives cannot all be
strictly positive.  If they were, choose the integer Smith step

    N = 3*Delta + 1

after the single ramification by twenty.  Every normalised coefficient then
retains at least `2*N` parameter powers.  Thus the whole transformed
potential has the common factor `X^(2*N)`.

A general four-variable common-factor estimate proved below gives

    4*(2*N) <= 20*Delta,

contradicting `N = 3*Delta+1`.

Hence in the no-wall branch some genuine source monomial has symmetric
Smith derivative exactly zero.

This is the scale-safe finite endpoint statement wanted from the maximal
Smith normalisation:

    genuine wall
      OR
    no walls and a zero-grade source monomial.

The remaining geometric adapter is now sharply local: at a coefficient
wall or zero-grade no-wall endpoint, identify the corresponding primitive
coefficient on the special fibre; at a section wall, interpret the marked
point boundary.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Genuine wall set and first genuine wall -/

/-- The finite set of actual coefficient and marked-section walls. -/
noncomputable def alignedSmithGenuineWalls
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K) :
    Finset ℕ :=
  alignedSmithCoefficientWalls P ∪
    alignedSmithSectionWalls a ∪
    alignedSmithSectionWalls b

/-- There is at least one genuine aligned Smith wall. -/
def HasAlignedSmithGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K) : Prop :=
  (alignedSmithGenuineWalls P a b).Nonempty

/-- Minimum genuine wall, when one exists. -/
noncomputable def alignedSmithGenuineFirstWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    ℕ :=
  (alignedSmithGenuineWalls P a b).min' hwall

theorem alignedSmithGenuineFirstWall_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    alignedSmithGenuineFirstWall P a b hwall ∈
      alignedSmithGenuineWalls P a b := by
  unfold alignedSmithGenuineFirstWall
  exact
    Finset.min'_mem
      (alignedSmithGenuineWalls P a b)
      hwall

theorem alignedSmithGenuineFirstWall_le_of_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    {N : ℕ}
    (hN : N ∈ alignedSmithGenuineWalls P a b) :
    alignedSmithGenuineFirstWall P a b hwall ≤ N := by
  unfold alignedSmithGenuineFirstWall
  exact
    Finset.min'_le
      (alignedSmithGenuineWalls P a b)
      N hN

/-- The genuine first wall is one of the three actual wall types. -/
theorem alignedSmithGenuineFirstWall_cases
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P ∨
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls a ∨
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls b := by
  have hmem :=
    alignedSmithGenuineFirstWall_mem P a b hwall
  simpa [alignedSmithGenuineWalls,
    Finset.mem_union] using hmem

/-! ## Exact witnesses for the three genuine wall types -/

/-- Membership in the coefficient-wall set comes from an actual supported
negative-derivative monomial. -/
theorem mem_alignedSmithCoefficientWalls_exists_source
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {N : ℕ}
    (hN : N ∈ alignedSmithCoefficientWalls P) :
    ∃ d : Fin 4 →₀ ℕ,
      d ∈ P.support ∧
      smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0 ∧
      alignedSmithCoefficientWallStep P d = N := by
  classical
  unfold alignedSmithCoefficientWalls at hN
  rcases Finset.mem_image.mp hN with
    ⟨d, hdneg, hstep⟩
  have hd :=
    (mem_negativeSmithSourceSupport P).1 hdneg
  exact
    ⟨d, hd.1, hd.2, hstep⟩

/-- At a coefficient wall, that source coefficient has aligned order
exactly zero. -/
theorem alignedSmithCoefficientWall_member_value_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {N : ℕ}
    (hN : N ∈ alignedSmithCoefficientWalls P) :
    ∃ d : Fin 4 →₀ ℕ,
      d ∈ P.support ∧
      smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0 ∧
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        N
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) = 0 := by
  rcases
      mem_alignedSmithCoefficientWalls_exists_source
        P hN with
    ⟨d, hd, hneg, hstep⟩
  refine ⟨d, hd, hneg, ?_⟩
  rw [← hstep]
  exact
    alignedSmithCoefficientWallStep_value_zero
      P hd hneg

/-- Membership in a section-wall set comes from an actual nonzero
transverse coordinate. -/
theorem mem_alignedSmithSectionWalls_exists_coordinate
    (a : Fin 4 → Polynomial K)
    {N : ℕ}
    (hN : N ∈ alignedSmithSectionWalls a) :
    ∃ i : Fin 4,
      i ≠ 0 ∧
      a i ≠ 0 ∧
      alignedSmithSectionWallStep i (a i) = N := by
  classical
  unfold alignedSmithSectionWalls at hN
  rcases Finset.mem_image.mp hN with
    ⟨i, hi, hstep⟩
  have hidata :=
    (mem_nonzeroSmithTransverseCoordinates a).1 hi
  exact
    ⟨i, hidata.1, hidata.2, hstep⟩

/-- At a section wall, the corresponding aligned section order is exactly
zero. -/
theorem alignedSmithSectionWall_member_value_zero
    (a : Fin 4 → Polynomial K)
    {N : ℕ}
    (hN : N ∈ alignedSmithSectionWalls a) :
    ∃ i : Fin 4,
      i ≠ 0 ∧
      a i ≠ 0 ∧
      ((i = 3 ∧
          alignedSmithSectionValueFour
            (sectionCoordinateParameterOrder (a i))
            N = 0) ∨
        (i ≠ 3 ∧
          alignedSmithSectionValueTwo
            (sectionCoordinateParameterOrder (a i))
            N = 0)) := by
  rcases
      mem_alignedSmithSectionWalls_exists_coordinate
        a hN with
    ⟨i, hi0, hine, hstep⟩
  refine ⟨i, hi0, hine, ?_⟩
  by_cases hi3 : i = 3
  · left
    refine ⟨hi3, ?_⟩
    subst i
    unfold alignedSmithSectionWallStep at hstep
    simp only [if_pos rfl] at hstep
    rw [← hstep]
    exact
      alignedSmithSectionValueFour_wall
        (sectionCoordinateParameterOrder (a 3))
  · right
    refine ⟨hi3, ?_⟩
    unfold alignedSmithSectionWallStep at hstep
    rw [if_neg hi3] at hstep
    rw [← hstep]
    exact
      alignedSmithSectionValueTwo_wall
        (sectionCoordinateParameterOrder (a i))

/-! ## Integrality at the genuine first wall -/

/-- Every source coefficient remains integral up to the genuine first
wall. -/
theorem alignedSmithGenuineFirstWall_coefficient_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    0 ≤
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        (alignedSmithGenuineFirstWall P a b hwall)
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) := by
  by_cases hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0
  · have hcoeffWall :
      alignedSmithCoefficientWallStep P d ∈
        alignedSmithCoefficientWalls P :=
      alignedSmithCoefficientWallStep_mem
        P hd hneg
    have hglobalWall :
      alignedSmithCoefficientWallStep P d ∈
        alignedSmithGenuineWalls P a b := by
      simp [alignedSmithGenuineWalls, hcoeffWall]
    have hle :=
      alignedSmithGenuineFirstWall_le_of_mem
        P a b hwall hglobalWall
    rcases
        smithSeparatorDelta_one_one_negative_cases
          (smithAxisProjection d) hneg with
      h4 | h2
    · rw [h4]
      apply
        alignedSmithCoefficientValue_neg_four_nonnegative
      unfold alignedSmithCoefficientWallStep at hle
      simpa [h4] using hle
    · rw [h2]
      apply
        alignedSmithCoefficientValue_neg_two_nonnegative
      unfold alignedSmithCoefficientWallStep at hle
      have hne4 :
          smithSeparatorDelta 1 1
              (smithAxisProjection d) ≠ -4 := by
        omega
      simpa [hne4, h2] using hle
  · have hnonneg :
      0 ≤ smithSeparatorDelta 1 1
        (smithAxisProjection d) := by
      omega
    exact
      alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
        (smithFamilyCoefficientOrder P d)
        (alignedSmithGenuineFirstWall P a b hwall)
        _
        hnonneg

/-- Every nonzero transverse coordinate of either marked section remains
integral up to the genuine first wall. -/
theorem alignedSmithGenuineFirstWall_section_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (c : Fin 4 → Polynomial K)
    (hc : c = a ∨ c = b)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hine : c i ≠ 0) :
    if i = 3 then
      0 ≤
        alignedSmithSectionValueFour
          (sectionCoordinateParameterOrder (c i))
          (alignedSmithGenuineFirstWall P a b hwall)
    else
      0 ≤
        alignedSmithSectionValueTwo
          (sectionCoordinateParameterOrder (c i))
          (alignedSmithGenuineFirstWall P a b hwall) := by
  have hsectionWall :
      alignedSmithSectionWallStep i (c i) ∈
        alignedSmithSectionWalls c :=
    alignedSmithSectionWallStep_mem
      c hi0 hine
  have hglobalWall :
      alignedSmithSectionWallStep i (c i) ∈
        alignedSmithGenuineWalls P a b := by
    rcases hc with rfl | rfl
    · simp [alignedSmithGenuineWalls, hsectionWall]
    · simp [alignedSmithGenuineWalls, hsectionWall]
  have hle :=
    alignedSmithGenuineFirstWall_le_of_mem
      P a b hwall hglobalWall
  by_cases hi3 : i = 3
  · subst i
    simp only [if_pos rfl]
    apply alignedSmithSectionValueFour_nonnegative
    unfold alignedSmithSectionWallStep at hle
    simpa using hle
  · simp only [hi3]
    apply alignedSmithSectionValueTwo_nonnegative
    unfold alignedSmithSectionWallStep at hle
    simpa [hi3] using hle

/-- Exact coefficient divisibility at the genuine first wall. -/
theorem alignedSmithGenuineFirstWall_integralCoefficients
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    HasIntegralSmithConformalCoefficientDivisibility
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P) := by
  apply alignedSmith_coefficientDivisibility_of_nonnegative
  intro d hd
  exact
    alignedSmithGenuineFirstWall_coefficient_nonnegative
      P a b hwall hd

/-- Left-section divisibility at the genuine first wall. -/
theorem alignedSmithGenuineFirstWall_integralSection_left
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    HasIntegralSmithConformalSectionDivisibility
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex a) := by
  apply alignedSmith_sectionDivisibility_of_nonnegative
  intro i hi0 hine
  exact
    alignedSmithGenuineFirstWall_section_nonnegative
      P a b hwall a (Or.inl rfl) hi0 hine

/-- Right-section divisibility at the genuine first wall. -/
theorem alignedSmithGenuineFirstWall_integralSection_right
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    HasIntegralSmithConformalSectionDivisibility
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (2 * alignedSmithGenuineFirstWall P a b hwall)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex b) := by
  apply alignedSmith_sectionDivisibility_of_nonnegative
  intro i hi0 hine
  exact
    alignedSmithGenuineFirstWall_section_nonnegative
      P a b hwall b (Or.inr rfl) hi0 hine

/-! ## Genuine-wall transformed family and marked sections -/

noncomputable def alignedSmithGenuineFirstWallFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  let N := alignedSmithGenuineFirstWall P a b hwall
  integralSmithConformalFamily
    (2 * N) (2 * N)
    (parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P)
    (alignedSmithGenuineFirstWall_integralCoefficients
      P a b hwall)

noncomputable def alignedSmithGenuineFirstWallSectionLeft
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    Fin 4 → Polynomial K :=
  let N := alignedSmithGenuineFirstWall P a b hwall
  integralSmithConformalSection
    (2 * N) (2 * N)
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex a)
    (alignedSmithGenuineFirstWall_integralSection_left
      P a b hwall)

noncomputable def alignedSmithGenuineFirstWallSectionRight
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    Fin 4 → Polynomial K :=
  let N := alignedSmithGenuineFirstWall P a b hwall
  integralSmithConformalSection
    (2 * N) (2 * N)
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex b)
    (alignedSmithGenuineFirstWall_integralSection_right
      P a b hwall)

/-- Pure Hessian defect survives on the single ramified scale. -/
theorem alignedSmithGenuineFirstWall_preservesHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (alignedSmithGenuineFirstWallFamily
        P a b hwall)
      (alignedSmithRamificationIndex * Delta) := by
  let N := alignedSmithGenuineFirstWall P a b hwall
  have hram :
      HasPolynomialFamilyHessianDefect
        (K := K)
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex P)
        (alignedSmithRamificationIndex * Delta) :=
    parameterRamificationFamily_hasHessianDefect
      alignedSmithRamificationIndex Delta P hdef
  unfold alignedSmithGenuineFirstWallFamily
  dsimp only
  exact
    integralSmithConformalFamily_preservesHessianDefect
      (2 * N) (2 * N)
      (alignedSmithRamificationIndex * Delta)
      (parameterRamificationFamily
        (K := K) alignedSmithRamificationIndex P)
      (alignedSmithGenuineFirstWall_integralCoefficients
        P a b hwall)
      hram

/-- Exact moving gradient collision survives to the genuine wall. -/
theorem alignedSmithGenuineFirstWall_preservesExactCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (alignedSmithGenuineFirstWallFamily
        P a b hwall)
      (alignedSmithGenuineFirstWallSectionLeft
        P a b hwall)
      (alignedSmithGenuineFirstWallSectionRight
        P a b hwall) := by
  let N := alignedSmithGenuineFirstWall P a b hwall
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let aram :=
    parameterRamificationSection
      (K := K) alignedSmithRamificationIndex a
  let bram :=
    parameterRamificationSection
      (K := K) alignedSmithRamificationIndex b
  have hramColl :
      HasPolynomialFamilyExactGradientCollision
        Pram aram bram := by
    dsimp [Pram, aram, bram]
    exact
      polynomialFamilyExactGradientCollision_parameterRamification
        alignedSmithRamificationIndex
        P a b hcoll
  unfold alignedSmithGenuineFirstWallFamily
  unfold alignedSmithGenuineFirstWallSectionLeft
  unfold alignedSmithGenuineFirstWallSectionRight
  dsimp only
  exact
    polynomialFamilyExactGradientCollision_integralSmithConformal
      (2 * N) (2 * N)
      Pram
      (alignedSmithGenuineFirstWall_integralCoefficients
        P a b hwall)
      aram bram
      (alignedSmithGenuineFirstWall_integralSection_left
        P a b hwall)
      (alignedSmithGenuineFirstWall_integralSection_right
        P a b hwall)
      hramColl

/-! ## No genuine wall: exact structural consequences -/

/-- If there is no genuine wall, no source coefficient has negative
symmetric Smith derivative. -/
theorem no_negativeSmithDerivative_of_noGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    ∀ d ∈ P.support,
      0 ≤
        smithSeparatorDelta 1 1
          (smithAxisProjection d) := by
  intro d hd
  by_contra hnot
  have hneg :
      smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0 := by
    omega
  have hcoeff :
      alignedSmithCoefficientWallStep P d ∈
        alignedSmithCoefficientWalls P :=
    alignedSmithCoefficientWallStep_mem
      P hd hneg
  apply hnone
  refine
    ⟨alignedSmithCoefficientWallStep P d, ?_⟩
  simp [alignedSmithGenuineWalls, hcoeff]

/-- If there is no genuine wall, every transverse coordinate of the left
moving section is the zero polynomial. -/
theorem leftTransverse_zero_of_noGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    ∀ i : Fin 4,
      i ≠ 0 →
        a i = 0 := by
  intro i hi0
  by_contra hine
  have hsection :
      alignedSmithSectionWallStep i (a i) ∈
        alignedSmithSectionWalls a :=
    alignedSmithSectionWallStep_mem
      a hi0 hine
  apply hnone
  refine
    ⟨alignedSmithSectionWallStep i (a i), ?_⟩
  simp [alignedSmithGenuineWalls, hsection]

/-- If there is no genuine wall, every transverse coordinate of the right
moving section is the zero polynomial. -/
theorem rightTransverse_zero_of_noGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    ∀ i : Fin 4,
      i ≠ 0 →
        b i = 0 := by
  intro i hi0
  by_contra hine
  have hsection :
      alignedSmithSectionWallStep i (b i) ∈
        alignedSmithSectionWalls b :=
    alignedSmithSectionWallStep_mem
      b hi0 hine
  apply hnone
  refine
    ⟨alignedSmithSectionWallStep i (b i), ?_⟩
  simp [alignedSmithGenuineWalls, hsection]

/-! ## General common-factor defect budget -/

/-- **Four-variable common-factor budget.**

If every coefficient of a four-variable potential contains `X^n` and its
Hessian determinant is exactly `X^Delta`, then

    4*n <= Delta.

Phase 93.61 proved the case `n=1`.  The general form is what lets an
arbitrarily long no-wall Smith motion contradict a fixed defect. -/
theorem four_mul_le_defect_of_commonParameterFactor
    (n : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    4 * n ≤ Delta := by
  let Q :=
    commonParameterFactorFamily n P hdiv
  have hfactor :
      P =
        MvPolynomial.C (Polynomial.X ^ n) * Q :=
    commonParameterFactorFamily_factorisation
      n P hdiv
  have hdet :=
    congrArg HC4.Polynomial.hessianDeterminant
      hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef] at hdet
  have hdvdMv :
      (MvPolynomial.C
          (Polynomial.X ^ (4 * n)) :
          MvPolynomial (Fin 4) (Polynomial K)) ∣
        MvPolynomial.C
          (Polynomial.X ^ Delta) := by
    refine
      ⟨HC4.Polynomial.hessianDeterminant Q, ?_⟩
    simpa [MvPolynomial.C_pow, ← pow_mul,
      Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hdet
  have hdvdPoly :
      (Polynomial.X ^ (4 * n) : Polynomial K) ∣
        Polynomial.X ^ Delta := by
    have hall :=
      (MvPolynomial.C_dvd_iff_dvd_coeff
        (Polynomial.X ^ (4 * n))
        (MvPolynomial.C
          (Polynomial.X ^ Delta) :
          MvPolynomial (Fin 4) (Polynomial K))).mp
        hdvdMv
    simpa only [MvPolynomial.coeff_zero_C] using
      (hall (0 : Fin 4 →₀ ℕ))
  rcases hdvdPoly with ⟨R, hR⟩
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hR
    exact
      (pow_ne_zero Delta Polynomial.X_ne_zero)
        hR
  have hX :
      (Polynomial.X ^ (4 * n) : Polynomial K) ≠ 0 :=
    pow_ne_zero (4 * n) Polynomial.X_ne_zero
  have hdeg :
      Delta = 4 * n + R.natDegree := by
    calc
      Delta =
          (Polynomial.X ^ Delta :
            Polynomial K).natDegree := by
              simp
      _ =
          ((Polynomial.X ^ (4 * n) :
            Polynomial K) * R).natDegree := by
              rw [hR]
      _ =
          (Polynomial.X ^ (4 * n) :
            Polynomial K).natDegree +
              R.natDegree := by
                exact
                  Polynomial.natDegree_mul
                    hX hRne
      _ = 4 * n + R.natDegree := by simp
  omega

/-! ## Cancelling arbitrary parameter-power margins -/

/-- If `X^(n+m)` divides `X^n*q`, then `X^m` divides `q`. -/
theorem polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
    (n m : ℕ)
    (q : Polynomial K)
    (h :
      Polynomial.X ^ (n + m) ∣
        Polynomial.X ^ n * q) :
    Polynomial.X ^ m ∣ q := by
  rcases h with ⟨r, hr⟩
  have heq :
      Polynomial.X ^ n * q =
        Polynomial.X ^ n *
          (Polynomial.X ^ m * r) := by
    calc
      Polynomial.X ^ n * q =
          Polynomial.X ^ (n + m) * r := hr
      _ =
          Polynomial.X ^ n *
            (Polynomial.X ^ m * r) := by
              rw [pow_add]
              ring
  have hcancel :=
    polynomial_X_pow_mul_cancel
      (K := K) n heq
  exact ⟨r, hcancel⟩

/-! ## Strictly positive derivative family gains a large common factor -/

/-- If every supported symmetric Smith derivative is at least two, then
after ramification by twenty and `N` integer symmetric steps, the normalised
family has the common factor `X^(2*N)`. -/
theorem alignedSmith_commonFactor_two_mul_of_delta_ge_two
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (N : ℕ)
    (hdelta :
      ∀ d ∈ P.support,
        (2 : ℤ) ≤
          smithSeparatorDelta 1 1
            (smithAxisProjection d)) :
    let Pram :=
      parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P
    let hsmith :
      HasIntegralSmithConformalCoefficientDivisibility
        (2 * N) (2 * N) Pram :=
      alignedSmith_coefficientDivisibility_of_nonnegative
        (K := K) P N
        (by
          intro d hd
          have hd2 := hdelta d hd
          exact
            alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
              (smithFamilyCoefficientOrder P d)
              N
              _
              (by omega))
    let Q :=
      integralSmithConformalFamily
        (2 * N) (2 * N) Pram hsmith
    HasCommonParameterFactor (2 * N) Q := by
  dsimp
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :
      HasIntegralSmithConformalCoefficientDivisibility
        (2 * N) (2 * N) Pram :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N
      (by
        intro d hd
        have hd2 := hdelta d hd
        exact
          alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
            (smithFamilyCoefficientOrder P d)
            N
            _
            (by omega))
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  intro d hdQ
  have hdRam :
      d ∈ Pram.support :=
    support_integralSmithConformalFamily_subset
      (2 * N) (2 * N) Pram hsmith hdQ
  have hdP :
      d ∈ P.support := by
    dsimp [Pram] at hdRam
    exact
      (MvPolynomial.support_map_subset
        (parameterRamificationHom
          (K := K) alignedSmithRamificationIndex)
        P)
        hdRam
  let v := smithFamilyCoefficientOrder P d
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_dvd P hdP
  have hramdiv :
      Polynomial.X ^
          (alignedSmithRamificationIndex * v) ∣
        MvPolynomial.coeff d Pram := by
    dsimp [Pram]
    unfold parameterRamificationFamily
    rw [MvPolynomial.coeff_map]
    exact
      parameterRamification_pow_dvd
        (K := K)
        alignedSmithRamificationIndex
        v
        (MvPolynomial.coeff d P)
        hvdiv
  have hfactor :=
    smithConformalCoefficientFactor_two_mul
      (K := K) N d
  have htotal :
      Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) ∣
        smithConformalCoefficientFactor
            (K := K) (2 * N) (2 * N) d *
          MvPolynomial.coeff d Pram := by
    rcases hramdiv with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [hfactor, hr]
    calc
      Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d) *
          (Polynomial.X ^
              (alignedSmithRamificationIndex * v) *
            r) =
        (Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d) *
          Polynomial.X ^
            (alignedSmithRamificationIndex * v)) *
          r := by ring
      _ =
        Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d +
              alignedSmithRamificationIndex * v) *
          r := by rw [← pow_add]
  have hdeltaRaw :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  have hd2 := hdelta d hdP
  have hmargin :
      4 * N + 2 * N ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex * v := by
    have hz :
        (6 : ℤ) * (N : ℤ) ≤
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (20 : ℤ) * (v : ℤ) := by
      rw [hdeltaRaw] at hd2
      have hNv :
          (0 : ℤ) ≤ (20 : ℤ) * (v : ℤ) := by
        positivity
      nlinarith
    have hsum :
        4 * N + 2 * N = 6 * N := by
      omega
    rw [hsum]
    norm_num [alignedSmithRamificationIndex] at ⊢
    exact_mod_cast hz
  have hsmall :
      (Polynomial.X ^ (4 * N + 2 * N) :
          Polynomial K) ∣
        Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hmargin
  have hbig :
      (Polynomial.X ^ (4 * N + 2 * N) :
          Polynomial K) ∣
        smithConformalCoefficientFactor
            (K := K) (2 * N) (2 * N) d *
          MvPolynomial.coeff d Pram :=
    dvd_trans hsmall htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam
  have hquotRaw :
      (Polynomial.X ^ (4 * N + 2 * N) :
          Polynomial K) ∣
        smithConformalMultiplier (2 * N) (2 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    rw [← hspec]
    exact hbig
  have hquot :
      (Polynomial.X ^ (4 * N + 2 * N) :
          Polynomial K) ∣
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent_two_mul] using hquotRaw
  have hmarginQuot :
      Polynomial.X ^ (2 * N) ∣
        smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d := by
    exact
      polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
        (K := K)
        (4 * N) (2 * N)
        (smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d)
        hquot
  rw [coeff_integralSmithConformalFamily_of_mem
    (2 * N) (2 * N) Pram hsmith hdRam]
  exact hmarginQuot

/-! ## No-wall endpoint must contain a zero Smith grade -/

/-- A nonnegative even symmetric Smith derivative which is not zero is at
least two. -/
theorem smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
    (e : SmithSupportExponent)
    (hnonneg :
      0 ≤ smithSeparatorDelta 1 1 e)
    (hne :
      smithSeparatorDelta 1 1 e ≠ 0) :
    (2 : ℤ) ≤ smithSeparatorDelta 1 1 e := by
  rcases smithSeparatorDelta_one_one_even e with
    ⟨z, hz⟩
  rw [hz] at hnonneg hne ⊢
  omega

/-- **No genuine wall forces a zero-grade source monomial.**

This is the defect-budget closure of the infinite Smith-ray possibility.
-/
theorem exists_zeroSmithDerivative_of_noGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    ∃ d ∈ P.support,
      smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0 := by
  by_contra hzero
  have hnonneg :=
    no_negativeSmithDerivative_of_noGenuineWall
      P a b hnone
  have hdelta2 :
      ∀ d ∈ P.support,
        (2 : ℤ) ≤
          smithSeparatorDelta 1 1
            (smithAxisProjection d) := by
    intro d hd
    have hne :
        smithSeparatorDelta 1 1
            (smithAxisProjection d) ≠ 0 := by
      intro hz
      apply hzero
      exact ⟨d, hd, hz⟩
    exact
      smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
        (smithAxisProjection d)
        (hnonneg d hd)
        hne
  let N := 3 * Delta + 1
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :
      HasIntegralSmithConformalCoefficientDivisibility
        (2 * N) (2 * N) Pram :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N
      (by
        intro d hd
        exact
          alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
            (smithFamilyCoefficientOrder P d)
            N
            _
            (by
              have := hdelta2 d hd
              omega))
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  have hcommon :
      HasCommonParameterFactor (2 * N) Q := by
    dsimp [Q, Pram, hsmith]
    exact
      alignedSmith_commonFactor_two_mul_of_delta_ge_two
        (K := K) P N hdelta2
  have hramDef :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Pram]
    exact
      parameterRamificationFamily_hasHessianDefect
        alignedSmithRamificationIndex Delta P hdef
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      integralSmithConformalFamily_preservesHessianDefect
        (2 * N) (2 * N)
        (alignedSmithRamificationIndex * Delta)
        Pram hsmith hramDef
  have hbudget :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K)
      (2 * N) Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQdef
  dsimp [N] at hbudget
  norm_num [alignedSmithRamificationIndex] at hbudget
  omega

/-! ## Final scale-safe endpoint dichotomy -/

/-- **Scale-safe aligned Smith endpoint dichotomy.**

Either there is a genuine first wall, and it is an actual coefficient or
left/right section wall, or there are no walls at all; in the latter case
the moving sections are exactly axial and a source monomial of Smith
derivative zero exists.

No artificial cap remains in this statement. -/
theorem alignedSmith_genuineEndpoint_dichotomy
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    (∃ hwall : HasAlignedSmithGenuineWall P a b,
        alignedSmithGenuineFirstWall P a b hwall ∈
            alignedSmithCoefficientWalls P ∨
          alignedSmithGenuineFirstWall P a b hwall ∈
            alignedSmithSectionWalls a ∨
          alignedSmithGenuineFirstWall P a b hwall ∈
            alignedSmithSectionWalls b) ∨
      ((∀ i : Fin 4, i ≠ 0 → a i = 0) ∧
        (∀ i : Fin 4, i ≠ 0 → b i = 0) ∧
        ∃ d ∈ P.support,
          smithSeparatorDelta 1 1
            (smithAxisProjection d) = 0) := by
  classical
  by_cases hwall :
      HasAlignedSmithGenuineWall P a b
  · left
    exact
      ⟨hwall,
        alignedSmithGenuineFirstWall_cases
          P a b hwall⟩
  · right
    exact
      ⟨leftTransverse_zero_of_noGenuineWall
          P a b hwall,
        rightTransverse_zero_of_noGenuineWall
          P a b hwall,
        exists_zeroSmithDerivative_of_noGenuineWall
          P a b Delta hdef hwall⟩

end

end HC4.Valuation
