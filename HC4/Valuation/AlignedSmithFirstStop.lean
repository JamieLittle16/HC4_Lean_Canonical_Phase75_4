import HC4.Valuation.AlignedSmithWallArithmetic
import Mathlib.Tactic

/-!
# Finite aligned Smith first-stop selection

Phase 93.66 puts all coefficient and marked-section walls for the canonical
symmetric Smith direction on one natural-number lattice after the single
base change

    tau = s^20.

This file performs the finite selection.

For a genuine Rees family `P` and moving marked sections `a,b` we build:

* a finite set of negative-coefficient walls;
* finite section-wall sets for `a` and `b`;
* an explicit finite search cap;
* the first stop `N_*`, defined as the minimum of the cap together with all
  actual walls.

We then prove that `N_*` lies no later than every genuine wall.  Therefore
all coefficient orders and all marked-section orders remain nonnegative at
`N_*`.

The arithmetic legality is converted back into the exact Phase 93.59
divisibility predicates.  Consequently the actual integral Smith family
with parameters `(2*N_*,2*N_*)` and the two transformed moving sections are
constructed, and both the pure Hessian defect and exact gradient collision
are transported to them.

The endpoint is finite and explicit:

    N_* = cap

or `N_*` belongs to one of the three genuine wall sets.

Thus the next phase only has to interpret a wall/cap endpoint; it no longer
needs to reconstruct the Smith transformation or prove its integrality.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Total exact coefficient order on source exponents -/

/-- Exact parameter order of a source coefficient, returning zero away from
the support. -/
noncomputable def smithFamilyCoefficientOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ := by
  classical
  exact
    if hd : d ∈ P.support then
      smithFamilyCoefficientParameterOrder P d hd
    else
      0

theorem smithFamilyCoefficientOrder_eq
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    smithFamilyCoefficientOrder P d =
      smithFamilyCoefficientParameterOrder P d hd := by
  classical
  unfold smithFamilyCoefficientOrder
  simp [hd]

theorem smithFamilyCoefficientOrder_dvd
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    Polynomial.X ^ (smithFamilyCoefficientOrder P d) ∣
      MvPolynomial.coeff d P := by
  rw [smithFamilyCoefficientOrder_eq P hd]
  exact
    smithFamilyCoefficientParameterOrder_dvd
      P d hd

/-! ## Finite coefficient-wall set -/

/-- Source exponents whose symmetric Smith derivative is negative. -/
noncomputable def negativeSmithSourceSupport
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset (Fin 4 →₀ ℕ) := by
  classical
  exact
    P.support.filter
      (fun d =>
        smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0)

/-- Aligned wall step of a negative-derivative source coefficient. -/
def alignedSmithCoefficientWallStep
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ :=
  if smithSeparatorDelta 1 1
        (smithAxisProjection d) = -4 then
    5 * smithFamilyCoefficientOrder P d
  else
    10 * smithFamilyCoefficientOrder P d

/-- Finite set of all genuine negative-coefficient walls. -/
noncomputable def alignedSmithCoefficientWalls
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset ℕ := by
  classical
  exact
    (negativeSmithSourceSupport P).image
      (alignedSmithCoefficientWallStep P)

theorem mem_negativeSmithSourceSupport
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ} :
    d ∈ negativeSmithSourceSupport P ↔
      d ∈ P.support ∧
        smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0 := by
  classical
  simp [negativeSmithSourceSupport]

/-- Every negative source coefficient contributes its exact aligned wall. -/
theorem alignedSmithCoefficientWallStep_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0) :
    alignedSmithCoefficientWallStep P d ∈
      alignedSmithCoefficientWalls P := by
  classical
  unfold alignedSmithCoefficientWalls
  apply Finset.mem_image.mpr
  exact
    ⟨d,
      (mem_negativeSmithSourceSupport P).2
        ⟨hd, hneg⟩,
      rfl⟩

/-- The selected coefficient wall is the exact zero of the aligned order. -/
theorem alignedSmithCoefficientWallStep_value_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0) :
    alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        (alignedSmithCoefficientWallStep P d)
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) = 0 := by
  rcases
      smithSeparatorDelta_one_one_negative_cases
        (smithAxisProjection d) hneg with
    h4 | h2
  · unfold alignedSmithCoefficientWallStep
    rw [if_pos h4, h4]
    exact
      alignedSmithCoefficientValue_neg_four_wall
        (smithFamilyCoefficientOrder P d)
  · unfold alignedSmithCoefficientWallStep
    rw [if_neg (by omega), h2]
    exact
      alignedSmithCoefficientValue_neg_two_wall
        (smithFamilyCoefficientOrder P d)

/-! ## Section-wall sets -/

/-- Exact order of a nonzero moving-section coordinate, zero by convention
for the zero polynomial. -/
noncomputable def sectionCoordinateParameterOrder
    (c : Polynomial K) : ℕ := by
  classical
  exact
    if hc : c ≠ 0 then
      polynomialParameterOrder c hc
    else
      0

theorem sectionCoordinateParameterOrder_dvd
    (c : Polynomial K) :
    Polynomial.X ^ (sectionCoordinateParameterOrder c) ∣ c := by
  classical
  by_cases hc : c = 0
  · rw [hc]
    simp
  · unfold sectionCoordinateParameterOrder
    simp [hc]
    exact polynomialParameterOrder_dvd c hc

/-- Aligned wall step for a nonzero transverse section coordinate. -/
def alignedSmithSectionWallStep
    (i : Fin 4)
    (c : Polynomial K) : ℕ :=
  if i = 3 then
    5 * sectionCoordinateParameterOrder c
  else
    10 * sectionCoordinateParameterOrder c

/-- Genuine transverse coordinates of a section which are nonzero
polynomials. -/
noncomputable def nonzeroSmithTransverseCoordinates
    (a : Fin 4 → Polynomial K) :
    Finset (Fin 4) := by
  classical
  exact
    Finset.univ.filter
      (fun i =>
        i ≠ 0 ∧ a i ≠ 0)

/-- Finite section-wall set. -/
noncomputable def alignedSmithSectionWalls
    (a : Fin 4 → Polynomial K) :
    Finset ℕ := by
  classical
  exact
    (nonzeroSmithTransverseCoordinates a).image
      (fun i => alignedSmithSectionWallStep i (a i))

theorem mem_nonzeroSmithTransverseCoordinates
    (a : Fin 4 → Polynomial K)
    {i : Fin 4} :
    i ∈ nonzeroSmithTransverseCoordinates a ↔
      i ≠ 0 ∧ a i ≠ 0 := by
  classical
  simp [nonzeroSmithTransverseCoordinates]

theorem alignedSmithSectionWallStep_mem
    (a : Fin 4 → Polynomial K)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hine : a i ≠ 0) :
    alignedSmithSectionWallStep i (a i) ∈
      alignedSmithSectionWalls a := by
  classical
  unfold alignedSmithSectionWalls
  apply Finset.mem_image.mpr
  exact
    ⟨i,
      (mem_nonzeroSmithTransverseCoordinates a).2
        ⟨hi0, hine⟩,
      rfl⟩

/-! ## Finite first stop -/

/-- Explicit finite cap.  The endpoint interpretation can strengthen this
later; the selector itself only needs a finite sentinel. -/
def alignedSmithSearchCap
    (Delta : ℕ) : ℕ :=
  5 * Delta + 1

theorem alignedSmithSearchCap_pos
    (Delta : ℕ) :
    0 < alignedSmithSearchCap Delta := by
  unfold alignedSmithSearchCap
  omega

/-- All genuine walls, plus the finite sentinel cap. -/
noncomputable def alignedSmithStopCandidates
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    Finset ℕ :=
  insert
    (alignedSmithSearchCap Delta)
    (alignedSmithCoefficientWalls P ∪
      alignedSmithSectionWalls a ∪
      alignedSmithSectionWalls b)

/-- The first aligned stop. -/
noncomputable def alignedSmithFirstStop
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) : ℕ :=
  (alignedSmithStopCandidates P a b Delta).min'
    (by
      refine
        ⟨alignedSmithSearchCap Delta, ?_⟩
      simp [alignedSmithStopCandidates])

theorem alignedSmithFirstStop_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    alignedSmithFirstStop P a b Delta ∈
      alignedSmithStopCandidates P a b Delta := by
  unfold alignedSmithFirstStop
  exact
    Finset.min'_mem
      (alignedSmithStopCandidates P a b Delta)
      _

/-- The first stop is no later than any candidate. -/
theorem alignedSmithFirstStop_le_of_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    {N : ℕ}
    (hN :
      N ∈ alignedSmithStopCandidates P a b Delta) :
    alignedSmithFirstStop P a b Delta ≤ N := by
  unfold alignedSmithFirstStop
  exact
    Finset.min'_le
      (alignedSmithStopCandidates P a b Delta)
      N hN

theorem alignedSmithFirstStop_le_cap
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    alignedSmithFirstStop P a b Delta ≤
      alignedSmithSearchCap Delta := by
  apply
    alignedSmithFirstStop_le_of_mem
      P a b Delta
  simp [alignedSmithStopCandidates]

/-- Endpoint split: either the sentinel cap is first, or a genuine
coefficient/section wall is first. -/
theorem alignedSmithFirstStop_cap_or_wall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    alignedSmithFirstStop P a b Delta =
        alignedSmithSearchCap Delta ∨
      alignedSmithFirstStop P a b Delta ∈
        alignedSmithCoefficientWalls P ∪
          alignedSmithSectionWalls a ∪
          alignedSmithSectionWalls b := by
  have hmem :=
    alignedSmithFirstStop_mem P a b Delta
  simpa [alignedSmithStopCandidates] using hmem

/-! ## Arithmetic legality at the selected stop -/

/-- Every source coefficient has nonnegative aligned order at the first
stop. -/
theorem alignedSmithFirstStop_coefficient_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    0 ≤
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        (alignedSmithFirstStop P a b Delta)
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) := by
  by_cases hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0
  · have hwall :=
      alignedSmithCoefficientWallStep_mem
        P hd hneg
    have hwallCandidate :
        alignedSmithCoefficientWallStep P d ∈
          alignedSmithStopCandidates P a b Delta := by
      simp [alignedSmithStopCandidates, hwall]
    have hle :=
      alignedSmithFirstStop_le_of_mem
        P a b Delta hwallCandidate
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
        (alignedSmithFirstStop P a b Delta)
        _
        hnonneg

/-- Every nonzero transverse coordinate of either marked section remains
integral at the first stop. -/
theorem alignedSmithFirstStop_section_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (c : Fin 4 → Polynomial K)
    (hc :
      c = a ∨ c = b)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hine : c i ≠ 0) :
    if i = 3 then
      0 ≤
        alignedSmithSectionValueFour
          (sectionCoordinateParameterOrder (c i))
          (alignedSmithFirstStop P a b Delta)
    else
      0 ≤
        alignedSmithSectionValueTwo
          (sectionCoordinateParameterOrder (c i))
          (alignedSmithFirstStop P a b Delta) := by
  have hwall :
      alignedSmithSectionWallStep i (c i) ∈
        alignedSmithSectionWalls c :=
    alignedSmithSectionWallStep_mem
      c hi0 hine
  have hcandidate :
      alignedSmithSectionWallStep i (c i) ∈
        alignedSmithStopCandidates P a b Delta := by
    rcases hc with rfl | rfl
    · simp [alignedSmithStopCandidates, hwall]
    · simp [alignedSmithStopCandidates, hwall]
  have hle :=
    alignedSmithFirstStop_le_of_mem
      P a b Delta hcandidate
  by_cases hi3 : i = 3
  · simp only [hi3, if_pos]
    apply alignedSmithSectionValueFour_nonnegative
    unfold alignedSmithSectionWallStep at hle
    simpa [hi3] using hle
  · simp only [hi3, if_neg]
    apply alignedSmithSectionValueTwo_nonnegative
    unfold alignedSmithSectionWallStep at hle
    simpa [hi3] using hle

/-! ## Exponent identities for a selected multi-step Smith move -/

/-- Raw source exponent scales linearly in the integer Smith step. -/
theorem smithConformalRawExponent_two_mul
    (N : ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithConformalRawExponent (2 * N) (2 * N) d =
      N * smithConformalRawExponent 2 2 d := by
  unfold smithConformalRawExponent
  ring

/-- Multiplier exponent at step `N` is `4*N`. -/
theorem smithConformalMultiplierExponent_two_mul
    (N : ℕ) :
    smithConformalMultiplierExponent (2 * N) (2 * N) =
      4 * N := by
  unfold smithConformalMultiplierExponent
  omega

/-- The coefficient factor for the selected multi-step move is the
corresponding pure parameter power. -/
theorem smithConformalCoefficientFactor_two_mul
    (N : ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithConformalCoefficientFactor
        (K := K) (2 * N) (2 * N) d =
      Polynomial.X ^
        (N * smithConformalRawExponent 2 2 d) := by
  unfold smithConformalCoefficientFactor
  rw [Fin.prod_univ_four]
  simp only [
    smithConformalDerivativeCoefficient,
    smithConformalSourceExponent]
  simp
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [← pow_add, ← pow_add]
  congr 1
  unfold smithConformalRawExponent
  ring

/-- The projection derivative is raw exponent minus four. -/
theorem smithSeparatorDelta_projection_eq_raw_sub_four
    (d : Fin 4 →₀ ℕ) :
    smithSeparatorDelta 1 1
        (smithAxisProjection d) =
      (smithConformalRawExponent 2 2 d : ℤ) - 4 := by
  unfold smithSeparatorDelta
  rw [HC4.Newton.smithExtremeSeparator_one_one]
  have h :=
    smithConformalRawExponent_sub_multiplier_eq_gradeDot
      2 2 d
  simpa [smithAxisProjection,
    SmithSupportExponent.grade,
    smithConformalMultiplierExponent] using h.symm

/-! ## Arithmetic legality -> actual integral Smith transform -/

/-- Coefficient nonnegativity on the aligned scale gives the exact
coefficient divisibility required by Phase 93.59 after the single
ramification by twenty. -/
theorem alignedSmith_coefficientDivisibility_of_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (N : ℕ)
    (hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d))) :
    HasIntegralSmithConformalCoefficientDivisibility
      (2 * N) (2 * N)
      (parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P) := by
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  intro d hdRam
  have hdP :
      d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom
        (K := K) alignedSmithRamificationIndex)
      P) hdRam
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
  have hdelta :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  have hnonneg := hlegal d hdP
  have hpowLe :
      4 * N ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex * v := by
    unfold alignedSmithCoefficientValue at hnonneg
    rw [hdelta] at hnonneg
    change
      (0 : ℤ) ≤
        (20 : ℤ) * (v : ℤ) +
          (N : ℤ) *
            ((smithConformalRawExponent 2 2 d : ℤ) - 4)
      at hnonneg
    have hexpand :
        (20 : ℤ) * (v : ℤ) +
            (N : ℤ) *
              ((smithConformalRawExponent 2 2 d : ℤ) - 4) =
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (20 : ℤ) * (v : ℤ) -
            (4 : ℤ) * (N : ℤ) := by
      ring
    rw [hexpand] at hnonneg
    have hz :
        (4 : ℤ) * (N : ℤ) ≤
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (20 : ℤ) * (v : ℤ) := by
      omega
    norm_num [alignedSmithRamificationIndex] at ⊢
    exact_mod_cast hz
  have htotal :
      Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) ∣
        smithConformalCoefficientFactor
            (K := K) (2 * N) (2 * N) d *
          MvPolynomial.coeff d Pram := by
    rcases hramdiv with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [smithConformalCoefficientFactor_two_mul]
    rw [hr]
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
          r := by
            rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ (4 * N) : Polynomial K) ∣
        Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) (4 * N) _ hpowLe
  have hout :=
    dvd_trans hsmall htotal
  simpa [smithConformalMultiplier,
    smithConformalMultiplierExponent_two_mul] using hout

/-- Section-order legality gives the exact inverse-source divisibility
required by Phase 93.59. -/
theorem alignedSmith_sectionDivisibility_of_nonnegative
    (a : Fin 4 → Polynomial K)
    (N : ℕ)
    (hlegal :
      ∀ i : Fin 4,
        i ≠ 0 ->
        a i ≠ 0 ->
          if i = 3 then
            0 ≤
              alignedSmithSectionValueFour
                (sectionCoordinateParameterOrder (a i))
                N
          else
            0 ≤
              alignedSmithSectionValueTwo
                (sectionCoordinateParameterOrder (a i))
                N) :
    HasIntegralSmithConformalSectionDivisibility
      (2 * N) (2 * N)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex a) := by
  intro i
  fin_cases i
  · simp [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent]
  · by_cases hz : a 1 = 0
    · simp [hz, parameterRamificationSection]
    · have horder :=
        sectionCoordinateParameterOrder_dvd (a 1)
      have hram :=
        parameterRamification_pow_dvd
          (K := K)
          alignedSmithRamificationIndex
          (sectionCoordinateParameterOrder (a 1))
          (a 1) horder
      have hnonneg :=
        hlegal 1 (by decide) hz
      simp only [show (1 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          2 * N ≤
            alignedSmithRamificationIndex *
              sectionCoordinateParameterOrder (a 1) := by
        norm_num [alignedSmithRamificationIndex] at ⊢
        omega
      have hsmall :
          (Polynomial.X ^ (2 * N) : Polynomial K) ∣
            Polynomial.X ^
              (alignedSmithRamificationIndex *
                sectionCoordinateParameterOrder (a 1)) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection] using
        dvd_trans hsmall hram
  · by_cases hz : a 2 = 0
    · simp [hz, parameterRamificationSection]
    · have horder :=
        sectionCoordinateParameterOrder_dvd (a 2)
      have hram :=
        parameterRamification_pow_dvd
          (K := K)
          alignedSmithRamificationIndex
          (sectionCoordinateParameterOrder (a 2))
          (a 2) horder
      have hnonneg :=
        hlegal 2 (by decide) hz
      simp only [show (2 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          2 * N ≤
            alignedSmithRamificationIndex *
              sectionCoordinateParameterOrder (a 2) := by
        norm_num [alignedSmithRamificationIndex] at ⊢
        omega
      have hsmall :
          (Polynomial.X ^ (2 * N) : Polynomial K) ∣
            Polynomial.X ^
              (alignedSmithRamificationIndex *
                sectionCoordinateParameterOrder (a 2)) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection] using
        dvd_trans hsmall hram
  · by_cases hz : a 3 = 0
    · simp [hz, parameterRamificationSection]
    · have horder :=
        sectionCoordinateParameterOrder_dvd (a 3)
      have hram :=
        parameterRamification_pow_dvd
          (K := K)
          alignedSmithRamificationIndex
          (sectionCoordinateParameterOrder (a 3))
          (a 3) horder
      have hnonneg :=
        hlegal 3 (by decide) hz
      simp only [if_pos rfl] at hnonneg
      unfold alignedSmithSectionValueFour at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          4 * N ≤
            alignedSmithRamificationIndex *
              sectionCoordinateParameterOrder (a 3) := by
        norm_num [alignedSmithRamificationIndex] at ⊢
        omega
      have hsmall :
          (Polynomial.X ^ (4 * N) : Polynomial K) ∣
            Polynomial.X ^
              (alignedSmithRamificationIndex *
                sectionCoordinateParameterOrder (a 3)) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      have hout :=
        dvd_trans hsmall hram
      have hexp :
          2 * N + 2 * N = 4 * N := by
        omega
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection,
        hexp] using hout

/-! ## The actual selected family and collision datum -/

/-- Coefficient divisibility at the first stop. -/
theorem alignedSmithFirstStop_integralCoefficients
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    HasIntegralSmithConformalCoefficientDivisibility
      (2 * alignedSmithFirstStop P a b Delta)
      (2 * alignedSmithFirstStop P a b Delta)
      (parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P) := by
  apply alignedSmith_coefficientDivisibility_of_nonnegative
  intro d hd
  exact
    alignedSmithFirstStop_coefficient_nonnegative
      P a b Delta hd

/-- Section divisibility for the first marked section. -/
theorem alignedSmithFirstStop_integralSection_left
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    HasIntegralSmithConformalSectionDivisibility
      (2 * alignedSmithFirstStop P a b Delta)
      (2 * alignedSmithFirstStop P a b Delta)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex a) := by
  apply alignedSmith_sectionDivisibility_of_nonnegative
  intro i hi0 hine
  exact
    alignedSmithFirstStop_section_nonnegative
      P a b Delta a (Or.inl rfl) hi0 hine

/-- Section divisibility for the second marked section. -/
theorem alignedSmithFirstStop_integralSection_right
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    HasIntegralSmithConformalSectionDivisibility
      (2 * alignedSmithFirstStop P a b Delta)
      (2 * alignedSmithFirstStop P a b Delta)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex b) := by
  apply alignedSmith_sectionDivisibility_of_nonnegative
  intro i hi0 hine
  exact
    alignedSmithFirstStop_section_nonnegative
      P a b Delta b (Or.inr rfl) hi0 hine

/-- The selected aligned Smith family. -/
noncomputable def alignedSmithFirstStopFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  let N := alignedSmithFirstStop P a b Delta
  integralSmithConformalFamily
    (2 * N) (2 * N)
    (parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P)
    (alignedSmithFirstStop_integralCoefficients
      P a b Delta)

/-- First transformed marked section. -/
noncomputable def alignedSmithFirstStopSectionLeft
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    Fin 4 → Polynomial K :=
  let N := alignedSmithFirstStop P a b Delta
  integralSmithConformalSection
    (2 * N) (2 * N)
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex a)
    (alignedSmithFirstStop_integralSection_left
      P a b Delta)

/-- Second transformed marked section. -/
noncomputable def alignedSmithFirstStopSectionRight
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ) :
    Fin 4 → Polynomial K :=
  let N := alignedSmithFirstStop P a b Delta
  integralSmithConformalSection
    (2 * N) (2 * N)
    (parameterRamificationSection
      (K := K) alignedSmithRamificationIndex b)
    (alignedSmithFirstStop_integralSection_right
      P a b Delta)

/-- The selected family retains the pure Hessian defect on the single
ramified scale `20*Delta`. -/
theorem alignedSmithFirstStop_preservesHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (alignedSmithFirstStopFamily P a b Delta)
      (alignedSmithRamificationIndex * Delta) := by
  let N := alignedSmithFirstStop P a b Delta
  have hram :
      HasPolynomialFamilyHessianDefect
        (K := K)
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex P)
        (alignedSmithRamificationIndex * Delta) :=
    parameterRamificationFamily_hasHessianDefect
      alignedSmithRamificationIndex Delta P hdef
  unfold alignedSmithFirstStopFamily
  dsimp only
  exact
    integralSmithConformalFamily_preservesHessianDefect
      (2 * N) (2 * N)
      (alignedSmithRamificationIndex * Delta)
      (parameterRamificationFamily
        (K := K) alignedSmithRamificationIndex P)
      (alignedSmithFirstStop_integralCoefficients
        P a b Delta)
      hram

/-- Exact family-gradient collision survives the entire selected
ramification-plus-Smith move. -/
theorem alignedSmithFirstStop_preservesExactCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (alignedSmithFirstStopFamily P a b Delta)
      (alignedSmithFirstStopSectionLeft
        P a b Delta)
      (alignedSmithFirstStopSectionRight
        P a b Delta) := by
  let N := alignedSmithFirstStop P a b Delta
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
  unfold alignedSmithFirstStopFamily
  unfold alignedSmithFirstStopSectionLeft
  unfold alignedSmithFirstStopSectionRight
  dsimp only
  exact
    polynomialFamilyExactGradientCollision_integralSmithConformal
      (2 * N) (2 * N)
      Pram
      (alignedSmithFirstStop_integralCoefficients
        P a b Delta)
      aram bram
      (alignedSmithFirstStop_integralSection_left
        P a b Delta)
      (alignedSmithFirstStop_integralSection_right
        P a b Delta)
      hramColl

/-- **Selected aligned Smith package.**

The family and both moving points genuinely exist at the finite first stop,
the exact collision and pure Hessian defect survive, and the stop is either
the finite cap or an actual coefficient/section wall. -/
theorem alignedSmithFirstStop_package
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyHessianDefect
        (K := K)
        (alignedSmithFirstStopFamily P a b Delta)
        (alignedSmithRamificationIndex * Delta) ∧
      HasPolynomialFamilyExactGradientCollision
        (alignedSmithFirstStopFamily P a b Delta)
        (alignedSmithFirstStopSectionLeft P a b Delta)
        (alignedSmithFirstStopSectionRight P a b Delta) ∧
      (alignedSmithFirstStop P a b Delta =
          alignedSmithSearchCap Delta ∨
        alignedSmithFirstStop P a b Delta ∈
          alignedSmithCoefficientWalls P ∪
            alignedSmithSectionWalls a ∪
            alignedSmithSectionWalls b) := by
  exact
    ⟨alignedSmithFirstStop_preservesHessianDefect
        P a b Delta hdef,
      alignedSmithFirstStop_preservesExactCollision
        P a b Delta hcoll,
      alignedSmithFirstStop_cap_or_wall
        P a b Delta⟩

end

end HC4.Valuation
