import HC4.Valuation.PrimitiveSmithEndpoint
import HC4.Valuation.ZeroSlopeSmithDispatcher
import Mathlib.Tactic

/-!
# Separated Smith boundary closure

Phase 93.69 reduces the scale-safe zero-slope Smith endpoint to

* a coefficient wall;
* a marked-section wall;
* or a no-wall primitive symmetric-minimal family.

This file closes every *separated* endpoint.

The key observation is elementary but decisive.

Suppose the genuine first aligned wall is a section wall but is not a
coefficient wall.  Assume also that the original special fibre does not
already contain a primitive zero-Smith-grade coefficient.

Then every source coefficient has *strictly positive* residual parameter
order at the first section wall:

* negative Smith derivative: the first section wall is strictly before the
  coefficient's own wall;
* zero Smith derivative: zero residual would mean an order-zero primitive
  zero-grade coefficient, excluded by hypothesis;
* positive Smith derivative: the section wall occurs at a positive integer
  step, and the symmetric derivative is even, hence at least two.

Thus the entire first-wall family has a common factor `X`.  On the single
fixed ramified scale this gives the honest strict restart

    20*Delta -> 20*Delta - 4,

with the exact family-gradient collision preserved.

The other separated cases are local:

* an order-zero zero-grade source coefficient means the original special
  fibre is already symmetric minimal;
* a coefficient first wall with no simultaneous section wall has the
  canonical special points `0` and `e0`, so the green symmetric-minimal
  local classifier applies;
* the no-wall primitive family from Phase 93.69 also has canonical special
  points and enters the same classifier.

Consequently the complete zero-slope endpoint is now

    local repair/terminal
      OR
    strict fixed-scale defect restart
      OR
    coupled coefficient+section wall.

Only the final coupled wall remains geometric.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Order-zero zero-grade source coefficients -/

/-- A source monomial already survives on the original special fibre with
symmetric Smith derivative zero. -/
def HasPrimitiveZeroSmithSource
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∃ d : Fin 4 →₀ ℕ,
    d ∈ P.support ∧
    smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0 ∧
    smithFamilyCoefficientOrder P d = 0

/-- Exact parameter order zero means the source coefficient has nonzero
constant term. -/
theorem constantCoeff_ne_zero_of_smithFamilyCoefficientOrder_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (horder :
      smithFamilyCoefficientOrder P d = 0) :
    Polynomial.constantCoeff
      (MvPolynomial.coeff d P) ≠ 0 := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hparameter :
      polynomialParameterOrder c hc = 0 := by
    have hp :
        smithFamilyCoefficientParameterOrder P d hd = 0 :=
      (smithFamilyCoefficientOrder_eq P hd).symm.trans
        horder
    simpa [c, smithFamilyCoefficientParameterOrder] using hp
  have hnot :
      ¬ Polynomial.X ∣ c := by
    have hsucc :=
      polynomialParameterOrder_succ_not_dvd
        c hc
    rw [hparameter] at hsucc
    simpa using hsucc
  intro hzero
  apply hnot
  rw [Polynomial.X_dvd_iff]
  exact hzero

/-- A primitive zero-grade source coefficient puts an actual zero-grade
monomial on the original special fibre. -/
theorem primitiveZeroSmithSource_mem_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : HasPrimitiveZeroSmithSource P) :
    ∃ d ∈ (polynomialFamilySpecialFiber P).support,
      smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0 := by
  rcases hzero with
    ⟨d, hd, hdelta, horder⟩
  have hconst :=
    constantCoeff_ne_zero_of_smithFamilyCoefficientOrder_eq_zero
      P hd horder
  have hdSpecial :
      d ∈ (polynomialFamilySpecialFiber P).support :=
    (mem_polynomialFamilySpecialFiber_support_iff
      P d).2 ⟨hd, hconst⟩
  exact ⟨d, hdSpecial, hdelta⟩

/-- Hence an order-zero zero-grade source coefficient is already the
canonical symmetric-minimal special-fibre witness. -/
theorem primitiveZeroSmithSource_specialFiber_symmetricMinimal
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : HasPrimitiveZeroSmithSource P) :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P))
      0
      (fun _ => (0 : ℤ)) := by
  rcases
      primitiveZeroSmithSource_mem_specialFiber
        P hzero with
    ⟨d, hd, hdelta⟩
  refine ⟨smithAxisProjection d, ?_, ?_⟩
  · unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  · unfold smithIntegralSeparatorTilt
    unfold finiteIntegralRescaledTilt
    unfold smithRescaledOldMinimum
    simp [hdelta]

/-! ## Canonical transverse special-point facts -/

theorem specialPoint_zero_transverse_constantCoeff
    (a : Fin 4 → Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K))) :
    ∀ i : Fin 4, i ≠ 0 →
      Polynomial.constantCoeff (a i) = 0 := by
  intro i hi
  have h := congrFun ha i
  simpa [polynomialSectionSpecialPoint] using h

theorem specialPoint_axis_transverse_constantCoeff
    (b : Fin 4 → Polynomial K)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∀ i : Fin 4, i ≠ 0 →
      Polynomial.constantCoeff (b i) = 0 := by
  intro i hi
  have h := congrFun hb i
  simpa [polynomialSectionSpecialPoint,
    coordinateAxisPoint, hi] using h

/-! ## A genuine section wall has positive step under canonical points -/

/-- A nonzero transverse coordinate whose special value is zero has
strictly positive exact parameter order. -/
theorem sectionCoordinateParameterOrder_pos_of_constantCoeff_zero
    (c : Polynomial K)
    (hc : c ≠ 0)
    (hconst : Polynomial.constantCoeff c = 0) :
    0 < sectionCoordinateParameterOrder c := by
  have hXdvd : Polynomial.X ∣ c := by
    rw [Polynomial.X_dvd_iff]
    exact hconst
  have hpow :
      Polynomial.X ^ 1 ∣ c := by
    simpa using hXdvd
  have hle :=
    polynomial_X_pow_dvd_le_parameterOrder
      c hc 1 hpow
  unfold sectionCoordinateParameterOrder
  simp [hc]
  omega

/-- Any actual transverse section wall is at positive aligned step when
that section originally has zero transverse special coordinates. -/
theorem alignedSmithSectionWall_step_pos
    (c : Fin 4 → Polynomial K)
    (htrans :
      ∀ i : Fin 4, i ≠ 0 →
        Polynomial.constantCoeff (c i) = 0)
    {N : ℕ}
    (hN : N ∈ alignedSmithSectionWalls c) :
    0 < N := by
  rcases
      mem_alignedSmithSectionWalls_exists_coordinate
        c hN with
    ⟨i, hi0, hine, hstep⟩
  have hv :
      0 <
        sectionCoordinateParameterOrder (c i) :=
    sectionCoordinateParameterOrder_pos_of_constantCoeff_zero
      (c i) hine (htrans i hi0)
  unfold alignedSmithSectionWallStep at hstep
  by_cases hi3 : i = 3
  · rw [if_pos hi3] at hstep
    omega
  · rw [if_neg hi3] at hstep
    omega

/-! ## Strict residual coefficient order at a separated section wall -/

/-- If the genuine first wall is not a coefficient wall, it occurs strictly
before every negative-derivative coefficient wall. -/
theorem genuineFirstWall_lt_negativeCoefficientWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithCoefficientWalls P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0) :
    alignedSmithGenuineFirstWall P a b hwall <
      alignedSmithCoefficientWallStep P d := by
  have hmem :
      alignedSmithCoefficientWallStep P d ∈
        alignedSmithGenuineWalls P a b := by
    have hc :=
      alignedSmithCoefficientWallStep_mem
        P hd hneg
    simp [alignedSmithGenuineWalls, hc]
  have hle :=
    alignedSmithGenuineFirstWall_le_of_mem
      P a b hwall hmem
  have hne :
      alignedSmithGenuineFirstWall P a b hwall ≠
        alignedSmithCoefficientWallStep P d := by
    intro heq
    apply hnotCoeff
    rw [heq]
    exact
      alignedSmithCoefficientWallStep_mem
        P hd hneg
  omega

/-- At a separated positive section wall every coefficient numerator has
at least one parameter power beyond the Smith multiplier.

This is the arithmetic heart of the section-wall restart. -/
theorem separatedSectionWall_coefficient_margin_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hNpos :
      0 < alignedSmithGenuineFirstWall P a b hwall)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let N :=
      alignedSmithGenuineFirstWall P a b hwall
    4 * N + 1 ≤
      N * smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder P d := by
  dsimp
  have hrel :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  by_cases hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0
  · have hlt :=
      genuineFirstWall_lt_negativeCoefficientWall
        P a b hwall hnotCoeff hd hneg
    rcases
        smithSeparatorDelta_one_one_negative_cases
          (smithAxisProjection d) hneg with
      h4 | h2
    · have hraw :
          smithConformalRawExponent 2 2 d = 0 := by
        rw [h4] at hrel
        exact_mod_cast
          (by omega :
            (smithConformalRawExponent 2 2 d : ℤ) = 0)
      have hwallEq :
          alignedSmithCoefficientWallStep P d =
            5 * smithFamilyCoefficientOrder P d := by
        unfold alignedSmithCoefficientWallStep
        rw [if_pos h4]
      rw [hwallEq] at hlt
      rw [hraw]
      norm_num [alignedSmithRamificationIndex]
      omega
    · have hraw :
          smithConformalRawExponent 2 2 d = 2 := by
        rw [h2] at hrel
        exact_mod_cast
          (by omega :
            (smithConformalRawExponent 2 2 d : ℤ) = 2)
      have hne4 :
          smithSeparatorDelta 1 1
              (smithAxisProjection d) ≠ -4 := by
        omega
      have hwallEq :
          alignedSmithCoefficientWallStep P d =
            10 * smithFamilyCoefficientOrder P d := by
        unfold alignedSmithCoefficientWallStep
        rw [if_neg hne4]
      rw [hwallEq] at hlt
      rw [hraw]
      norm_num [alignedSmithRamificationIndex]
      omega
  · have hnonneg :
        0 ≤
          smithSeparatorDelta 1 1
            (smithAxisProjection d) := by
      omega
    by_cases hzero :
        smithSeparatorDelta 1 1
          (smithAxisProjection d) = 0
    · have hvpos :
          0 < smithFamilyCoefficientOrder P d := by
        by_contra hvnot
        have hvzero :
            smithFamilyCoefficientOrder P d = 0 := by
          omega
        apply hnoPrimitive
        exact ⟨d, hd, hzero, hvzero⟩
      have hraw :
          smithConformalRawExponent 2 2 d = 4 := by
        rw [hzero] at hrel
        exact_mod_cast
          (by omega :
            (smithConformalRawExponent 2 2 d : ℤ) = 4)
      rw [hraw]
      norm_num [alignedSmithRamificationIndex]
      omega
    · have hdelta2 :=
        smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
          (smithAxisProjection d)
          hnonneg hzero
      have hraw6 :
          6 ≤ smithConformalRawExponent 2 2 d := by
        rw [hrel] at hdelta2
        exact_mod_cast
          (by omega :
            (6 : ℤ) ≤
              (smithConformalRawExponent 2 2 d : ℤ))
      norm_num [alignedSmithRamificationIndex]
      nlinarith

/-! ## Separated section wall -> common factor -> strict restart -/

/-- If the first genuine wall is a section wall but not a coefficient wall,
and there was no primitive zero-grade source term to stop at initially,
the entire transformed family is divisible by `X`. -/
theorem separatedSectionWall_commonParameterFactor_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls a ∨
        alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasCommonParameterFactor 1
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall) := by
  let N :=
    alignedSmithGenuineFirstWall P a b hwall
  have hNpos : 0 < N := by
    rcases hsection with hA | hB
    · exact
        alignedSmithSectionWall_step_pos
          a
          (specialPoint_zero_transverse_constantCoeff
            a ha)
          hA
    · exact
        alignedSmithSectionWall_step_pos
          b
          (specialPoint_axis_transverse_constantCoeff
            b hb)
          hB
  have hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)) := by
    intro d hd
    dsimp [N]
    exact
      alignedSmithGenuineFirstWall_coefficient_nonnegative
        P a b hwall hd
  have hmargin :
      ∀ d ∈ P.support,
        4 * N + 1 ≤
          N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex *
              smithFamilyCoefficientOrder P d := by
    intro d hd
    exact
      separatedSectionWall_coefficient_margin_one
        P a b hwall hnotCoeff hnoPrimitive
        hNpos hd
  have hout :=
    alignedSmith_commonFactor_of_margin
      (K := K)
      P N 1 hlegal hmargin
  simpa [alignedSmithGenuineFirstWallFamily, N] using hout

/-- Fixed-scale strict restart package created by a separated section wall. -/
def HasSeparatedSectionWallStrictRestart
    (Delta : ℕ)
    (s : GlobalRestartState) : Prop :=
  ∃ t : GlobalRestartState,
    t.defect =
        alignedSmithRamificationIndex * Delta - 4 ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t

/-- **Separated section wall is an honest strict global restart.**

No fresh ramification occurs here.  The source state is already measured on
the once-ramified scale `20*Delta`. -/
theorem separatedSectionWall_exactCollision_and_strictRestart
    {s : GlobalRestartState}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls a ∨
        alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hs :
      s.defect =
        alignedSmithRamificationIndex * Delta)
    (newRepair : RepairState) :
    HasSeparatedSectionWallStrictRestart Delta s := by
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P a b hwall
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P a b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P a b hwall
  have hcommon :
      HasCommonParameterFactor 1 Q := by
    dsimp [Q]
    exact
      separatedSectionWall_commonParameterFactor_one
        P a b hwall hnotCoeff hnoPrimitive
        hsection ha hb
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWall_preservesHessianDefect
        P a b hwall Delta hdef
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q a' b' := by
    dsimp [Q, a', b']
    exact
      alignedSmithGenuineFirstWall_preservesExactCollision
        P a b hwall hcoll
  have hout :=
    commonParameterFactor_one_exactCollision_and_strictRestart
      (s := s)
      Q hcommon hQdef
      a' b' hQcoll hs newRepair
  let t : GlobalRestartState :=
    { defect :=
        alignedSmithRamificationIndex * Delta - 4
      repair := newRepair }
  refine ⟨t, rfl, ?_, ?_⟩
  · simpa [t] using hout.2.2.1
  · simpa [t] using hout.2.2.2

/-! ## Section integrality strictly before its wall -/

/-- Before the exact section wall, the transformed nonzero transverse
coordinate still has zero special value. -/
theorem alignedSmithSection_beforeWall_constantCoeff_zero
    (c : Fin 4 → Polynomial K)
    (N : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c))
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hine : c i ≠ 0)
    (hlt :
      N < alignedSmithSectionWallStep i (c i)) :
    Polynomial.constantCoeff
      (integralSmithConformalSection
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv i) = 0 := by
  let v := sectionCoordinateParameterOrder (c i)
  let sexp :=
    smithConformalSourceExponent (2 * N) (2 * N) i
  have hmargin :
      sexp + 1 ≤
        alignedSmithRamificationIndex * v := by
    fin_cases i
    · exact False.elim (hi0 rfl)
    · dsimp [sexp, v]
      simp [alignedSmithSectionWallStep,
        smithConformalSourceExponent,
        alignedSmithRamificationIndex] at hlt ⊢
      omega
    · dsimp [sexp, v]
      simp [alignedSmithSectionWallStep,
        smithConformalSourceExponent,
        alignedSmithRamificationIndex] at hlt ⊢
      omega
    · dsimp [sexp, v]
      simp [alignedSmithSectionWallStep,
        smithConformalSourceExponent,
        alignedSmithRamificationIndex] at hlt ⊢
      omega
  have hvdiv :=
    sectionCoordinateParameterOrder_dvd
      (c i)
  have hram :
      Polynomial.X ^
          (alignedSmithRamificationIndex * v) ∣
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c) i := by
    dsimp [v]
    unfold parameterRamificationSection
    exact
      parameterRamification_pow_dvd
        (K := K)
        alignedSmithRamificationIndex
        (sectionCoordinateParameterOrder (c i))
        (c i)
        hvdiv
  have hsmall :
      (Polynomial.X ^ (sexp + 1) :
          Polynomial K) ∣
        Polynomial.X ^
          (alignedSmithRamificationIndex * v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hmargin
  have hbig :=
    dvd_trans hsmall hram
  let q :=
    integralSmithConformalSection
      (2 * N) (2 * N)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex c)
      hdiv i
  have hinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K)
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv)
      i
  have hinflate' :
      Polynomial.X ^ sexp * q =
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c) i := by
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient,
      sexp, q] using hinflate
  have hbig' :
      (Polynomial.X ^ (sexp + 1) :
          Polynomial K) ∣
        Polynomial.X ^ sexp * q := by
    rw [hinflate']
    exact hbig
  have hXdiv :
      Polynomial.X ∣ q := by
    have hcancel :=
      polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
        (K := K)
        sexp 1 q
        (by
          simpa [Nat.add_comm] using hbig')
    simpa using hcancel
  rw [Polynomial.X_dvd_iff] at hXdiv
  change Polynomial.constantCoeff q = 0
  exact hXdiv

/-- If a transverse coordinate is identically zero, its integral Smith
quotient is also zero. -/
theorem alignedSmithSection_zeroCoordinate
    (c : Fin 4 → Polynomial K)
    (N : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c))
    {i : Fin 4}
    (hzero : c i = 0) :
    integralSmithConformalSection
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv i = 0 := by
  let sexp :=
    smithConformalSourceExponent (2 * N) (2 * N) i
  let q :=
    integralSmithConformalSection
      (2 * N) (2 * N)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex c)
      hdiv i
  have hinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K)
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv)
      i
  have hz :
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex c) i = 0 := by
    unfold parameterRamificationSection
    rw [hzero]
    simp
  have heq :
      Polynomial.X ^ sexp * q =
        Polynomial.X ^ sexp * 0 := by
    have hinflate' :
        Polynomial.X ^ sexp * q =
          (parameterRamificationSection
            (K := K)
            alignedSmithRamificationIndex c) i := by
      simpa [smithConformalInflateSection,
        smithConformalDerivativeCoefficient,
        sexp, q] using hinflate
    rw [hinflate', hz]
    simp
  have hcancel :=
    polynomial_X_pow_mul_cancel
      (K := K) sexp heq
  simpa [q] using hcancel

/-- Coordinate zero is unchanged at the level of special points by the
aligned ramification plus Smith move. -/
theorem alignedSmithSection_zeroCoordinate_constantCoeff
    (c : Fin 4 → Polynomial K)
    (N : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)) :
    Polynomial.constantCoeff
      (integralSmithConformalSection
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv 0) =
      Polynomial.constantCoeff (c 0) := by
  let q :=
    integralSmithConformalSection
      (2 * N) (2 * N)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex c)
      hdiv 0
  have hinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K)
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv)
      (0 : Fin 4)
  have hq :
      q =
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (c 0) := by
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient,
      smithConformalSourceExponent,
      parameterRamificationSection,
      q] using hinflate
  change Polynomial.constantCoeff q =
    Polynomial.constantCoeff (c 0)
  rw [hq]
  exact
    constantCoeff_parameterRamificationHom
      alignedSmithRamificationIndex
      alignedSmithRamificationIndex_pos
      (c 0)

/-- At the genuine first wall, if a given marked section does not itself
hit a section wall, all of its transverse transformed special coordinates
remain zero. -/
theorem genuineFirstWall_section_transverseSpecial_zero_of_notWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b c : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hc :
      c = a ∨ c = b)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * alignedSmithGenuineFirstWall P a b hwall)
        (2 * alignedSmithGenuineFirstWall P a b hwall)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c))
    (hnot :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls c)
    {i : Fin 4}
    (hi0 : i ≠ 0) :
    Polynomial.constantCoeff
      (integralSmithConformalSection
        (2 * alignedSmithGenuineFirstWall P a b hwall)
        (2 * alignedSmithGenuineFirstWall P a b hwall)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv i) = 0 := by
  let N :=
    alignedSmithGenuineFirstWall P a b hwall
  by_cases hine : c i = 0
  · rw [alignedSmithSection_zeroCoordinate
      c N hdiv hine]
    simp
  · have hsection :
        alignedSmithSectionWallStep i (c i) ∈
          alignedSmithSectionWalls c :=
      alignedSmithSectionWallStep_mem
        c hi0 hine
    have hglobal :
        alignedSmithSectionWallStep i (c i) ∈
          alignedSmithGenuineWalls P a b := by
      rcases hc with rfl | rfl
      · simp [alignedSmithGenuineWalls, hsection]
      · simp [alignedSmithGenuineWalls, hsection]
    have hle :=
      alignedSmithGenuineFirstWall_le_of_mem
        P a b hwall hglobal
    have hne :
        N ≠ alignedSmithSectionWallStep i (c i) := by
      intro heq
      apply hnot
      have heq' :
          alignedSmithGenuineFirstWall P a b hwall =
            alignedSmithSectionWallStep i (c i) := by
        simpa [N] using heq
      rw [heq']
      exact hsection
    have hlt :
        N < alignedSmithSectionWallStep i (c i) := by
      omega
    have hout :=
      alignedSmithSection_beforeWall_constantCoeff_zero
        c N hdiv hi0 hine hlt
    simpa [N] using hout

/-! ## Pure coefficient wall keeps the canonical collision points -/

/-- A coefficient wall with no simultaneous section wall retains the exact
canonical special points `0` and `e0`. -/
theorem pureCoefficientWall_specialPoints_canonical
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hnotA :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls a)
    (hnotB :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (alignedSmithGenuineFirstWallSectionLeft
          (K := K) P a b hwall) =
          (fun _ => (0 : K)) ∧
      polynomialSectionSpecialPoint
        (alignedSmithGenuineFirstWallSectionRight
          (K := K) P a b hwall) =
          coordinateAxisPoint (K := K) (0 : Fin 4) := by
  constructor
  · funext i
    fin_cases i
    · have h0 :=
        alignedSmithSection_zeroCoordinate_constantCoeff
          a
          (alignedSmithGenuineFirstWall P a b hwall)
          (alignedSmithGenuineFirstWall_integralSection_left
            P a b hwall)
      have ha0 := congrFun ha (0 : Fin 4)
      simpa [polynomialSectionSpecialPoint,
        alignedSmithGenuineFirstWallSectionLeft] using
        h0.trans ha0
    · exact
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b a hwall (Or.inl rfl)
          (alignedSmithGenuineFirstWall_integralSection_left
            P a b hwall)
          hnotA
          (i := (1 : Fin 4)) (by decide)
    · exact
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b a hwall (Or.inl rfl)
          (alignedSmithGenuineFirstWall_integralSection_left
            P a b hwall)
          hnotA
          (i := (2 : Fin 4)) (by decide)
    · exact
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b a hwall (Or.inl rfl)
          (alignedSmithGenuineFirstWall_integralSection_left
            P a b hwall)
          hnotA
          (i := (3 : Fin 4)) (by decide)
  · funext i
    fin_cases i
    · have h0 :=
        alignedSmithSection_zeroCoordinate_constantCoeff
          b
          (alignedSmithGenuineFirstWall P a b hwall)
          (alignedSmithGenuineFirstWall_integralSection_right
            P a b hwall)
      have hb0 := congrFun hb (0 : Fin 4)
      simpa [polynomialSectionSpecialPoint,
        alignedSmithGenuineFirstWallSectionRight,
        coordinateAxisPoint] using
        h0.trans hb0
    · have hz :=
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b b hwall (Or.inr rfl)
          (alignedSmithGenuineFirstWall_integralSection_right
            P a b hwall)
          hnotB
          (i := (1 : Fin 4)) (by decide)
      simpa [polynomialSectionSpecialPoint,
        alignedSmithGenuineFirstWallSectionRight,
        coordinateAxisPoint] using hz
    · have hz :=
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b b hwall (Or.inr rfl)
          (alignedSmithGenuineFirstWall_integralSection_right
            P a b hwall)
          hnotB
          (i := (2 : Fin 4)) (by decide)
      simpa [polynomialSectionSpecialPoint,
        alignedSmithGenuineFirstWallSectionRight,
        coordinateAxisPoint] using hz
    · have hz :=
        genuineFirstWall_section_transverseSpecial_zero_of_notWall
          P a b b hwall (Or.inr rfl)
          (alignedSmithGenuineFirstWall_integralSection_right
            P a b hwall)
          hnotB
          (i := (3 : Fin 4)) (by decide)
      simpa [polynomialSectionSpecialPoint,
        alignedSmithGenuineFirstWallSectionRight,
        coordinateAxisPoint] using hz

/-! ## Ready local Smith classifier packages -/

/-- We only need the existential local packet polynomial for final assembly. -/
def HasCanonicalSmithRepairOrTerminal
    (D complexity : ℕ) : Prop :=
  ∃ G : MvPolynomial (Fin 4) K,
    HasRepairOrTerminal
      (HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D G)
      (rankOneRepairState complexity)

/-- Any canonical symmetric-minimal family immediately supplies the
existential local repair/terminal package. -/
theorem canonicalSymmetricMinimal_hasRepairOrTerminal
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D : ℕ}
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity := by
  have hprojected :
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P)).Nonempty := by
    rcases hminimal with ⟨e, he, hle⟩
    exact ⟨e, he⟩
  refine
    ⟨canonicalSpecialFiberSmithPolynomial
        (polynomialFamilySpecialFiber P), ?_⟩
  exact
    symmetricMinimalSpecialFiber_hasRepairOrTerminal
      P a b hhom hD hprojected
      hcoll ha hb hminimal complexity

/-- Full-family source homogeneity passes through the genuine first-wall
family and then to its special fibre. -/
theorem genuineFirstWall_specialFiber_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    (polynomialFamilySpecialFiber
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall)).IsHomogeneous D := by
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  have hPram : Pram.IsHomogeneous D := by
    dsimp [Pram]
    exact hP.map _
  have hQ :
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall).IsHomogeneous D := by
    unfold alignedSmithGenuineFirstWallFamily
    dsimp only
    exact
      integralSmithConformalFamily_isHomogeneous
        Pram hPram
        (alignedSmithGenuineFirstWall_integralCoefficients
          P a b hwall)
  exact
    polynomialFamilySpecialFiber_isHomogeneous
      _ hQ

/-- A pure coefficient wall is completely closed by the green local Smith
classifier. -/
theorem pureCoefficientWall_hasRepairOrTerminal
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hcoeff :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P)
    (hnotA :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls a)
    (hnotB :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity := by
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P a b hwall
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P a b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P a b hwall
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D := by
    dsimp [Q]
    exact
      genuineFirstWall_specialFiber_isHomogeneous
        P hP a b hwall
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q a' b' := by
    dsimp [Q, a', b']
    exact
      alignedSmithGenuineFirstWall_preservesExactCollision
        P a b hwall hcoll
  have hpoints :=
    pureCoefficientWall_specialPoints_canonical
      P a b hwall hnotA hnotB ha hb
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber Q))
        0
        (fun _ => (0 : ℤ)) := by
    dsimp [Q]
    exact
      genuineCoefficientWall_specialFiber_symmetricMinimal
        P a b hwall hcoeff
  exact
    canonicalSymmetricMinimal_hasRepairOrTerminal
      Q a' b' hhom hD hQcoll
      (by simpa [a'] using hpoints.1)
      (by simpa [b'] using hpoints.2)
      hminimal complexity

/-! ## No-wall primitive family has canonical transformed points -/

/-- In the no-wall case, all transverse section polynomials vanish
identically; therefore the explicit Smith-transformed sections have the
same special points as the originals. -/
theorem alignedSmithSection_specialPoint_eq_of_transverse_zero
    (c : Fin 4 → Polynomial K)
    (htrans :
      ∀ i : Fin 4, i ≠ 0 → c i = 0)
    (N : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)) :
    polynomialSectionSpecialPoint
      (integralSmithConformalSection
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex c)
        hdiv) =
      polynomialSectionSpecialPoint c := by
  funext i
  fin_cases i
  · exact
      alignedSmithSection_zeroCoordinate_constantCoeff
        c N hdiv
  · have hz :=
      alignedSmithSection_zeroCoordinate
        c N hdiv
        (htrans (1 : Fin 4) (by decide))
    simp [polynomialSectionSpecialPoint, hz,
      htrans (1 : Fin 4) (by decide)]
  · have hz :=
      alignedSmithSection_zeroCoordinate
        c N hdiv
        (htrans (2 : Fin 4) (by decide))
    simp [polynomialSectionSpecialPoint, hz,
      htrans (2 : Fin 4) (by decide)]
  · have hz :=
      alignedSmithSection_zeroCoordinate
        c N hdiv
        (htrans (3 : Fin 4) (by decide))
    simp [polynomialSectionSpecialPoint, hz,
      htrans (3 : Fin 4) (by decide)]

/-- The no-wall primitive family carries an exact collision at explicit
sections whose special points are still `0` and `e0`. -/
theorem noWallPrimitiveSmithFamily_canonicalCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∃ a' b' : Fin 4 → Polynomial K,
      HasPolynomialFamilyExactGradientCollision
        (noWallPrimitiveSmithFamily
          P a b Delta hdef hnone)
        a' b' ∧
      polynomialSectionSpecialPoint a' =
        (fun _ => (0 : K)) ∧
      polynomialSectionSpecialPoint b' =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P a b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)) :=
    fun d hd =>
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone m hd
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  have hadiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex a) := by
    intro i
    fin_cases i
    · simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection]
    · have hz :=
        leftTransverse_zero_of_noGenuineWall
          P a b hnone (1 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz :=
        leftTransverse_zero_of_noGenuineWall
          P a b hnone (2 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz :=
        leftTransverse_zero_of_noGenuineWall
          P a b hnone (3 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
  have hbdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex b) := by
    intro i
    fin_cases i
    · simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection]
    · have hz :=
        rightTransverse_zero_of_noGenuineWall
          P a b hnone (1 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz :=
        rightTransverse_zero_of_noGenuineWall
          P a b hnone (2 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz :=
        rightTransverse_zero_of_noGenuineWall
          P a b hnone (3 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
  let aram :=
    parameterRamificationSection
      (K := K)
      alignedSmithRamificationIndex a
  let bram :=
    parameterRamificationSection
      (K := K)
      alignedSmithRamificationIndex b
  let a' :=
    integralSmithConformalSection
      (2 * N) (2 * N) aram hadiv
  let b' :=
    integralSmithConformalSection
      (2 * N) (2 * N) bram hbdiv
  have hramColl :
      HasPolynomialFamilyExactGradientCollision
        Pram aram bram := by
    dsimp [Pram, aram, bram]
    exact
      polynomialFamilyExactGradientCollision_parameterRamification
        alignedSmithRamificationIndex
        P a b hcoll
  have hsmithColl :
      HasPolynomialFamilyExactGradientCollision
        (integralSmithConformalFamily
          (2 * N) (2 * N) Pram hsmith)
        a' b' := by
    dsimp [a', b']
    exact
      polynomialFamilyExactGradientCollision_integralSmithConformal
        (2 * N) (2 * N)
        Pram hsmith
        aram bram hadiv hbdiv
        hramColl
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  have hfinal :
      HasPolynomialFamilyExactGradientCollision
        (commonParameterFactorFamily
          (alignedSmithRamificationIndex * m)
          Q hcommon)
        a' b' :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      (alignedSmithRamificationIndex * m)
      Q hcommon a' b' hsmithColl
  have haSpecial :
      polynomialSectionSpecialPoint a' =
        polynomialSectionSpecialPoint a := by
    dsimp [a', aram]
    exact
      alignedSmithSection_specialPoint_eq_of_transverse_zero
        a
        (leftTransverse_zero_of_noGenuineWall
          P a b hnone)
        N hadiv
  have hbSpecial :
      polynomialSectionSpecialPoint b' =
        polynomialSectionSpecialPoint b := by
    dsimp [b', bram]
    exact
      alignedSmithSection_specialPoint_eq_of_transverse_zero
        b
        (rightTransverse_zero_of_noGenuineWall
          P a b hnone)
        N hbdiv
  refine ⟨a', b', ?_, ?_, ?_⟩
  · simpa [noWallPrimitiveSmithFamily,
      hne, m, N, hlegal, Pram, hsmith, Q, hcommon] using
      hfinal
  · exact haSpecial.trans ha
  · exact hbSpecial.trans hb

/-- The no-wall endpoint is fully closed by the local Smith classifier. -/
theorem noWallPrimitiveSmithFamily_hasRepairOrTerminal
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity := by
  rcases
      noWallPrimitiveSmithFamily_canonicalCollision
        P a b Delta hdef hnone
        hcoll ha hb with
    ⟨a', b', hcoll', ha', hb'⟩
  have hhomFull :=
    noWallPrimitiveSmithFamily_isHomogeneous
      P hP a b Delta hdef hnone
  have hhom :=
    polynomialFamilySpecialFiber_isHomogeneous
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone)
      hhomFull
  have hminimal :=
    noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
      P a b Delta hdef hnone
  exact
    canonicalSymmetricMinimal_hasRepairOrTerminal
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone)
      a' b' hhom hD hcoll'
      ha' hb' hminimal complexity

/-! ## Coupled wall: the only residual boundary geometry -/

/-- A coupled aligned Smith wall is a genuine first wall at which a
potential coefficient and at least one marked section hit zero residual
order simultaneously. -/
def HasCoupledAlignedSmithWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K) : Prop :=
  ∃ hwall : HasAlignedSmithGenuineWall P a b,
    alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P ∧
      (alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls a ∨
       alignedSmithGenuineFirstWall P a b hwall ∈
          alignedSmithSectionWalls b)

/-- Exact finite arithmetic carried by a coupled wall.

The coefficient derivative is `-4` or `-2`, while the marked section wall
is one of the weight-two (`y,z`) or weight-four (`w`) walls. -/
theorem coupledAlignedSmithWall_finiteArithmetic
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoupled :
      HasCoupledAlignedSmithWall P a b) :
    ∃ hwall : HasAlignedSmithGenuineWall P a b,
      ∃ d : Fin 4 →₀ ℕ,
        d ∈ P.support ∧
        (smithSeparatorDelta 1 1
            (smithAxisProjection d) = -4 ∨
         smithSeparatorDelta 1 1
            (smithAxisProjection d) = -2) ∧
        ∃ c : Fin 4 → Polynomial K,
          (c = a ∨ c = b) ∧
          ∃ i : Fin 4,
            i ≠ 0 ∧
            c i ≠ 0 ∧
            alignedSmithCoefficientWallStep P d =
              alignedSmithSectionWallStep i (c i) ∧
            alignedSmithGenuineFirstWall P a b hwall =
              alignedSmithCoefficientWallStep P d := by
  rcases hcoupled with
    ⟨hwall, hcoeff, hsection⟩
  rcases
      mem_alignedSmithCoefficientWalls_exists_source
        P hcoeff with
    ⟨d, hd, hneg, hcoeffStep⟩
  have hdeltaCases :=
    smithSeparatorDelta_one_one_negative_cases
      (smithAxisProjection d) hneg
  rcases hsection with hA | hB
  · rcases
        mem_alignedSmithSectionWalls_exists_coordinate
          a hA with
      ⟨i, hi0, hine, hsectionStep⟩
    refine
      ⟨hwall, d, hd, hdeltaCases,
        a, Or.inl rfl, i, hi0, hine, ?_, ?_⟩
    · calc
        alignedSmithCoefficientWallStep P d =
          alignedSmithGenuineFirstWall P a b hwall :=
            hcoeffStep
        _ =
          alignedSmithSectionWallStep i (a i) :=
            hsectionStep.symm
    · exact hcoeffStep.symm
  · rcases
        mem_alignedSmithSectionWalls_exists_coordinate
          b hB with
      ⟨i, hi0, hine, hsectionStep⟩
    refine
      ⟨hwall, d, hd, hdeltaCases,
        b, Or.inr rfl, i, hi0, hine, ?_, ?_⟩
    · calc
        alignedSmithCoefficientWallStep P d =
          alignedSmithGenuineFirstWall P a b hwall :=
            hcoeffStep
        _ =
          alignedSmithSectionWallStep i (b i) :=
            hsectionStep.symm
    · exact hcoeffStep.symm

/-! ## Headline separated-boundary dispatcher -/

/-- **Zero-slope aligned Smith endpoint after closing all separated walls.**

Assume the genuine family is source-homogeneous, carries the canonical
marked collision, and the global state is already measured on the one
fixed ramified scale.

Then exactly the outcomes needed by final assembly remain:

1. local Smith repair/terminal;
2. strict defect restart `20*Delta -> 20*Delta-4`;
3. a coupled coefficient+section wall.

There is no free section-boundary branch anymore. -/
theorem alignedSmith_separatedBoundaryDispatcher
    [CharZero K]
    {s : GlobalRestartState}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hs :
      s.defect =
        alignedSmithRamificationIndex * Delta)
    (complexity : ℕ)
    (newRepair : RepairState) :
    HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity ∨
      HasSeparatedSectionWallStrictRestart Delta s ∨
      HasCoupledAlignedSmithWall P a b := by
  classical
  by_cases hprimitive :
      HasPrimitiveZeroSmithSource P
  · left
    have hhom :=
      polynomialFamilySpecialFiber_isHomogeneous
        P hP
    have hminimal :=
      primitiveZeroSmithSource_specialFiber_symmetricMinimal
        P hprimitive
    exact
      canonicalSymmetricMinimal_hasRepairOrTerminal
        P a b hhom hD hcoll
        ha hb hminimal complexity
  · by_cases hwall :
      HasAlignedSmithGenuineWall P a b
    · let N :=
        alignedSmithGenuineFirstWall P a b hwall
      by_cases hcoeff :
          N ∈ alignedSmithCoefficientWalls P
      · by_cases hA :
          N ∈ alignedSmithSectionWalls a
        · right
          right
          exact
            ⟨hwall, hcoeff, Or.inl hA⟩
        · by_cases hB :
            N ∈ alignedSmithSectionWalls b
          · right
            right
            exact
              ⟨hwall, hcoeff, Or.inr hB⟩
          · left
            exact
              pureCoefficientWall_hasRepairOrTerminal
                P hP a b hwall
                (by simpa [N] using hcoeff)
                (by simpa [N] using hA)
                (by simpa [N] using hB)
                hD hcoll ha hb complexity
      · right
        left
        have hcases :=
          alignedSmithGenuineFirstWall_cases
            P a b hwall
        have hsection :
            N ∈ alignedSmithSectionWalls a ∨
              N ∈ alignedSmithSectionWalls b := by
          rcases hcases with hc | hA | hB
          · exact False.elim (hcoeff (by simpa [N] using hc))
          · exact Or.inl (by simpa [N] using hA)
          · exact Or.inr (by simpa [N] using hB)
        exact
          separatedSectionWall_exactCollision_and_strictRestart
            (s := s)
            P a b hwall
            (by simpa [N] using hcoeff)
            hprimitive
            (by simpa [N] using hsection)
            hdef hcoll ha hb hs newRepair
    · left
      exact
        noWallPrimitiveSmithFamily_hasRepairOrTerminal
          P hP a b Delta hdef hwall
          hD hcoll ha hb complexity

end

end HC4.Valuation
