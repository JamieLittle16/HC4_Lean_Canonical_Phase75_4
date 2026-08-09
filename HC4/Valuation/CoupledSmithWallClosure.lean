import HC4.Valuation.SeparatedSmithBoundaryClosure
import Mathlib.Tactic

/-!
# Coupled aligned Smith wall closure

Phase 93.70 closes every separated Smith endpoint.  Its only residual
alternative is a *coupled wall*: the same genuine first aligned Smith step
is simultaneously

* a coefficient wall, and
* a wall of at least one marked transverse section coordinate.

This file proves that the coupled wall is impossible in the nonprimitive
branch in which it can actually arise.

The argument is finite and very rigid.

Let `N > 0` be the coupled first wall and let `F` be the special fibre of
the once-ramified, Smith-normalised first-wall family.  A monomial of `F`
must have aligned residual coefficient order exactly zero.

If the original source has no order-zero, zero-Smith-grade coefficient,
then every monomial surviving in `F` has *negative* symmetric Smith
derivative:

* positive derivative gives strictly positive residual order because
  `N > 0`;
* derivative zero and residual zero force original coefficient order zero,
  which is the excluded primitive-zero branch.

The symmetric derivative has only the values `-4` and `-2` when negative.
Under ordinary degree-`D` homogeneity those are exactly the three low
blockers

    x^D,
    x^(D-1) y,
    x^(D-1) z.

Thus the whole first-wall special fibre has the exact form

    A x^D + B x^(D-1) y + C x^(D-1) z.

The Smith transformation does not alter the longitudinal (`x = 0`)
coordinate of the marked sections.  Their special-fibre x-coordinates are
therefore still `0` and `1`.

Exact gradient collision now kills the model immediately:

* the `y`-gradient gives `B = 0`;
* the `z`-gradient gives `C = 0`;
* the `x`-gradient gives `A = 0`.

Hence the special fibre is zero, contradicting the coefficient wall,
which already supplies a surviving monomial.

The final theorem removes the coupled alternative from Phase 93.70:

    local repair/terminal
      OR
    strict fixed-scale defect restart.

This is the closed zero-slope Smith endpoint dispatcher intended for final
assembly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Surviving first-wall coefficients have residual order zero -/

/-- Any support monomial of the genuine first-wall special fibre comes from
the original source support. -/
theorem genuineFirstWall_specialFiber_source_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    {d : Fin 4 →₀ ℕ}
    (hdF :
      d ∈
        (polynomialFamilySpecialFiber
          (alignedSmithGenuineFirstWallFamily
            (K := K) P a b hwall)).support) :
    d ∈ P.support := by
  let N :=
    alignedSmithGenuineFirstWall P a b hwall
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmithGenuineFirstWall_integralCoefficients
      (K := K) P a b hwall
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  have hdQ :
      d ∈ Q.support := by
    have hdata :=
      (mem_polynomialFamilySpecialFiber_support_iff
        (alignedSmithGenuineFirstWallFamily
          (K := K) P a b hwall) d).1 hdF
    simpa [alignedSmithGenuineFirstWallFamily,
      N, Pram, hsmith, Q] using hdata.1
  have hdRam :
      d ∈ Pram.support :=
    support_integralSmithConformalFamily_subset
      (2 * N) (2 * N) Pram hsmith hdQ
  dsimp [Pram] at hdRam
  exact
    (MvPolynomial.support_map_subset
      (parameterRamificationHom
        (K := K) alignedSmithRamificationIndex)
      P)
      hdRam

/-- If an integral aligned Smith coefficient has strictly positive residual
order, its transformed coefficient is divisible by `X`. -/
theorem genuineFirstWall_coefficient_X_dvd_of_positiveResidual
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hpos :
      0 <
        alignedSmithCoefficientValue
          (smithFamilyCoefficientOrder P d)
          (alignedSmithGenuineFirstWall P a b hwall)
          (smithSeparatorDelta 1 1
            (smithAxisProjection d))) :
    Polynomial.X ∣
      MvPolynomial.coeff d
        (alignedSmithGenuineFirstWallFamily
          (K := K) P a b hwall) := by
  let N :=
    alignedSmithGenuineFirstWall P a b hwall
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmithGenuineFirstWall_integralCoefficients
      (K := K) P a b hwall
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Pram]
    exact
      mem_parameterRamificationFamily_support_of_mem
        P hd
  let v := smithFamilyCoefficientOrder P d
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact
      smithFamilyCoefficientOrder_dvd P hd
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
              (alignedSmithRamificationIndex * v) * r) =
        (Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d) *
          Polynomial.X ^
            (alignedSmithRamificationIndex * v)) * r := by
              ring
      _ =
        Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d +
              alignedSmithRamificationIndex * v) * r := by
                rw [← pow_add]
  have hrel :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  have hmargin :
      4 * N + 1 ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex * v := by
    have hpos' := hpos
    change
      0 <
        alignedSmithCoefficientValue
          v N
          (smithSeparatorDelta 1 1
            (smithAxisProjection d))
      at hpos'
    unfold alignedSmithCoefficientValue at hpos'
    rw [hrel] at hpos'
    have hidentity :
        (alignedSmithRamificationIndex : ℤ) * (v : ℤ) +
            (N : ℤ) *
              ((smithConformalRawExponent 2 2 d : ℤ) - 4) =
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) * (v : ℤ) -
            4 * (N : ℤ) := by
      ring
    rw [hidentity] at hpos'
    have hzInt :
        (4 : ℤ) * (N : ℤ) + 1 ≤
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) * (v : ℤ) := by
      omega
    have hz :
        (4 * N + 1 : ℕ) ≤
          N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v := by
      norm_num [alignedSmithRamificationIndex] at hzInt ⊢
      exact_mod_cast hzInt
    exact hz
  have hsmall :
      (Polynomial.X ^ (4 * N + 1) :
          Polynomial K) ∣
        Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hmargin
  have hbig :
      (Polynomial.X ^ (4 * N + 1) :
          Polynomial K) ∣
        smithConformalCoefficientFactor
            (K := K) (2 * N) (2 * N) d *
          MvPolynomial.coeff d Pram :=
    dvd_trans hsmall htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam
  have hquotRaw :
      (Polynomial.X ^ (4 * N + 1) :
          Polynomial K) ∣
        smithConformalMultiplier
            (K := K) (2 * N) (2 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    rw [← hspec]
    exact hbig
  have hquot :
      (Polynomial.X ^ (4 * N + 1) :
          Polynomial K) ∣
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent_two_mul] using
      hquotRaw
  have hX :
      Polynomial.X ∣
        smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d := by
    have hout :=
      polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
        (K := K)
        (4 * N) 1
        (smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d)
        hquot
    simpa using hout
  have hcoeff :
      MvPolynomial.coeff d Q =
        smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d := by
    exact
      coeff_integralSmithConformalFamily_of_mem
        (2 * N) (2 * N) Pram hsmith hdRam
  unfold alignedSmithGenuineFirstWallFamily
  dsimp only
  rw [hcoeff]
  exact hX

/-- Every coefficient that actually survives on the first-wall special fibre
has aligned residual order exactly zero. -/
theorem genuineFirstWall_specialFiber_residual_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    {d : Fin 4 →₀ ℕ}
    (hdF :
      d ∈
        (polynomialFamilySpecialFiber
          (alignedSmithGenuineFirstWallFamily
            (K := K) P a b hwall)).support) :
    alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        (alignedSmithGenuineFirstWall P a b hwall)
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) = 0 := by
  have hdP :=
    genuineFirstWall_specialFiber_source_mem
      P a b hwall hdF
  have hnonneg :=
    alignedSmithGenuineFirstWall_coefficient_nonnegative
      P a b hwall hdP
  by_contra hne
  have hpos :
      0 <
        alignedSmithCoefficientValue
          (smithFamilyCoefficientOrder P d)
          (alignedSmithGenuineFirstWall P a b hwall)
          (smithSeparatorDelta 1 1
            (smithAxisProjection d)) := by
    omega
  have hX :=
    genuineFirstWall_coefficient_X_dvd_of_positiveResidual
      P a b hwall hdP hpos
  have hdata :=
    (mem_polynomialFamilySpecialFiber_support_iff
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall) d).1 hdF
  have hconst := hdata.2
  rw [Polynomial.X_dvd_iff] at hX
  exact hconst hX

/-! ## Positive first wall + no primitive zero grade => negative support -/

/-- In the nonprimitive branch, every monomial surviving at a positive
genuine first wall has negative symmetric Smith derivative. -/
theorem genuineFirstWall_specialFiber_negativeSmith_of_noPrimitive
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hNpos :
      0 < alignedSmithGenuineFirstWall P a b hwall)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    {d : Fin 4 →₀ ℕ}
    (hdF :
      d ∈
        (polynomialFamilySpecialFiber
          (alignedSmithGenuineFirstWallFamily
            (K := K) P a b hwall)).support) :
    smithSeparatorDelta 1 1
      (smithAxisProjection d) < 0 := by
  have hdP :=
    genuineFirstWall_specialFiber_source_mem
      P a b hwall hdF
  have hzero :=
    genuineFirstWall_specialFiber_residual_zero
      P a b hwall hdF
  by_contra hnot
  have hnonneg :
      0 ≤
        smithSeparatorDelta 1 1
          (smithAxisProjection d) := by
    omega
  by_cases hdelta :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0
  · have hvzero :
        smithFamilyCoefficientOrder P d = 0 := by
      unfold alignedSmithCoefficientValue at hzero
      rw [hdelta] at hzero
      norm_num [alignedSmithRamificationIndex] at hzero
      omega
    exact
      hnoPrimitive
        ⟨d, hdP, hdelta, hvzero⟩
  · have hdpos :
        0 <
          smithSeparatorDelta 1 1
            (smithAxisProjection d) := by
      omega
    unfold alignedSmithCoefficientValue at hzero
    norm_num [alignedSmithRamificationIndex] at hzero
    have hterm :
        0 <
          (alignedSmithGenuineFirstWall P a b hwall : ℤ) *
            smithSeparatorDelta 1 1
              (smithAxisProjection d) := by
      exact mul_pos
        (by exact_mod_cast hNpos)
        hdpos
    have hvnonneg :
        0 ≤
          (20 : ℤ) *
            (smithFamilyCoefficientOrder P d : ℤ) := by
      positivity
    omega

/-! ## Negative Smith derivative is exactly one of three low patterns -/

/-- The only exponent patterns with negative symmetric Smith derivative are
the pure longitudinal blocker and the two linear transverse blockers. -/
theorem negativeSmithDerivative_lowPattern_cases
    (e : SmithSupportExponent)
    (hneg :
      smithSeparatorDelta 1 1 e < 0) :
    IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e := by
  have hformula :=
    smithSeparatorDelta_one_one_formula e
  rcases
      smithSeparatorDelta_one_one_negative_cases
        e hneg with
    h4 | h2
  · left
    unfold IsPureLongitudinalSmithPattern
    rw [h4] at hformula
    omega
  · rw [h2] at hformula
    have hd0 : e.d = 0 := by
      omega
    have hbc : e.b + e.c = 1 := by
      omega
    by_cases hb0 : e.b = 0
    · right
      left
      unfold IsLowNegativeFirstSmithPattern
      refine ⟨hb0, ?_, hd0⟩
      omega
    · right
      right
      unfold IsLowNegativeSecondSmithPattern
      refine ⟨?_, ?_, hd0⟩
      · omega
      · omega

/-! ## Homogeneous negative support reconstructs the three blockers -/

/-- A homogeneous Fin-4 support monomial with negative symmetric Smith
derivative is exactly `x^D`, `x^(D-1)y`, or `x^(D-1)z`. -/
theorem homogeneous_negativeSmith_support_cases
    (F : MvPolynomial (Fin 4) K)
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ F.support)
    (hneg :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0) :
    d = longitudinalAxisBlockerExponent (0 : Fin 4) D ∨
      d = transverseAxisBlockerExponent (0 : Fin 4) 1 D ∨
      d = transverseAxisBlockerExponent (0 : Fin 4) 2 D := by
  have hcoeff :
      MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdeg :
      (Finsupp.weight
        (fun _ : Fin 4 => 1)) d = D :=
    hhom hcoeff
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      d
  rw [hdecomp] at hdeg
  have htotal :
      d 0 + d 1 + d 2 + d 3 = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  rcases
      negativeSmithDerivative_lowPattern_cases
        (smithAxisProjection d) hneg with
    hpure | hfirst | hsecond
  · have h1 : d 1 = 0 := by
      exact hpure.1
    have h2 : d 2 = 0 := by
      exact hpure.2.1
    have h3 : d 3 = 0 := by
      exact hpure.2.2
    have h0 : d 0 = D := by
      omega
    left
    calc
      d =
          Finsupp.single 0 (d 0) +
          Finsupp.single 1 (d 1) +
          Finsupp.single 2 (d 2) +
          Finsupp.single 3 (d 3) := hdecomp
      _ =
          longitudinalAxisBlockerExponent
            (0 : Fin 4) D := by
        simp [h0, h1, h2, h3,
          longitudinalAxisBlockerExponent]
  · have h1 : d 1 = 0 := by
      exact hfirst.1
    have h2 : d 2 = 1 := by
      exact hfirst.2.1
    have h3 : d 3 = 0 := by
      exact hfirst.2.2
    have h0 : d 0 = D - 1 := by
      omega
    right
    right
    calc
      d =
          Finsupp.single 0 (d 0) +
          Finsupp.single 1 (d 1) +
          Finsupp.single 2 (d 2) +
          Finsupp.single 3 (d 3) := hdecomp
      _ =
          transverseAxisBlockerExponent
            (0 : Fin 4) 2 D := by
        simp [h0, h1, h2, h3,
          transverseAxisBlockerExponent, add_assoc]
  · have h1 : d 1 = 1 := by
      exact hsecond.1
    have h2 : d 2 = 0 := by
      exact hsecond.2.1
    have h3 : d 3 = 0 := by
      exact hsecond.2.2
    have h0 : d 0 = D - 1 := by
      omega
    right
    left
    calc
      d =
          Finsupp.single 0 (d 0) +
          Finsupp.single 1 (d 1) +
          Finsupp.single 2 (d 2) +
          Finsupp.single 3 (d 3) := hdecomp
      _ =
          transverseAxisBlockerExponent
            (0 : Fin 4) 1 D := by
        simp [h0, h1, h2, h3,
          transverseAxisBlockerExponent, add_assoc]

/-! ## Exact three-blocker normal form -/

/-- Support restriction to the three low blockers. -/
def HasCoupledLowBlockerSupport
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d : Fin 4 →₀ ℕ,
    MvPolynomial.coeff d F ≠ 0 →
      d = longitudinalAxisBlockerExponent
            (0 : Fin 4) D ∨
      d = transverseAxisBlockerExponent
            (0 : Fin 4) 1 D ∨
      d = transverseAxisBlockerExponent
            (0 : Fin 4) 2 D

noncomputable def coupledLowBlockerCoeffX
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) : K :=
  MvPolynomial.coeff
    (longitudinalAxisBlockerExponent
      (0 : Fin 4) D) F

noncomputable def coupledLowBlockerCoeffY
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) : K :=
  MvPolynomial.coeff
    (transverseAxisBlockerExponent
      (0 : Fin 4) 1 D) F

noncomputable def coupledLowBlockerCoeffZ
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) : K :=
  MvPolynomial.coeff
    (transverseAxisBlockerExponent
      (0 : Fin 4) 2 D) F

theorem coupledLongitudinal_ne_Y
    (D : ℕ) :
    longitudinalAxisBlockerExponent
        (0 : Fin 4) D ≠
      transverseAxisBlockerExponent
        (0 : Fin 4) 1 D := by
  intro h
  have h1 :=
    congrArg
      (fun d : Fin 4 →₀ ℕ => d (1 : Fin 4))
      h
  simp [longitudinalAxisBlockerExponent,
    transverseAxisBlockerExponent,
    finFour_zero_ne_one,
    Ne.symm finFour_zero_ne_one] at h1

theorem coupledLongitudinal_ne_Z
    (D : ℕ) :
    longitudinalAxisBlockerExponent
        (0 : Fin 4) D ≠
      transverseAxisBlockerExponent
        (0 : Fin 4) 2 D := by
  intro h
  have h2 :=
    congrArg
      (fun d : Fin 4 →₀ ℕ => d (2 : Fin 4))
      h
  simp [longitudinalAxisBlockerExponent,
    transverseAxisBlockerExponent,
    finFour_zero_ne_two,
    Ne.symm finFour_zero_ne_two] at h2

theorem coupledY_ne_Z
    (D : ℕ) :
    transverseAxisBlockerExponent
        (0 : Fin 4) 1 D ≠
      transverseAxisBlockerExponent
        (0 : Fin 4) 2 D := by
  intro h
  have h1 :=
    congrArg
      (fun d : Fin 4 →₀ ℕ => d (1 : Fin 4))
      h
  simp [transverseAxisBlockerExponent,
    finFour_zero_ne_one,
    finFour_zero_ne_two,
    finFour_one_ne_two,
    Ne.symm finFour_zero_ne_one,
    Ne.symm finFour_zero_ne_two,
    Ne.symm finFour_one_ne_two] at h1

/-- Three-monomial coefficient presentation of the coupled-wall fibre. -/
noncomputable def coupledLowBlockerMonomialModel
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.monomial
      (longitudinalAxisBlockerExponent
        (0 : Fin 4) D)
      (coupledLowBlockerCoeffX D F) +
    MvPolynomial.monomial
      (transverseAxisBlockerExponent
        (0 : Fin 4) 1 D)
      (coupledLowBlockerCoeffY D F) +
    MvPolynomial.monomial
      (transverseAxisBlockerExponent
        (0 : Fin 4) 2 D)
      (coupledLowBlockerCoeffZ D F)

/-- Support restriction reconstructs the whole coupled-wall fibre from its
three blocker coefficients. -/
theorem coupledLowBlocker_eq_monomialModel
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : HasCoupledLowBlockerSupport D F) :
    F = coupledLowBlockerMonomialModel D F := by
  classical
  apply MvPolynomial.ext
  intro d
  have hXY :=
    coupledLongitudinal_ne_Y D
  have hXZ :=
    coupledLongitudinal_ne_Z D
  have hYZ :=
    coupledY_ne_Z D
  by_cases hX :
      d =
        longitudinalAxisBlockerExponent
          (0 : Fin 4) D
  · subst d
    simp [coupledLowBlockerMonomialModel,
      coupledLowBlockerCoeffX,
      coupledLowBlockerCoeffY,
      coupledLowBlockerCoeffZ,
      hXY, hXZ, Ne.symm hXY, Ne.symm hXZ]
  · by_cases hY :
      d =
        transverseAxisBlockerExponent
          (0 : Fin 4) 1 D
    · subst d
      simp [coupledLowBlockerMonomialModel,
        coupledLowBlockerCoeffX,
        coupledLowBlockerCoeffY,
        coupledLowBlockerCoeffZ,
        hXY, hYZ, Ne.symm hXY, Ne.symm hYZ]
    · by_cases hZ :
        d =
          transverseAxisBlockerExponent
            (0 : Fin 4) 2 D
      · subst d
        simp [coupledLowBlockerMonomialModel,
          coupledLowBlockerCoeffX,
          coupledLowBlockerCoeffY,
          coupledLowBlockerCoeffZ,
          hXZ, hYZ, Ne.symm hXZ, Ne.symm hYZ]
      · have hzero :
          MvPolynomial.coeff d F = 0 := by
          by_contra hne
          rcases hsupp d hne with hx | hy | hz
          · exact hX hx
          · exact hY hy
          · exact hZ hz
        simp [coupledLowBlockerMonomialModel,
          hzero, hX, hY, hZ,
          Ne.symm hX, Ne.symm hY, Ne.symm hZ]

/-- Algebraic variable presentation of the same three-blocker fibre. -/
noncomputable def coupledLowBlockerAlgebraicModel
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.C (coupledLowBlockerCoeffX D F) *
      MvPolynomial.X (0 : Fin 4) ^ D +
    MvPolynomial.C (coupledLowBlockerCoeffY D F) *
      MvPolynomial.X (0 : Fin 4) ^ (D - 1) *
      MvPolynomial.X (1 : Fin 4) +
    MvPolynomial.C (coupledLowBlockerCoeffZ D F) *
      MvPolynomial.X (0 : Fin 4) ^ (D - 1) *
      MvPolynomial.X (2 : Fin 4)

/-- Monomial and algebraic blocker presentations agree. -/
theorem coupledLowBlockerMonomialModel_eq_algebraicModel
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    coupledLowBlockerMonomialModel D F =
      coupledLowBlockerAlgebraicModel D F := by
  unfold coupledLowBlockerMonomialModel
  unfold coupledLowBlockerAlgebraicModel
  simp only [longitudinalAxisBlockerExponent,
    transverseAxisBlockerExponent,
    MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial,
    pow_one]

/-- Exact algebraic normal form of every coupled low-blocker fibre. -/
theorem coupledLowBlocker_eq_algebraicModel
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : HasCoupledLowBlockerSupport D F) :
    F = coupledLowBlockerAlgebraicModel D F := by
  calc
    F = coupledLowBlockerMonomialModel D F :=
      coupledLowBlocker_eq_monomialModel hsupp
    _ = coupledLowBlockerAlgebraicModel D F :=
      coupledLowBlockerMonomialModel_eq_algebraicModel
        D F

/-! ## Gradient formulas for the three-blocker model -/

/-- The y-gradient depends only on the longitudinal coordinate. -/
theorem coupledLowBlocker_gradient_y_at
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : HasCoupledLowBlockerSupport D F)
    (point : Fin 4 → K) :
    mvGradientComponentAt point F (1 : Fin 4) =
      coupledLowBlockerCoeffY D F *
        point 0 ^ (D - 1) := by
  calc
    mvGradientComponentAt point F (1 : Fin 4) =
      mvGradientComponentAt point
        (coupledLowBlockerAlgebraicModel D F)
        (1 : Fin 4) := by
          exact congrArg
            (fun G : MvPolynomial (Fin 4) K =>
              mvGradientComponentAt point G (1 : Fin 4))
            (coupledLowBlocker_eq_algebraicModel
              hsupp)
    _ =
      coupledLowBlockerCoeffY D F *
        point 0 ^ (D - 1) := by
          unfold mvGradientComponentAt
          unfold coupledLowBlockerAlgebraicModel
          simp [finFour_zero_ne_one,
            finFour_zero_ne_two,
            finFour_one_ne_two,
            Ne.symm finFour_zero_ne_one,
            Ne.symm finFour_zero_ne_two,
            Ne.symm finFour_one_ne_two]

/-- The z-gradient depends only on the longitudinal coordinate. -/
theorem coupledLowBlocker_gradient_z_at
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : HasCoupledLowBlockerSupport D F)
    (point : Fin 4 → K) :
    mvGradientComponentAt point F (2 : Fin 4) =
      coupledLowBlockerCoeffZ D F *
        point 0 ^ (D - 1) := by
  calc
    mvGradientComponentAt point F (2 : Fin 4) =
      mvGradientComponentAt point
        (coupledLowBlockerAlgebraicModel D F)
        (2 : Fin 4) := by
          exact congrArg
            (fun G : MvPolynomial (Fin 4) K =>
              mvGradientComponentAt point G (2 : Fin 4))
            (coupledLowBlocker_eq_algebraicModel
              hsupp)
    _ =
      coupledLowBlockerCoeffZ D F *
        point 0 ^ (D - 1) := by
          unfold mvGradientComponentAt
          unfold coupledLowBlockerAlgebraicModel
          simp [-standardTwoZero_pderiv_two_eq_A,
            finFour_zero_ne_one,
            finFour_zero_ne_two,
            finFour_one_ne_two,
            Ne.symm finFour_zero_ne_one,
            Ne.symm finFour_zero_ne_two,
            Ne.symm finFour_one_ne_two]

/-- Once the two transverse blocker coefficients vanish, the x-gradient is
the pure longitudinal derivative. -/
theorem coupledLowBlocker_gradient_x_at_of_transverse_zero
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : HasCoupledLowBlockerSupport D F)
    (hY : coupledLowBlockerCoeffY D F = 0)
    (hZ : coupledLowBlockerCoeffZ D F = 0)
    (point : Fin 4 → K) :
    mvGradientComponentAt point F (0 : Fin 4) =
      (D : K) *
        coupledLowBlockerCoeffX D F *
        point 0 ^ (D - 1) := by
  calc
    mvGradientComponentAt point F (0 : Fin 4) =
      mvGradientComponentAt point
        (coupledLowBlockerAlgebraicModel D F)
        (0 : Fin 4) := by
          exact congrArg
            (fun G : MvPolynomial (Fin 4) K =>
              mvGradientComponentAt point G (0 : Fin 4))
            (coupledLowBlocker_eq_algebraicModel
              hsupp)
    _ =
      (D : K) *
        coupledLowBlockerCoeffX D F *
        point 0 ^ (D - 1) := by
          unfold mvGradientComponentAt
          unfold coupledLowBlockerAlgebraicModel
          rw [hY, hZ]
          simp
          ring_nf

/-- A degree-at-least-two three-blocker polynomial cannot have equal
gradients at points whose longitudinal coordinates are `0` and `1` unless
the polynomial is zero. -/
theorem coupledLowBlocker_exactCollision_forces_zero
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (F : MvPolynomial (Fin 4) K)
    (hsupp : HasCoupledLowBlockerSupport D F)
    (p q : Fin 4 → K)
    (hp0 : p 0 = 0)
    (hq0 : q 0 = 1)
    (hcoll :
      HasExactGradientCollision F p q) :
    F = 0 := by
  have hDm1 : D - 1 ≠ 0 := by
    omega
  have hy := hcoll (1 : Fin 4)
  rw [coupledLowBlocker_gradient_y_at hsupp p,
      coupledLowBlocker_gradient_y_at hsupp q,
      hp0, hq0] at hy
  simp [hDm1] at hy
  have hY :
      coupledLowBlockerCoeffY D F = 0 := by
    exact hy.symm
  have hz := hcoll (2 : Fin 4)
  rw [coupledLowBlocker_gradient_z_at hsupp p,
      coupledLowBlocker_gradient_z_at hsupp q,
      hp0, hq0] at hz
  simp [hDm1] at hz
  have hZ :
      coupledLowBlockerCoeffZ D F = 0 := by
    exact hz.symm
  have hx := hcoll (0 : Fin 4)
  rw [coupledLowBlocker_gradient_x_at_of_transverse_zero
        hsupp hY hZ p,
      coupledLowBlocker_gradient_x_at_of_transverse_zero
        hsupp hY hZ q,
      hp0, hq0] at hx
  simp [hDm1] at hx
  have hDnat : D ≠ 0 := by
    omega
  have hX :
      coupledLowBlockerCoeffX D F = 0 := by
    rcases hx with hDzero | hXzero
    · exact False.elim (hDnat hDzero)
    · exact hXzero
  rw [coupledLowBlocker_eq_algebraicModel hsupp]
  simp [coupledLowBlockerAlgebraicModel,
    hX, hY, hZ]

/-! ## The transformed marked longitudinal coordinates remain 0 and 1 -/

/-- The left first-wall marked point still has longitudinal coordinate zero. -/
theorem genuineFirstWall_leftSpecialPoint_zeroCoordinate
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K))) :
    polynomialSectionSpecialPoint
        (alignedSmithGenuineFirstWallSectionLeft
          (K := K) P a b hwall)
        (0 : Fin 4) = 0 := by
  have h0 :=
    alignedSmithSection_zeroCoordinate_constantCoeff
      a
      (alignedSmithGenuineFirstWall P a b hwall)
      (alignedSmithGenuineFirstWall_integralSection_left
        P a b hwall)
  have ha0 := congrFun ha (0 : Fin 4)
  simpa [polynomialSectionSpecialPoint,
    alignedSmithGenuineFirstWallSectionLeft] using
    h0.trans ha0

/-- The right first-wall marked point still has longitudinal coordinate one. -/
theorem genuineFirstWall_rightSpecialPoint_oneCoordinate
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (alignedSmithGenuineFirstWallSectionRight
          (K := K) P a b hwall)
        (0 : Fin 4) = 1 := by
  have h0 :=
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

/-! ## Coupled wall contradiction -/

/-- A coupled wall occurs at a strictly positive Smith step under the
canonical initial marked points. -/
theorem coupledAlignedSmithWall_firstWall_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
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
    0 < alignedSmithGenuineFirstWall P a b hwall := by
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

/-- **Coupled aligned Smith wall impossibility.**

In the nonprimitive branch the first-wall special fibre is forced onto the
three low blockers.  Its exact marked collision still has longitudinal
coordinates `0` and `1`, so the three-blocker gradient calculation forces
the fibre to vanish, contradicting the coefficient wall. -/
theorem coupledAlignedSmithWall_impossible_of_noPrimitive
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
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
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hcoupled :
      HasCoupledAlignedSmithWall P a b) :
    False := by
  rcases hcoupled with
    ⟨hwall, hcoeff, hsection⟩
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P a b hwall
  let F :=
    polynomialFamilySpecialFiber Q
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P a b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P a b hwall
  let p :=
    polynomialSectionSpecialPoint a'
  let q :=
    polynomialSectionSpecialPoint b'
  have hNpos :=
    coupledAlignedSmithWall_firstWall_pos
      P a b hwall hsection ha hb
  have hhomF :
      F.IsHomogeneous D := by
    dsimp [F, Q]
    exact
      genuineFirstWall_specialFiber_isHomogeneous
        P hP a b hwall
  have hsupp :
      HasCoupledLowBlockerSupport D F := by
    intro d hdcoeff
    have hdF : d ∈ F.support :=
      MvPolynomial.mem_support_iff.mpr hdcoeff
    have hneg :
        smithSeparatorDelta 1 1
          (smithAxisProjection d) < 0 := by
      dsimp [F, Q] at hdF
      exact
        genuineFirstWall_specialFiber_negativeSmith_of_noPrimitive
          P a b hwall hNpos hnoPrimitive hdF
    exact
      homogeneous_negativeSmith_support_cases
        F hhomF hdF hneg
  have hfamily :
      HasPolynomialFamilyExactGradientCollision
        Q a' b' := by
    dsimp [Q, a', b']
    exact
      alignedSmithGenuineFirstWall_preservesExactCollision
        P a b hwall hcoll
  have hspecial :
      HasExactGradientCollision F p q := by
    dsimp [F, p, q]
    exact
      polynomialFamilyExactGradientCollision_specialFiber
        Q a' b' hfamily
  have hp0 : p 0 = 0 := by
    dsimp [p, a']
    exact
      genuineFirstWall_leftSpecialPoint_zeroCoordinate
        P a b hwall ha
  have hq0 : q 0 = 1 := by
    dsimp [q, b']
    exact
      genuineFirstWall_rightSpecialPoint_oneCoordinate
        P a b hwall hb
  have hFzero :
      F = 0 :=
    coupledLowBlocker_exactCollision_forces_zero
      hD F hsupp p q hp0 hq0 hspecial
  have hsurvive :=
    genuineCoefficientWall_specialFiber_has_negativeGrade
      P a b hwall hcoeff
  rcases hsurvive with
    ⟨d, hdF, _hneg⟩
  dsimp [F, Q] at hFzero hdF
  rw [hFzero] at hdF
  simpa using hdF

/-! ## Closed zero-slope endpoint dispatcher -/

/-- **Closed aligned Smith endpoint dispatcher.**

All three former first-stop endpoint types are now discharged.

The only possible outcomes are exactly those needed by global assembly:

1. a canonical local Smith repair/terminal outcome;
2. an honest strict defect restart on the fixed once-ramified scale.

The coupled-wall alternative from Phase 93.70 is impossible. -/
theorem alignedSmith_closedBoundaryDispatcher
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
      HasSeparatedSectionWallStrictRestart Delta s := by
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
  · rcases
      alignedSmith_separatedBoundaryDispatcher
        (s := s)
        P hP a b hdef hD hcoll
        ha hb hs complexity newRepair with
      hlocal | hrestart | hcoupled
    · exact Or.inl hlocal
    · exact Or.inr hrestart
    · exact
        False.elim
          (coupledAlignedSmithWall_impossible_of_noPrimitive
            P hP a b hD hcoll
            ha hb hprimitive hcoupled)

end

end HC4.Valuation
