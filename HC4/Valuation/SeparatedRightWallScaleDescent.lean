import HC4.Valuation.PointedShearContinuation
import HC4.Valuation.ExactKernelDefectDrop
import Mathlib.Tactic

/-!
# Separated right Smith wall: genuine unramified scale descent

Phase 93.73 closes the pointed-coordinate problem at a separated right
Smith section wall, but its first implementation still lived on the
once-ramified parameter scale.

This file removes that scale obstruction completely.

Let the first separated right wall occur in a transverse coordinate `i`.
Write `v_i` for the exact parameter order of that moving coordinate.

There are two arithmetic branches.

## Ten-aligned branch

If the first wall step is a multiple of ten, write

    N = 10 m.

This includes every `y/z` wall and every `w` wall of even parameter order.

The aligned inequalities divide by twenty exactly.  Therefore the
ramified first-wall construction is the ramification of the honest
unramified symmetric Smith move

    theta_1 = theta_2 = m.

The strict separated-wall margin gives one *unramified* common parameter
factor.  Hence

    Delta -> Delta - 4.

No repeated denominator clearing occurs.

## Odd w branch

The only remaining possibility is a `w` wall whose exact section order is

    v_w = 2 l + 1.

Instead of ramifying, perform the smaller honest symmetric Smith move

    theta_1 = theta_2 = l.

The first-wall inequalities imply that this move is integral both on the
family and on the marked sections.

After this move all three transformed transverse section coordinates are
divisible by `tau`.  Inflate the three transverse source variables once:

    y -> tau y,
    z -> tau z,
    w -> tau w.

The separated-wall margin implies that every coefficient of the inflated
potential is divisible by `tau^2`.  Extract those two common parameter
factors.

The Hessian determinant bookkeeping is exact:

    Smith_l                       : Delta -> Delta
    three source inflations       : Delta -> Delta + 6
    common factor tau^2 extraction: Delta + 6 -> Delta - 2.

Thus the exceptional odd `w` wall also returns an honest polynomial family
over the original parameter ring with a strictly smaller defect.

Finally the determinant-one pointed shear from Phase 93.73 restores the
canonical special pair `0,e0` without changing the defect.

The headline theorem is

    separatedRightSmithWall_strictCanonicalGeometricRestart

and proves that **every** separated right wall produces a canonical
geometric successor with strictly smaller *unramified* determinant defect.

Combining it with the green zero-section dispatcher gives

    alignedSmith_zeroSection_closedGeometricStep

whose only outcomes are now:

* canonical local repair/terminal; or
* genuine strict geometric defect restart.

There is no residual Smith section-wall scale case.
-/

namespace HC4.Valuation

noncomputable section

open scoped BigOperators
open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Basic symmetric-Smith arithmetic on the unramified scale
------------------------------------------------------------------------ -/

/-- Raw Smith exponent at `(2,2)` is twice the raw exponent at `(1,1)`. -/
theorem smithConformalRawExponent_two_two_eq_two_mul_one_one
    (d : Fin 4 →₀ ℕ) :
    smithConformalRawExponent 2 2 d =
      2 * smithConformalRawExponent 1 1 d := by
  unfold smithConformalRawExponent
  ring

/-- Equal Smith weights factor out of the raw exponent. -/
theorem smithConformalRawExponent_same
    (m : ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithConformalRawExponent m m d =
      m * smithConformalRawExponent 1 1 d := by
  unfold smithConformalRawExponent
  ring

/-- Equal Smith weights have multiplier exponent `2m`. -/
@[simp] theorem smithConformalMultiplierExponent_same
    (m : ℕ) :
    smithConformalMultiplierExponent m m = 2 * m := by
  unfold smithConformalMultiplierExponent
  omega

/-- The coefficient factor for equal Smith weights is the corresponding
pure parameter power. -/
theorem smithConformalCoefficientFactor_same
    (m : ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithConformalCoefficientFactor
        (K := K) m m d =
      Polynomial.X ^
        (m * smithConformalRawExponent 1 1 d) := by
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

/-- Symmetric Smith derivative written at half-scale. -/
theorem smithSeparatorDelta_projection_eq_two_mul_halfRaw
    (d : Fin 4 →₀ ℕ) :
    smithSeparatorDelta 1 1
        (smithAxisProjection d) =
      2 *
        ((smithConformalRawExponent 1 1 d : ℤ) - 2) := by
  rw [smithSeparatorDelta_projection_eq_raw_sub_four]
  rw [smithConformalRawExponent_two_two_eq_two_mul_one_one]
  push_cast
  ring

/-! -----------------------------------------------------------------------
  Ten-aligned separated walls
------------------------------------------------------------------------ -/

/-- At a separated right wall whose step is `10*m`, the strict residual
margin is in fact at least twenty. -/
theorem separatedRightWall_margin_twenty_of_step_eq_ten_mul
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    4 * N + 20 ≤
      N * smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder P d := by
  dsimp
  let N :=
    alignedSmithGenuineFirstWall
      P (zeroPolynomialSection (K := K)) b hwall
  have hbase :
      4 * N + 10 ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d := by
    exact
      separatedSectionWall_coefficient_margin_ten
        P b hwall hnotCoeff hnoPrimitive
        hsection hb hd
  rcases
      smithSeparatorDelta_one_one_even
        (smithAxisProjection d) with
    ⟨z, hz⟩
  have hrel :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  let v := smithFamilyCoefficientOrder P d
  -- Rebuild the useful integral residual identity directly.
  have hres' :
      (N : ℤ) *
            (smithConformalRawExponent 2 2 d : ℤ) +
          (alignedSmithRamificationIndex : ℤ) *
            (smithFamilyCoefficientOrder P d : ℤ) -
          4 * (N : ℤ) =
        20 *
          ((smithFamilyCoefficientOrder P d : ℤ) +
            (m : ℤ) * z) := by
    dsimp [N]
    rw [hN]
    rw [hz] at hrel
    norm_num [alignedSmithRamificationIndex]
    nlinarith
  have hbaseInt :
      (10 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    have hcast :
        (4 * N + 10 : ℤ) ≤
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) := by
      exact_mod_cast hbase
    omega
  have htwentyInt :
      (20 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    rw [hres'] at hbaseInt ⊢
    omega
  have hout :
      (4 * N + 20 : ℕ) ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d := by
    exact_mod_cast
      (show
        (4 * N + 20 : ℤ) ≤
          (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) by
        omega)
  exact hout

/-- **Unramified coefficient integrality at a ten-aligned separated wall.** -/
theorem tenAlignedSeparatedRightWall_unramifiedCoefficientDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m) :
    HasIntegralSmithConformalCoefficientDivisibility
      m m P := by
  intro d hd
  let v := smithFamilyCoefficientOrder P d
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_dvd P hd
  have hmargin :=
    separatedRightWall_margin_twenty_of_step_eq_ten_mul
      P b hwall hnotCoeff hnoPrimitive hsection hb
      m hN hd
  have hraw2 :=
    smithConformalRawExponent_two_two_eq_two_mul_one_one d
  have hpowLe :
      2 * m + 1 ≤
        m * smithConformalRawExponent 1 1 d + v := by
    dsimp at hmargin
    rw [hN, hraw2] at hmargin
    norm_num [alignedSmithRamificationIndex] at hmargin
    nlinarith
  have htotal :
      Polynomial.X ^
          (m * smithConformalRawExponent 1 1 d + v) ∣
        smithConformalCoefficientFactor
            (K := K) m m d *
          MvPolynomial.coeff d P := by
    rcases hvdiv with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [smithConformalCoefficientFactor_same]
    rw [hr]
    calc
      Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d) *
          (Polynomial.X ^ v * r) =
        (Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d) *
          Polynomial.X ^ v) * r := by ring
      _ =
        Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d + v) *
          r := by rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ (2 * m) : Polynomial K) ∣
        Polynomial.X ^
          (m * smithConformalRawExponent 1 1 d + v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ (by omega)
  have hout := dvd_trans hsmall htotal
  simpa [smithConformalMultiplier,
    smithConformalMultiplierExponent_same] using hout

/-- Section divisibility for the honest unramified symmetric Smith move at
a ten-aligned first wall. -/
theorem tenAlignedSeparatedRightWall_unramifiedSectionDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m) :
    HasIntegralSmithConformalSectionDivisibility
      m m b := by
  intro i
  fin_cases i
  · simp [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent]
  · by_cases hz : b 1 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord :=
        sectionCoordinateParameterOrder_dvd (b 1)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (1 : Fin 4))
          (by decide) hz
      simp only [show (1 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          m ≤ sectionCoordinateParameterOrder (b 1) := by
        omega
      have hsmall :
          (Polynomial.X ^ m : Polynomial K) ∣
            Polynomial.X ^
              sectionCoordinateParameterOrder (b 1) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      have hout := dvd_trans hsmall hord
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent] using hout
  · by_cases hz : b 2 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord :=
        sectionCoordinateParameterOrder_dvd (b 2)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (2 : Fin 4))
          (by decide) hz
      simp only [show (2 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          m ≤ sectionCoordinateParameterOrder (b 2) := by
        omega
      have hsmall :
          (Polynomial.X ^ m : Polynomial K) ∣
            Polynomial.X ^
              sectionCoordinateParameterOrder (b 2) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      have hout := dvd_trans hsmall hord
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent] using hout
  · by_cases hz : b 3 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord :=
        sectionCoordinateParameterOrder_dvd (b 3)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (3 : Fin 4))
          (by decide) hz
      simp only [if_pos rfl] at hnonneg
      unfold alignedSmithSectionValueFour at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          2 * m ≤ sectionCoordinateParameterOrder (b 3) := by
        omega
      have hsmall :
          (Polynomial.X ^ (2 * m) : Polynomial K) ∣
            Polynomial.X ^
              sectionCoordinateParameterOrder (b 3) :=
        polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle
      have hout := dvd_trans hsmall hord
      simpa [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent, two_mul] using hout

/-- The zero section is integrally divisible for every Smith weight. -/
theorem zeroPolynomialSection_smithDivisibility
    (m : ℕ) :
    HasIntegralSmithConformalSectionDivisibility
      (K := K) m m
      (zeroPolynomialSection (K := K)) := by
  intro i
  simp [zeroPolynomialSection]

/-- The integral symmetric Smith transform of the zero section is exactly
the zero section. -/
theorem integralSmithConformalSection_zeroPolynomialSection
    (m : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (K := K) m m
        (zeroPolynomialSection (K := K))) :
    integralSmithConformalSection
        m m
        (zeroPolynomialSection (K := K))
        hdiv =
      zeroPolynomialSection (K := K) := by
  funext i
  have hreinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K)
        m m
        (zeroPolynomialSection (K := K))
        hdiv)
      i
  let q :=
    integralSmithConformalSection
      m m
      (zeroPolynomialSection (K := K))
      hdiv i
  let e :=
    smithConformalSourceExponent m m i
  have heq :
      Polynomial.X ^ e * q =
        Polynomial.X ^ e * 0 := by
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient,
      zeroPolynomialSection, e, q] using hreinflate
  have hcancel :=
    polynomial_X_pow_mul_cancel
      (K := K) e heq
  simpa [q, zeroPolynomialSection] using hcancel

/-- Coordinate zero of an integral symmetric Smith section is unchanged. -/
theorem integralSmithConformalSection_zeroCoordinate
    (m : ℕ)
    (b : Fin 4 → Polynomial K)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        m m b) :
    integralSmithConformalSection m m b hdiv 0 =
      b 0 := by
  have hreinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K) m m b hdiv)
      (0 : Fin 4)
  simpa [smithConformalInflateSection,
    smithConformalDerivativeCoefficient,
    smithConformalSourceExponent] using hreinflate

/-- The direct ten-aligned Smith family has one common parameter factor. -/
theorem tenAlignedSeparatedRightWall_unramifiedCommonFactor_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m)
    (hPdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        m m P) :
    HasCommonParameterFactor 1
      (integralSmithConformalFamily m m P hPdiv) := by
  intro d hdQ
  have hdP :
      d ∈ P.support :=
    support_integralSmithConformalFamily_subset
      m m P hPdiv hdQ
  let v := smithFamilyCoefficientOrder P d
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_dvd P hdP
  have hmargin :=
    separatedRightWall_margin_twenty_of_step_eq_ten_mul
      P b hwall hnotCoeff hnoPrimitive hsection hb
      m hN hdP
  have hraw2 :=
    smithConformalRawExponent_two_two_eq_two_mul_one_one d
  have hpowLe :
      2 * m + 1 ≤
        m * smithConformalRawExponent 1 1 d + v := by
    dsimp at hmargin
    rw [hN, hraw2] at hmargin
    norm_num [alignedSmithRamificationIndex] at hmargin
    nlinarith
  have htotal :
      Polynomial.X ^
          (m * smithConformalRawExponent 1 1 d + v) ∣
        smithConformalCoefficientFactor
            (K := K) m m d *
          MvPolynomial.coeff d P := by
    rcases hvdiv with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [smithConformalCoefficientFactor_same]
    rw [hr]
    calc
      Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d) *
          (Polynomial.X ^ v * r) =
        (Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d) *
          Polynomial.X ^ v) * r := by ring
      _ =
        Polynomial.X ^
            (m * smithConformalRawExponent 1 1 d + v) * r := by
          rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ (2 * m + 1) : Polynomial K) ∣
        Polynomial.X ^
          (m * smithConformalRawExponent 1 1 d + v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hpowLe
  have hbig := dvd_trans hsmall htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      m m P hPdiv hdP
  have hquot :
      (Polynomial.X ^ (2 * m + 1) : Polynomial K) ∣
        Polynomial.X ^ (2 * m) *
          smithConformalCoefficientQuotient
            m m P hPdiv d := by
    have hraw :
        (Polynomial.X ^ (2 * m + 1) : Polynomial K) ∣
          smithConformalMultiplier (K := K) m m *
            smithConformalCoefficientQuotient
              m m P hPdiv d := by
      rw [← hspec]
      exact hbig
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent_same] using hraw
  have hX :
      Polynomial.X ∣
        smithConformalCoefficientQuotient
          m m P hPdiv d := by
    have hout :=
      polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
        (K := K) (2 * m) 1
        (smithConformalCoefficientQuotient
          m m P hPdiv d)
        (by
          simpa [Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hquot)
    simpa using hout
  rw [coeff_integralSmithConformalFamily_of_mem
    m m P hPdiv hdP]
  simpa only [pow_one] using hX

/-! -----------------------------------------------------------------------
  One-coordinate inverse section for honest source inflation
------------------------------------------------------------------------ -/

/-- A section whose selected coordinate is divisible by `X`. -/
def HasUnitKernelSectionDivisibility
    (kernel : Fin 4)
    (a : Fin 4 → Polynomial K) : Prop :=
  Polynomial.X ∣ a kernel

/-- Chosen inverse section for the source inflation
`X_kernel -> tau * X_kernel`. -/
noncomputable def unitKernelDeflateSection
    (kernel : Fin 4)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasUnitKernelSectionDivisibility kernel a) :
    Fin 4 → Polynomial K :=
  fun i =>
    if hi : i = kernel then
      Classical.choose hdiv
    else
      a i

/-- Reinflating the chosen inverse section recovers the original section. -/
theorem kernelBlowupSection_unitKernelDeflateSection
    (kernel : Fin 4)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasUnitKernelSectionDivisibility kernel a) :
    kernelBlowupSection kernel 1
        (unitKernelDeflateSection kernel a hdiv) =
      a := by
  funext i
  by_cases hi : i = kernel
  · subst i
    unfold kernelBlowupSection
    simp only [if_pos rfl, pow_one]
    unfold unitKernelDeflateSection
    simp only [dif_pos rfl]
    exact (Classical.choose_spec hdiv).symm
  · simp [kernelBlowupSection,
      unitKernelDeflateSection, hi]

/-- Exact collision covariance for an honest one-coordinate source
inflation when the marked sections can be divided by `X` in that
coordinate. -/
theorem polynomialFamilyExactGradientCollision_kernelInflate_unit
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hadiv : HasUnitKernelSectionDivisibility kernel a)
    (hbdiv : HasUnitKernelSectionDivisibility kernel b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (kernelInflateHom (K := K) kernel 1 P)
      (unitKernelDeflateSection kernel a hadiv)
      (unitKernelDeflateSection kernel b hbdiv) := by
  intro i
  rw [pderiv_kernelInflateHom]
  simp only [map_mul, MvPolynomial.eval_C]
  rw [eval_kernelInflateHom]
  rw [eval_kernelInflateHom]
  rw [kernelBlowupSection_unitKernelDeflateSection]
  rw [kernelBlowupSection_unitKernelDeflateSection]
  rw [hcoll i]

/-- Kernel source inflation by one raises a pure four-variable Hessian
defect by exactly two. -/
theorem kernelInflateHom_unit_hasHessianDefect_add_two
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (kernelInflateHom (K := K) kernel 1 P)
      (Delta + 2) := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_kernelInflateHom]
  rw [hdef]
  simp [kernelInflateHom,
    kernelInflateDerivativeCoefficient]
  have hpoly :
      (Polynomial.X ^ 2 : Polynomial K) *
          Polynomial.X ^ Delta =
        Polynomial.X ^ (Delta + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hC :=
    congrArg
      (fun q : Polynomial K =>
        (MvPolynomial.C q :
          MvPolynomial (Fin 4) (Polynomial K)))
      hpoly
  simpa only [MvPolynomial.C_mul,
    MvPolynomial.C_pow] using hC

/-- Source inflation introduces no source-degree change. -/
theorem kernelInflateHom_isHomogeneous
    {D : ℕ}
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D) :
    (kernelInflateHom (K := K) kernel 1 P).IsHomogeneous D := by
  intro d hdI
  rw [coeff_kernelInflateHom] at hdI
  have hsource :
      MvPolynomial.coeff d P ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdI
    exact hdI rfl
  exact hP hsource

/-! -----------------------------------------------------------------------
  Odd w wall: smaller Smith move + transverse inflation + X^2 extraction
------------------------------------------------------------------------ -/

/-- Coefficient integrality of the smaller Smith move in the odd-w branch. -/
theorem oddWSeparatedRightWall_smallSmithCoefficientDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1)) :
    HasIntegralSmithConformalCoefficientDivisibility
      l l P := by
  intro d hd
  let v := smithFamilyCoefficientOrder P d
  let r := smithConformalRawExponent 1 1 d
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_dvd P hd
  have hlegal :=
    alignedSmithGenuineFirstWall_coefficient_nonnegative
      P (zeroPolynomialSection (K := K)) b hwall hd
  have hdelta :=
    smithSeparatorDelta_projection_eq_two_mul_halfRaw d
  have hpowLe :
      2 * l ≤ l * r + v := by
    by_cases hr : 2 ≤ r
    · dsimp [r]
      have hv : 0 ≤ v := Nat.zero_le _
      nlinarith
    · have hcases : r = 0 ∨ r = 1 := by
        omega
      rcases hcases with hr0 | hr1
      · have hr0raw :
          smithConformalRawExponent 1 1 d = 0 := by
            simpa [r] using hr0
        unfold alignedSmithCoefficientValue at hlegal
        rw [hN, hdelta, hr0raw] at hlegal
        norm_num [alignedSmithRamificationIndex] at hlegal
        dsimp [r, v]
        rw [hr0raw]
        nlinarith
      · have hr1raw :
          smithConformalRawExponent 1 1 d = 1 := by
            simpa [r] using hr1
        unfold alignedSmithCoefficientValue at hlegal
        rw [hN, hdelta, hr1raw] at hlegal
        norm_num [alignedSmithRamificationIndex] at hlegal
        dsimp [r, v]
        rw [hr1raw]
        nlinarith
  have htotal :
      Polynomial.X ^ (l * r + v) ∣
        smithConformalCoefficientFactor
            (K := K) l l d *
          MvPolynomial.coeff d P := by
    rcases hvdiv with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [smithConformalCoefficientFactor_same]
    dsimp [r]
    rw [hq]
    calc
      Polynomial.X ^
            (l * smithConformalRawExponent 1 1 d) *
          (Polynomial.X ^ v * q) =
        (Polynomial.X ^
            (l * smithConformalRawExponent 1 1 d) *
          Polynomial.X ^ v) * q := by ring
      _ =
        Polynomial.X ^
            (l * smithConformalRawExponent 1 1 d + v) * q := by
          rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ (2 * l) : Polynomial K) ∣
        Polynomial.X ^ (l * r + v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hpowLe
  have hout := dvd_trans hsmall htotal
  simpa [smithConformalMultiplier,
    smithConformalMultiplierExponent_same] using hout

/-- Section integrality for the smaller Smith move in the odd-w branch. -/
theorem oddWSeparatedRightWall_smallSmithSectionDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1)) :
    HasIntegralSmithConformalSectionDivisibility
      l l b := by
  intro i
  fin_cases i
  · simp [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent]
  · by_cases hz : b 1 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord := sectionCoordinateParameterOrder_dvd (b 1)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (1 : Fin 4))
          (by decide) hz
      simp only [show (1 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          l ≤ sectionCoordinateParameterOrder (b 1) := by
        omega
      exact dvd_trans
        (polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle) hord
  · by_cases hz : b 2 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord := sectionCoordinateParameterOrder_dvd (b 2)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (2 : Fin 4))
          (by decide) hz
      simp only [show (2 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          l ≤ sectionCoordinateParameterOrder (b 2) := by
        omega
      exact dvd_trans
        (polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle) hord
  · by_cases hz : b 3 = 0
    · simp [hz, smithConformalDerivativeCoefficient,
        smithConformalSourceExponent]
    · have hord := sectionCoordinateParameterOrder_dvd (b 3)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (3 : Fin 4))
          (by decide) hz
      simp only [if_pos rfl] at hnonneg
      unfold alignedSmithSectionValueFour at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hle :
          2 * l ≤ sectionCoordinateParameterOrder (b 3) := by
        omega
      have hle' :
          smithConformalSourceExponent l l (3 : Fin 4) ≤
            sectionCoordinateParameterOrder (b 3) := by
        simpa [smithConformalSourceExponent, two_mul] using hle
      exact dvd_trans
        (polynomial_X_pow_dvd_X_pow_of_le
          (K := K) _ _ hle') hord

/-- The smaller-Smith transformed right section has one remaining parameter
factor in every transverse coordinate. -/
theorem oddWSeparatedRightWall_smallSmith_transverse_X_dvd
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1))
    (hwstep :
      alignedSmithSectionWallStep (3 : Fin 4) (b 3) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall)
    (hbdiv :
      HasIntegralSmithConformalSectionDivisibility
        l l b) :
    ∀ i : Fin 4,
      i ≠ 0 →
      Polynomial.X ∣
        integralSmithConformalSection l l b hbdiv i := by
  intro i hi0
  fin_cases i
  · exact False.elim (hi0 rfl)
  · by_cases hz : b 1 = 0
    · have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (1 : Fin 4)
      have hq :
          integralSmithConformalSection l l b hbdiv 1 = 0 := by
        rw [hz] at hreinflate
        have hcancel :=
          polynomial_X_pow_mul_cancel
            (K := K) l
            (by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent] using hreinflate)
        simpa using hcancel
      have hout :
          Polynomial.X ∣
            integralSmithConformalSection l l b hbdiv
              (1 : Fin 4) := by
        rw [hq]
        simp
      simpa using hout
    · have hord := sectionCoordinateParameterOrder_dvd (b 1)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (1 : Fin 4))
          (by decide) hz
      simp only [show (1 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hnext :
          Polynomial.X ^ (l + 1) ∣ b 1 := by
        exact dvd_trans
          (polynomial_X_pow_dvd_X_pow_of_le
            (K := K) _ _
            (by omega :
              l + 1 ≤ sectionCoordinateParameterOrder (b 1)))
          hord
      have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (1 : Fin 4)
      have hbig :
          Polynomial.X ^ (l + 1) ∣
            Polynomial.X ^ l *
              integralSmithConformalSection l l b hbdiv 1 := by
        rw [show
          Polynomial.X ^ l *
              integralSmithConformalSection l l b hbdiv 1 =
            b 1 by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent] using hreinflate]
        exact hnext
      have hout :=
        polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
          (K := K) l 1
          (integralSmithConformalSection l l b hbdiv 1)
          (by simpa [Nat.add_comm] using hbig)
      simpa using hout
  · by_cases hz : b 2 = 0
    · have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (2 : Fin 4)
      have hq :
          integralSmithConformalSection l l b hbdiv 2 = 0 := by
        rw [hz] at hreinflate
        have hcancel :=
          polynomial_X_pow_mul_cancel
            (K := K) l
            (by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent] using hreinflate)
        simpa using hcancel
      have hout :
          Polynomial.X ∣
            integralSmithConformalSection l l b hbdiv
              (2 : Fin 4) := by
        rw [hq]
        simp
      simpa using hout
    · have hord := sectionCoordinateParameterOrder_dvd (b 2)
      have hnonneg :=
        alignedSmithGenuineFirstWall_section_nonnegative
          P (zeroPolynomialSection (K := K)) b hwall
          b (Or.inr rfl) (i := (2 : Fin 4))
          (by decide) hz
      simp only [show (2 : Fin 4) ≠ 3 by decide,
        if_false] at hnonneg
      unfold alignedSmithSectionValueTwo at hnonneg
      rw [hN] at hnonneg
      norm_num [alignedSmithRamificationIndex] at hnonneg
      have hnext :
          Polynomial.X ^ (l + 1) ∣ b 2 := by
        exact dvd_trans
          (polynomial_X_pow_dvd_X_pow_of_le
            (K := K) _ _
            (by omega :
              l + 1 ≤ sectionCoordinateParameterOrder (b 2)))
          hord
      have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (2 : Fin 4)
      have hbig :
          Polynomial.X ^ (l + 1) ∣
            Polynomial.X ^ l *
              integralSmithConformalSection l l b hbdiv 2 := by
        rw [show
          Polynomial.X ^ l *
              integralSmithConformalSection l l b hbdiv 2 =
            b 2 by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent] using hreinflate]
        exact hnext
      have hout :=
        polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
          (K := K) l 1
          (integralSmithConformalSection l l b hbdiv 2)
          (by simpa [Nat.add_comm] using hbig)
      simpa using hout
  · by_cases hz : b 3 = 0
    · have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (3 : Fin 4)
      have hq :
          integralSmithConformalSection l l b hbdiv 3 = 0 := by
        rw [hz] at hreinflate
        have hcancel :=
          polynomial_X_pow_mul_cancel
            (K := K) (2 * l)
            (by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent] using hreinflate)
        simpa using hcancel
      have hout :
          Polynomial.X ∣
            integralSmithConformalSection l l b hbdiv
              (3 : Fin 4) := by
        rw [hq]
        simp
      simpa using hout
    · have hord := sectionCoordinateParameterOrder_dvd (b 3)
      have horder :
          sectionCoordinateParameterOrder (b 3) =
            2 * l + 1 := by
        have hw := hwstep
        simp [alignedSmithSectionWallStep] at hw
        rw [hN] at hw
        omega
      have hnext :
          Polynomial.X ^ (2 * l + 1) ∣ b 3 := by
        rw [← horder]
        exact hord
      have hreinflate :=
        congrFun
          (smithConformalInflateSection_integralSection_eq
            (K := K) l l b hbdiv)
          (3 : Fin 4)
      have hbig :
          Polynomial.X ^ (2 * l + 1) ∣
            Polynomial.X ^ (2 * l) *
              integralSmithConformalSection l l b hbdiv 3 := by
        rw [show
          Polynomial.X ^ (2 * l) *
              integralSmithConformalSection l l b hbdiv 3 =
            b 3 by
              simpa [smithConformalInflateSection,
                smithConformalDerivativeCoefficient,
                smithConformalSourceExponent, two_mul] using hreinflate]
        exact hnext
      have hout :=
        polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
          (K := K) (2 * l) 1
          (integralSmithConformalSection l l b hbdiv 3)
          (by simpa [Nat.add_comm, Nat.add_assoc] using hbig)
      simpa using hout

/-! ## Three transverse source inflations -/

noncomputable def unitTransverseInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  kernelInflateHom (K := K) (3 : Fin 4) 1
    (kernelInflateHom (K := K) (2 : Fin 4) 1
      (kernelInflateHom (K := K) (1 : Fin 4) 1 P))

/-- Exact coefficient formula for the three transverse source inflations. -/
theorem coeff_unitTransverseInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (unitTransverseInflateFamily (K := K) P) =
      Polynomial.X ^ (d 1 + d 2 + d 3) *
        MvPolynomial.coeff d P := by
  unfold unitTransverseInflateFamily
  repeat' rw [coeff_kernelInflateHom]
  simp [kernelCoefficientTauPower]
  rw [pow_add, pow_add]
  ring

/-- Three transverse source inflations preserve ordinary source
homogeneity. -/
theorem unitTransverseInflateFamily_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D) :
    (unitTransverseInflateFamily (K := K) P).IsHomogeneous D := by
  unfold unitTransverseInflateFamily
  apply kernelInflateHom_isHomogeneous
  apply kernelInflateHom_isHomogeneous
  apply kernelInflateHom_isHomogeneous
  exact hP

/-- Three transverse source inflations raise the Hessian defect by six. -/
theorem unitTransverseInflateFamily_hasHessianDefect_add_six
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (unitTransverseInflateFamily P)
      (Delta + 6) := by
  unfold unitTransverseInflateFamily
  have h1 :=
    kernelInflateHom_unit_hasHessianDefect_add_two
      (K := K) (1 : Fin 4) P hdef
  have h2 :=
    kernelInflateHom_unit_hasHessianDefect_add_two
      (K := K) (2 : Fin 4)
      (kernelInflateHom (K := K) (1 : Fin 4) 1 P)
      h1
  have h3 :=
    kernelInflateHom_unit_hasHessianDefect_add_two
      (K := K) (3 : Fin 4)
      (kernelInflateHom (K := K) (2 : Fin 4) 1
        (kernelInflateHom (K := K) (1 : Fin 4) 1 P))
      h2
  convert h3 using 1 <;> omega

/-- The zero section remains zero after all three inverse source
inflations. -/
theorem unitKernelDeflateSection_zero
    (kernel : Fin 4)
    (hdiv :
      HasUnitKernelSectionDivisibility
        (K := K) kernel
        (zeroPolynomialSection (K := K))) :
    unitKernelDeflateSection kernel
        (zeroPolynomialSection (K := K)) hdiv =
      zeroPolynomialSection (K := K) := by
  funext i
  by_cases hi : i = kernel
  · subst i
    unfold unitKernelDeflateSection
    simp only [dif_pos rfl]
    have hspec := Classical.choose_spec hdiv
    change
      (0 : Polynomial K) =
        Polynomial.X * Classical.choose hdiv at hspec
    have heq :
        Polynomial.X ^ 1 * Classical.choose hdiv =
          Polynomial.X ^ 1 * 0 := by
      simpa [pow_one] using hspec.symm
    have hcancel :=
      polynomial_X_pow_mul_cancel
        (K := K) 1 heq
    exact hcancel
  · simp [unitKernelDeflateSection,
      zeroPolynomialSection, hi]

/-- Dependent-safe zero-section transport for a chosen inverse coordinate. -/
theorem unitKernelDeflateSection_eq_zero_of_eq_zero
    (kernel : Fin 4)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasUnitKernelSectionDivisibility kernel a)
    (ha : a = zeroPolynomialSection (K := K)) :
    unitKernelDeflateSection kernel a hdiv =
      zeroPolynomialSection (K := K) := by
  subst a
  exact unitKernelDeflateSection_zero kernel hdiv

/-- Package the three inverse-section steps. -/
noncomputable def unitTransverseDeflateSection
    (a : Fin 4 → Polynomial K)
    (h1 : HasUnitKernelSectionDivisibility (K := K) 1 a)
    (h2 :
      HasUnitKernelSectionDivisibility (K := K) 2
        (unitKernelDeflateSection 1 a h1))
    (h3 :
      HasUnitKernelSectionDivisibility (K := K) 3
        (unitKernelDeflateSection 2
          (unitKernelDeflateSection 1 a h1) h2)) :
    Fin 4 → Polynomial K :=
  unitKernelDeflateSection 3
    (unitKernelDeflateSection 2
      (unitKernelDeflateSection 1 a h1) h2) h3

/-- Sequential exact collision covariance for the three transverse
inflations. -/
theorem polynomialFamilyExactGradientCollision_unitTransverseInflate
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (ha1 : HasUnitKernelSectionDivisibility (K := K) 1 a)
    (hb1 : HasUnitKernelSectionDivisibility (K := K) 1 b)
    (ha2 :
      HasUnitKernelSectionDivisibility (K := K) 2
        (unitKernelDeflateSection 1 a ha1))
    (hb2 :
      HasUnitKernelSectionDivisibility (K := K) 2
        (unitKernelDeflateSection 1 b hb1))
    (ha3 :
      HasUnitKernelSectionDivisibility (K := K) 3
        (unitKernelDeflateSection 2
          (unitKernelDeflateSection 1 a ha1) ha2))
    (hb3 :
      HasUnitKernelSectionDivisibility (K := K) 3
        (unitKernelDeflateSection 2
          (unitKernelDeflateSection 1 b hb1) hb2))
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (unitTransverseInflateFamily P)
      (unitTransverseDeflateSection a ha1 ha2 ha3)
      (unitTransverseDeflateSection b hb1 hb2 hb3) := by
  have hcoll1 :=
    polynomialFamilyExactGradientCollision_kernelInflate_unit
      (K := K) (1 : Fin 4) P a b
      ha1 hb1 hcoll
  have hcoll2 :=
    polynomialFamilyExactGradientCollision_kernelInflate_unit
      (K := K) (2 : Fin 4)
      (kernelInflateHom (K := K) (1 : Fin 4) 1 P)
      (unitKernelDeflateSection 1 a ha1)
      (unitKernelDeflateSection 1 b hb1)
      ha2 hb2 hcoll1
  have hcoll3 :=
    polynomialFamilyExactGradientCollision_kernelInflate_unit
      (K := K) (3 : Fin 4)
      (kernelInflateHom (K := K) (2 : Fin 4) 1
        (kernelInflateHom (K := K) (1 : Fin 4) 1 P))
      (unitKernelDeflateSection 2
        (unitKernelDeflateSection 1 a ha1) ha2)
      (unitKernelDeflateSection 2
        (unitKernelDeflateSection 1 b hb1) hb2)
      ha3 hb3 hcoll2
  simpa [unitTransverseInflateFamily,
    unitTransverseDeflateSection] using hcoll3

/-- Dividing one coordinate leaves every other coordinate unchanged. -/
theorem unitKernelDeflateSection_of_ne
    (kernel : Fin 4)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasUnitKernelSectionDivisibility kernel a)
    {i : Fin 4}
    (hi : i ≠ kernel) :
    unitKernelDeflateSection kernel a hdiv i = a i := by
  simp [unitKernelDeflateSection, hi]

/-- Coordinate zero is unchanged by all three inverse transverse
inflations. -/
theorem unitTransverseDeflateSection_zeroCoordinate
    (a : Fin 4 → Polynomial K)
    (h1 : HasUnitKernelSectionDivisibility (K := K) 1 a)
    (h2 :
      HasUnitKernelSectionDivisibility (K := K) 2
        (unitKernelDeflateSection 1 a h1))
    (h3 :
      HasUnitKernelSectionDivisibility (K := K) 3
        (unitKernelDeflateSection 2
          (unitKernelDeflateSection 1 a h1) h2)) :
    unitTransverseDeflateSection a h1 h2 h3 0 = a 0 := by
  simp [unitTransverseDeflateSection,
    unitKernelDeflateSection]

/-- In the odd-w branch, after the smaller Smith move and three transverse
inflations, every source coefficient has a common `X^2` factor. -/
theorem oddWSeparatedRightWall_transverseInflate_commonFactor_two
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1))
    (hPdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        l l P) :
    HasCommonParameterFactor 2
      (unitTransverseInflateFamily
        (integralSmithConformalFamily l l P hPdiv)) := by
  let S :=
    integralSmithConformalFamily l l P hPdiv
  intro d hdI
  have hcoeffI :=
    MvPolynomial.mem_support_iff.mp hdI
  rw [coeff_unitTransverseInflateFamily] at hcoeffI
  have hpowNe :
      (Polynomial.X ^ (d 1 + d 2 + d 3) :
        Polynomial K) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hdScoeff :
      MvPolynomial.coeff d S ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcoeffI
    exact hcoeffI rfl
  have hdS : d ∈ S.support :=
    MvPolynomial.mem_support_iff.mpr hdScoeff
  have hdP :
      d ∈ P.support :=
    support_integralSmithConformalFamily_subset
      l l P hPdiv hdS
  let v := smithFamilyCoefficientOrder P d
  let raw := smithConformalRawExponent 1 1 d
  let t := d 1 + d 2 + d 3
  have hvdiv :
      Polynomial.X ^ v ∣
        MvPolynomial.coeff d P := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_dvd P hdP
  have hmargin :=
    separatedSectionWall_coefficient_margin_ten
      P b hwall hnotCoeff hnoPrimitive
      hsection hb hdP
  have hraw2 :=
    smithConformalRawExponent_two_two_eq_two_mul_one_one d
  have hpowLe :
      2 * l + 2 ≤
        l * raw + v + t := by
    dsimp [raw, t] at hmargin ⊢
    rw [hN, hraw2] at hmargin
    norm_num [alignedSmithRamificationIndex] at hmargin
    unfold smithConformalRawExponent at hmargin ⊢
    nlinarith
  have htotal :
      Polynomial.X ^ (l * raw + v + t) ∣
        Polynomial.X ^ t *
          (smithConformalCoefficientFactor
              (K := K) l l d *
            MvPolynomial.coeff d P) := by
    rcases hvdiv with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [smithConformalCoefficientFactor_same]
    dsimp [raw]
    rw [hq]
    repeat' rw [← pow_add]
    ring
  have hsmall :
      (Polynomial.X ^ (2 * l + 2) : Polynomial K) ∣
        Polynomial.X ^ (l * raw + v + t) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hpowLe
  have hbig := dvd_trans hsmall htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      l l P hPdiv hdP
  have hquot :
      (Polynomial.X ^ (2 * l + 2) : Polynomial K) ∣
        Polynomial.X ^ t *
          (Polynomial.X ^ (2 * l) *
            smithConformalCoefficientQuotient
              l l P hPdiv d) := by
    have hraw :
        (Polynomial.X ^ (2 * l + 2) : Polynomial K) ∣
          Polynomial.X ^ t *
            (smithConformalMultiplier (K := K) l l *
              smithConformalCoefficientQuotient
                l l P hPdiv d) := by
      rw [← hspec]
      exact hbig
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent_same] using hraw
  have hquot' :
      (Polynomial.X ^ ((2 * l) + 2) : Polynomial K) ∣
        Polynomial.X ^ (2 * l) *
          (Polynomial.X ^ t *
            smithConformalCoefficientQuotient
              l l P hPdiv d) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hquot
  have hX2 :
      Polynomial.X ^ 2 ∣
        Polynomial.X ^ t *
          smithConformalCoefficientQuotient
            l l P hPdiv d :=
    polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
      (K := K) (2 * l) 2
      (Polynomial.X ^ t *
        smithConformalCoefficientQuotient
          l l P hPdiv d)
      hquot'
  rw [coeff_unitTransverseInflateFamily]
  rw [coeff_integralSmithConformalFamily_of_mem
    l l P hPdiv hdP]
  exact hX2

/-! -----------------------------------------------------------------------
  Canonical strict geometric restart package
------------------------------------------------------------------------ -/

/-- A genuine geometric successor at strictly smaller determinant defect. -/
def HasCanonicalStrictGeometricDefectRestart
    (D Delta : ℕ) : Prop :=
  ∃ Delta' : ℕ,
    Delta' < Delta ∧
    ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
      ∃ b' : Fin 4 → Polynomial K,
        P'.IsHomogeneous D ∧
        HasPolynomialFamilyHessianDefect
          (K := K) P' Delta' ∧
        HasPolynomialFamilyExactGradientCollision
          P'
          (zeroPolynomialSection (K := K))
          b' ∧
        polynomialSectionSpecialPoint b' =
          coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Ten-aligned separated right wall gives the direct unramified drop
`Delta -> Delta - 4`. -/
theorem tenAlignedSeparatedRightWall_strictCanonicalRestart
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m) :
    HasCanonicalStrictGeometricDefectRestart
      (K := K) D Delta := by
  let hPdiv :=
    tenAlignedSeparatedRightWall_unramifiedCoefficientDivisibility
      P b hwall hnotCoeff hnoPrimitive hsection hb m hN
  let haDiv :=
    zeroPolynomialSection_smithDivisibility
      (K := K) m
  let hbDiv :=
    tenAlignedSeparatedRightWall_unramifiedSectionDivisibility
      P b hwall m hN
  let Q :=
    integralSmithConformalFamily m m P hPdiv
  let aQ :=
    integralSmithConformalSection
      m m (zeroPolynomialSection (K := K)) haDiv
  let bQ :=
    integralSmithConformalSection m m b hbDiv
  have hQhom :
      Q.IsHomogeneous D :=
    integralSmithConformalFamily_isHomogeneous
      P hP hPdiv
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q Delta :=
    integralSmithConformalFamily_preservesHessianDefect
      m m Delta P hPdiv hdef
  have hQcollRaw :
      HasPolynomialFamilyExactGradientCollision
        Q aQ bQ :=
    polynomialFamilyExactGradientCollision_integralSmithConformal
      m m P hPdiv
      (zeroPolynomialSection (K := K)) b
      haDiv hbDiv hcoll
  have haQ :
      aQ = zeroPolynomialSection (K := K) := by
    dsimp [aQ]
    exact
      integralSmithConformalSection_zeroPolynomialSection
        m haDiv
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q (zeroPolynomialSection (K := K)) bQ := by
    rw [← haQ]
    exact hQcollRaw
  have hbQ0 :
      polynomialSectionSpecialPoint bQ 0 = 1 := by
    have hzero :=
      integralSmithConformalSection_zeroCoordinate
        (K := K) m b hbDiv
    have hb0 := congrFun hb (0 : Fin 4)
    have hb0' :
        Polynomial.constantCoeff (b 0) = 1 := by
      simpa [polynomialSectionSpecialPoint,
        coordinateAxisPoint] using hb0
    change
      Polynomial.constantCoeff
        (integralSmithConformalSection m m b hbDiv 0) = 1
    rw [hzero]
    exact hb0'
  let hcommon :=
    tenAlignedSeparatedRightWall_unramifiedCommonFactor_one
      P b hwall hnotCoeff hnoPrimitive hsection hb
      m hN hPdiv
  let R :=
    commonParameterFactorFamily 1 Q hcommon
  have hRhom :
      R.IsHomogeneous D :=
    commonParameterFactorFamily_isHomogeneous
      Q hQhom hcommon
  have hRdef :
      HasPolynomialFamilyHessianDefect
        (K := K) R (Delta - 4) :=
    commonParameterFactor_one_hasHessianDefect_sub_four
      Q hcommon Delta hQdef
  have hRcoll :
      HasPolynomialFamilyExactGradientCollision
        R (zeroPolynomialSection (K := K)) bQ :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      1 Q hcommon
      (zeroPolynomialSection (K := K)) bQ hQcoll
  have hbudget :
      4 ≤ Delta :=
    four_le_defect_of_commonParameterFactor_one
      Q hcommon Delta hQdef
  let R' := pointedShearNormalisedFamily R bQ
  let b' := pointedShearNormalisedSection bQ
  refine
    ⟨Delta - 4, by omega, R', b', ?_, ?_, ?_, ?_⟩
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_isHomogeneous
        R bQ hRhom
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_preservesHessianDefect
        R bQ hRdef
  · dsimp [R', b']
    exact
      pointedShearNormalisedFamily_preservesExactCollision
        R bQ hRcoll
  · dsimp [b']
    exact
      pointedShearNormalisedSection_specialPoint
        bQ hbQ0

/-- **Odd w wall gives the direct unramified drop `Delta -> Delta - 2`.** -/
theorem oddWSeparatedRightWall_strictCanonicalRestart
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1))
    (hwstep :
      alignedSmithSectionWallStep (3 : Fin 4) (b 3) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall) :
    HasCanonicalStrictGeometricDefectRestart
      (K := K) D Delta := by
  let hPdiv :=
    oddWSeparatedRightWall_smallSmithCoefficientDivisibility
      P b hwall hnotCoeff hnoPrimitive hsection hb l hN
  let haDiv :=
    zeroPolynomialSection_smithDivisibility
      (K := K) l
  let hbDiv :=
    oddWSeparatedRightWall_smallSmithSectionDivisibility
      P b hwall l hN
  let S :=
    integralSmithConformalFamily l l P hPdiv
  let aS :=
    integralSmithConformalSection
      l l (zeroPolynomialSection (K := K)) haDiv
  let bS :=
    integralSmithConformalSection l l b hbDiv
  have hShom :
      S.IsHomogeneous D :=
    integralSmithConformalFamily_isHomogeneous
      P hP hPdiv
  have hSdef :
      HasPolynomialFamilyHessianDefect
        (K := K) S Delta :=
    integralSmithConformalFamily_preservesHessianDefect
      l l Delta P hPdiv hdef
  have hScollRaw :
      HasPolynomialFamilyExactGradientCollision
        S aS bS :=
    polynomialFamilyExactGradientCollision_integralSmithConformal
      l l P hPdiv
      (zeroPolynomialSection (K := K)) b
      haDiv hbDiv hcoll
  have haS :
      aS = zeroPolynomialSection (K := K) := by
    dsimp [aS]
    exact
      integralSmithConformalSection_zeroPolynomialSection
        l haDiv
  have hScoll :
      HasPolynomialFamilyExactGradientCollision
        S (zeroPolynomialSection (K := K)) bS := by
    rw [← haS]
    exact hScollRaw
  have hbS0 :
      polynomialSectionSpecialPoint bS 0 = 1 := by
    have hzero :=
      integralSmithConformalSection_zeroCoordinate
        (K := K) l b hbDiv
    have hb0 := congrFun hb (0 : Fin 4)
    have hb0' :
        Polynomial.constantCoeff (b 0) = 1 := by
      simpa [polynomialSectionSpecialPoint,
        coordinateAxisPoint] using hb0
    change
      Polynomial.constantCoeff
        (integralSmithConformalSection l l b hbDiv 0) = 1
    rw [hzero]
    exact hb0'
  have hbSX :
      ∀ i : Fin 4, i ≠ 0 →
        Polynomial.X ∣ bS i := by
    dsimp [bS]
    exact
      oddWSeparatedRightWall_smallSmith_transverse_X_dvd
        P b hwall l hN hwstep hbDiv
  have ha1 :
      HasUnitKernelSectionDivisibility
        (K := K) 1
        (zeroPolynomialSection (K := K)) := by
    simp [HasUnitKernelSectionDivisibility,
      zeroPolynomialSection]
  have hb1 :
      HasUnitKernelSectionDivisibility (K := K) 1 bS :=
    hbSX 1 (by decide)
  let a1 :=
    unitKernelDeflateSection
      (K := K) 1
      (zeroPolynomialSection (K := K)) ha1
  let b1 :=
    unitKernelDeflateSection (K := K) 1 bS hb1
  have ha1zero :
      a1 = zeroPolynomialSection (K := K) := by
    dsimp [a1]
    exact unitKernelDeflateSection_zero 1 ha1
  have ha2 :
      HasUnitKernelSectionDivisibility (K := K) 2 a1 := by
    rw [ha1zero]
    simp [HasUnitKernelSectionDivisibility,
      zeroPolynomialSection]
  have hb2 :
      HasUnitKernelSectionDivisibility (K := K) 2 b1 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 bS hb1 (i := (2 : Fin 4)) (by decide)]
    exact hbSX 2 (by decide)
  let a2 := unitKernelDeflateSection (K := K) 2 a1 ha2
  let b2 := unitKernelDeflateSection (K := K) 2 b1 hb2
  have ha2zero :
      a2 = zeroPolynomialSection (K := K) := by
    dsimp [a2]
    exact
      unitKernelDeflateSection_eq_zero_of_eq_zero
        2 a1 ha2 ha1zero
  have ha3 :
      HasUnitKernelSectionDivisibility (K := K) 3 a2 := by
    rw [ha2zero]
    simp [HasUnitKernelSectionDivisibility,
      zeroPolynomialSection]
  have hb3 :
      HasUnitKernelSectionDivisibility (K := K) 3 b2 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b2]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 2 b1 hb2 (i := (3 : Fin 4)) (by decide)]
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 bS hb1 (i := (3 : Fin 4)) (by decide)]
    exact hbSX 3 (by decide)
  let aT :=
    unitTransverseDeflateSection
      (K := K)
      (zeroPolynomialSection (K := K))
      ha1 ha2 ha3
  let bT :=
    unitTransverseDeflateSection
      (K := K) bS hb1 hb2 hb3
  let I := unitTransverseInflateFamily S
  have hIhom :
      I.IsHomogeneous D := by
    dsimp [I]
    exact
      unitTransverseInflateFamily_isHomogeneous
        S hShom
  have hIdef :
      HasPolynomialFamilyHessianDefect
        (K := K) I (Delta + 6) := by
    dsimp [I]
    exact
      unitTransverseInflateFamily_hasHessianDefect_add_six
        S hSdef
  have hIcollRaw :
      HasPolynomialFamilyExactGradientCollision
        I aT bT := by
    dsimp [I, aT, bT]
    exact
      polynomialFamilyExactGradientCollision_unitTransverseInflate
        S
        (zeroPolynomialSection (K := K))
        bS
        ha1 hb1 ha2 hb2 ha3 hb3 hScoll
  have haT :
      aT = zeroPolynomialSection (K := K) := by
    dsimp [aT, unitTransverseDeflateSection]
    exact
      unitKernelDeflateSection_eq_zero_of_eq_zero
        3 a2 ha3 ha2zero
  have hIcoll :
      HasPolynomialFamilyExactGradientCollision
        I (zeroPolynomialSection (K := K)) bT := by
    rw [← haT]
    exact hIcollRaw
  have hbT0 :
      polynomialSectionSpecialPoint bT 0 = 1 := by
    have hzero :
        bT 0 = bS 0 := by
      dsimp [bT]
      exact
        unitTransverseDeflateSection_zeroCoordinate
          bS hb1 hb2 hb3
    simpa [polynomialSectionSpecialPoint, hzero] using hbS0
  let hcommon :=
    oddWSeparatedRightWall_transverseInflate_commonFactor_two
      P b hwall hnotCoeff hnoPrimitive hsection hb
      l hN hPdiv
  let R := commonParameterFactorFamily 2 I hcommon
  have hRhom :
      R.IsHomogeneous D :=
    commonParameterFactorFamily_isHomogeneous
      I hIhom hcommon
  have hbudget :
      4 * 2 ≤ Delta + 6 :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) 2 I hcommon (Delta + 6) hIdef
  have hDelta : 2 ≤ Delta := by
    omega
  have hRdefRaw :=
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (K := K)
      2 I hcommon (Delta + 6) hIdef
  have hsub :
      Delta + 6 - 4 * 2 = Delta - 2 := by
    omega
  have hRdef :
      HasPolynomialFamilyHessianDefect
        (K := K) R (Delta - 2) := by
    dsimp [R]
    rw [hsub] at hRdefRaw
    exact hRdefRaw
  have hRcoll :
      HasPolynomialFamilyExactGradientCollision
        R (zeroPolynomialSection (K := K)) bT :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      2 I hcommon
      (zeroPolynomialSection (K := K)) bT hIcoll
  let R' := pointedShearNormalisedFamily R bT
  let b' := pointedShearNormalisedSection bT
  refine
    ⟨Delta - 2, by omega, R', b', ?_, ?_, ?_, ?_⟩
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_isHomogeneous
        R bT hRhom
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_preservesHessianDefect
        R bT hRdef
  · dsimp [R', b']
    exact
      pointedShearNormalisedFamily_preservesExactCollision
        R bT hRcoll
  · dsimp [b']
    exact
      pointedShearNormalisedSection_specialPoint
        bT hbT0

/-! -----------------------------------------------------------------------
  Every separated right wall descends
------------------------------------------------------------------------ -/

/-- Every natural number has an even or odd double normal form. -/
theorem nat_double_or_double_add_one
    (n : ℕ) :
    (∃ m : ℕ, n = 2 * m) ∨
      (∃ l : ℕ, n = 2 * l + 1) := by
  induction n with
  | zero =>
      exact Or.inl ⟨0, by omega⟩
  | succ n ih =>
      rcases ih with ⟨m, hm⟩ | ⟨l, hl⟩
      · exact Or.inr ⟨m, by omega⟩
      · exact Or.inl ⟨l + 1, by omega⟩

/-- Every nonzero transverse wall is either ten-aligned, or is the unique
odd-`w` arithmetic case. -/
theorem separatedRightWall_tenAligned_or_oddW
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b) :
    (∃ m : ℕ,
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b
          (Classical.choose hsep) =
        10 * m) ∨
    (∃ l : ℕ,
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b
          (Classical.choose hsep) =
        5 * (2 * l + 1) ∧
      alignedSmithSectionWallStep (3 : Fin 4) (b 3) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b
          (Classical.choose hsep)) := by
  classical
  let hwall := Classical.choose hsep
  have hdata := Classical.choose_spec hsep
  have hsection := hdata.2.2
  rcases
      mem_alignedSmithSectionWalls_exists_coordinate
        b hsection with
    ⟨i, hi0, hine, hstep⟩
  by_cases hi3 : i = (3 : Fin 4)
  · subst i
    have hwstep :
        alignedSmithSectionWallStep (3 : Fin 4) (b 3) =
          alignedSmithGenuineFirstWall
            P (zeroPolynomialSection (K := K)) b hwall :=
      hstep
    have hstep' := hstep
    simp [alignedSmithSectionWallStep] at hstep'
    rcases
        nat_double_or_double_add_one
          (sectionCoordinateParameterOrder (b 3)) with
      heven | hodd
    · rcases heven with ⟨m, hm⟩
      left
      refine ⟨m, ?_⟩
      dsimp [hwall]
      omega
    · rcases hodd with ⟨l, hl⟩
      right
      refine ⟨l, ?_, ?_⟩
      · dsimp [hwall]
        omega
      · simpa [hwall] using hwstep
  · have hstep' := hstep
    simp [alignedSmithSectionWallStep, hi3] at hstep'
    left
    refine
      ⟨sectionCoordinateParameterOrder (b i), ?_⟩
    dsimp [hwall]
    omega

/-- **Main scale-descent theorem.**

Every separated right Smith section wall produces an actual homogeneous
canonical exact-collision family over the *original* parameter ring with a
strictly smaller Hessian determinant defect.

There is no remaining scale or section-wall alternative. -/
theorem separatedRightSmithWall_strictCanonicalGeometricRestart
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasCanonicalStrictGeometricDefectRestart
      (K := K) D Delta := by
  classical
  let hwall := Classical.choose hsep
  have hdata := Classical.choose_spec hsep
  have hnoPrimitive := hdata.1
  have hnotCoeff := hdata.2.1
  have hsection := hdata.2.2
  rcases
      separatedRightWall_tenAligned_or_oddW
        P b hsep with
    hten | hodd
  · rcases hten with ⟨m, hN⟩
    exact
      tenAlignedSeparatedRightWall_strictCanonicalRestart
        P hP b hwall hnotCoeff hnoPrimitive
        hsection hdef hcoll hb m
        (by simpa [hwall] using hN)
  · rcases hodd with ⟨l, hN, hwstep⟩
    exact
      oddWSeparatedRightWall_strictCanonicalRestart
        P hP b hwall hnotCoeff hnoPrimitive
        hsection hdef hcoll hb l
        (by simpa [hwall] using hN)
        (by simpa [hwall] using hwstep)

/-- **Closed zero-slope geometric step.**

The green zero-section Smith dispatcher from Phase 93.72, the coupled-wall
closure from Phase 93.71, the pointed shear from Phase 93.73, and the scale
descent above combine to leave exactly two outcomes:

* canonical local repair/terminal;
* strict canonical geometric defect restart.

This is the zero-slope theorem required by the final global recursion. -/
theorem alignedSmith_zeroSection_closedGeometricStep
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity ∨
      HasCanonicalStrictGeometricDefectRestart
        (K := K) D Delta := by
  rcases
      alignedSmith_zeroSection_geometricDispatcher
        P hP b hdef hD hcoll hb complexity with
    hlocal | hwall
  · exact Or.inl hlocal
  · exact
      Or.inr
        (separatedRightSmithWall_strictCanonicalGeometricRestart
          P hP b hwall hdef hcoll hb)

end

end HC4.Valuation
