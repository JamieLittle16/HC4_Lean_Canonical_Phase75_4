import HC4.Valuation.AlignedSmithEndpoint
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Primitive Smith endpoints

Phase 93.68 removes the global scale problem and leaves a finite endpoint
dichotomy:

* a genuine coefficient/section first wall; or
* no wall, axial moving sections, and a supported zero Smith derivative.

This file turns the two potential-side alternatives into actual
special-fibre Smith-minimal data.

The key device is exact coefficient primitivity.

For a source coefficient

    c = X^v * u,      u(0) != 0,

ramification by twenty gives

    c(X^20) = X^(20v) * u(X^20)

with the primitive factor still nonzero at zero.

At a coefficient wall the Smith numerator/multiplier exponents cancel
exactly, so the transformed coefficient is precisely `u(X^20)`.  Hence it
survives on the transformed special fibre, with negative Smith derivative,
which is enough for symmetric Smith minimality.

In the no-wall branch choose, among all zero-Smith-derivative source
monomials, one of minimal exact parameter order `m`.  Take one aligned
Smith move with

    N = 10*m.

Every transformed coefficient then has at least `20*m` residual parameter
order:

* zero-grade coefficients have source order at least `m`;
* positive-grade coefficients have derivative at least `2`, so the Smith
  motion alone contributes at least `20*m`.

Extract the common factor `X^(20*m)`.  The chosen minimal zero-grade
coefficient becomes primitive and survives on the resulting special fibre.
Thus the no-wall branch also lands at a genuine symmetric-minimal special
fibre in one finite move.

The file also proves the exact arbitrary common-factor Hessian defect law

    Delta -> Delta - 4*n

and transports homogeneity/collision through the no-wall normalization.

For section walls we prove the corresponding transformed marked coordinate
has nonzero special value.  This is the exact residual geometric datum; it
is intentionally not identified with a terminal weight certificate without
a separate boundary theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Ramification preserves primitive constant terms -/

/-- The polynomial ramification hom is Mathlib's `expand`. -/
theorem parameterRamificationHom_eq_expand
    (D : ℕ)
    (c : Polynomial K) :
    parameterRamificationHom (K := K) D c =
      (Polynomial.expand K D) c := by
  rw [parameterRamificationHom_apply]
  exact
    (Polynomial.expand_eq_comp_X_pow
      (R := K) D (f := c)).symm

/-- Ramification by a positive index is injective on polynomials. -/
theorem parameterRamificationHom_ne_zero_of_pos
    (D : ℕ)
    (hD : 0 < D)
    {c : Polynomial K}
    (hc : c ≠ 0) :
    parameterRamificationHom (K := K) D c ≠ 0 := by
  rw [parameterRamificationHom_eq_expand]
  exact
    (Polynomial.expand_ne_zero (R := K) hD).2 hc

/-- Positive ramification preserves the constant coefficient. -/
theorem constantCoeff_parameterRamificationHom
    (D : ℕ)
    (hD : 0 < D)
    (c : Polynomial K) :
    Polynomial.constantCoeff
        (parameterRamificationHom (K := K) D c) =
      Polynomial.constantCoeff c := by
  rw [parameterRamificationHom_eq_expand]
  change
    ((Polynomial.expand K D) c).coeff 0 =
      c.coeff 0
  rw [Polynomial.coeff_expand (R := K) hD c 0]
  simp

/-- In particular an exact primitive part stays primitive after the aligned
ramification. -/
theorem alignedRamification_primitive_constantCoeff_ne_zero
    (c : Polynomial K)
    (hc : c ≠ 0) :
    Polynomial.constantCoeff
        (parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart c hc)) ≠ 0 := by
  rw [constantCoeff_parameterRamificationHom
    alignedSmithRamificationIndex
    alignedSmithRamificationIndex_pos]
  exact
    polynomialParameterPrimitivePart_constantCoeff_ne_zero
      c hc

/-! ## Source support survives ramification -/

/-- A source monomial remains in support after the positive aligned
ramification. -/
theorem mem_parameterRamificationFamily_support_of_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    d ∈
      (parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P).support := by
  apply MvPolynomial.mem_support_iff.mpr
  unfold parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  apply
    parameterRamificationHom_ne_zero_of_pos
      alignedSmithRamificationIndex
      alignedSmithRamificationIndex_pos
  exact MvPolynomial.mem_support_iff.mp hd

/-! ## Homogeneity is preserved by coefficient-only operations -/

/-- Integral Smith normalisation preserves ordinary source homogeneity. -/
theorem integralSmithConformalFamily_isHomogeneous
    {D theta1 theta2 : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    (integralSmithConformalFamily
      theta1 theta2 P hdiv).IsHomogeneous D := by
  intro d hdQ
  have hdQsupport :
      d ∈
        (integralSmithConformalFamily
          theta1 theta2 P hdiv).support :=
    MvPolynomial.mem_support_iff.mpr hdQ
  have hdPsupport :
      d ∈ P.support :=
    support_integralSmithConformalFamily_subset
      theta1 theta2 P hdiv hdQsupport
  exact hP (MvPolynomial.mem_support_iff.mp hdPsupport)

/-- Common parameter-factor extraction preserves ordinary source
homogeneity. -/
theorem commonParameterFactorFamily_isHomogeneous
    {D n : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (hdiv : HasCommonParameterFactor n P) :
    (commonParameterFactorFamily n P hdiv).IsHomogeneous D := by
  intro d hdQ
  have hdQsupport :
      d ∈ (commonParameterFactorFamily n P hdiv).support :=
    MvPolynomial.mem_support_iff.mpr hdQ
  have hdPsupport :
      d ∈ P.support :=
    support_commonParameterFactorFamily_subset
      n P hdiv hdQsupport
  exact hP (MvPolynomial.mem_support_iff.mp hdPsupport)

/-- Taking the polynomial-family special fibre preserves ordinary
homogeneity. -/
theorem polynomialFamilySpecialFiber_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D) :
    (polynomialFamilySpecialFiber P).IsHomogeneous D := by
  unfold polynomialFamilySpecialFiber
  exact hP.map Polynomial.constantCoeff

/-! ## Arbitrary common-factor exact Hessian defect law -/

/-- **Exact four-variable defect after extracting `X^n`.**

This generalises the Phase 93.61 `n=1` theorem. -/
theorem commonParameterFactor_hasHessianDefect_sub_four_mul
    (n : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor n P)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (commonParameterFactorFamily n P hdiv)
      (Delta - 4 * n) := by
  let Q :=
    commonParameterFactorFamily n P hdiv
  have hle :
      4 * n ≤ Delta :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) n P hdiv Delta hdef
  have hfactor :
      P =
        MvPolynomial.C (Polynomial.X ^ n) * Q :=
    commonParameterFactorFamily_factorisation
      n P hdiv
  have hdet :=
    congrArg HC4.Polynomial.hessianDeterminant
      hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hdef] at hdet
  have hexp :
      n * 4 + (Delta - 4 * n) = Delta := by
    omega
  have hpow :
      (MvPolynomial.C (Polynomial.X ^ n) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C
          (Polynomial.X ^ (Delta - 4 * n)) =
      MvPolynomial.C
        (Polynomial.X ^ Delta) := by
    rw [← MvPolynomial.C_pow,
        ← MvPolynomial.C_mul]
    congr 1
    rw [← pow_mul]
    rw [← pow_add, hexp]
  have hcancel :
      (MvPolynomial.C (Polynomial.X ^ n) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C
          (Polynomial.X ^ (Delta - 4 * n)) =
      (MvPolynomial.C (Polynomial.X ^ n) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        HC4.Polynomial.hessianDeterminant Q := by
    calc
      _ =
        MvPolynomial.C
          (Polynomial.X ^ Delta) := hpow
      _ =
        (MvPolynomial.C (Polynomial.X ^ n) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
          HC4.Polynomial.hessianDeterminant Q := by
            simpa [Q] using hdet
  have hfac :
      (MvPolynomial.C (Polynomial.X ^ n) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 ≠ 0 := by
    exact
      pow_ne_zero 4
        (MvPolynomial.C_ne_zero.mpr
          (pow_ne_zero n Polynomial.X_ne_zero))
  have hz :
      (MvPolynomial.C (Polynomial.X ^ n) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        (MvPolynomial.C
            (Polynomial.X ^ (Delta - 4 * n)) -
          HC4.Polynomial.hessianDeterminant Q) = 0 := by
    rw [mul_sub, hcancel, sub_self]
  have hsub :
      MvPolynomial.C
          (Polynomial.X ^ (Delta - 4 * n)) -
        HC4.Polynomial.hessianDeterminant Q = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfac hzero)
    · exact hzero
  exact (sub_eq_zero.mp hsub).symm

/-! ## Exact wall coefficient survival -/

/-- Exact ramified factorisation of a supported source coefficient into its
aligned parameter power and ramified primitive part. -/
theorem alignedRamification_sourceCoefficient_factorisation
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let c := MvPolynomial.coeff d P
    let hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    let v := polynomialParameterOrder c hc
    let u := polynomialParameterPrimitivePart c hc
    MvPolynomial.coeff d
        (parameterRamificationFamily
          (K := K)
          alignedSmithRamificationIndex P) =
      Polynomial.X ^
          (alignedSmithRamificationIndex * v) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex u := by
  dsimp
  unfold parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  have hprimitive :=
    polynomialParameterPrimitivePart_spec
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)
  calc
    parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex
        (MvPolynomial.coeff d P) =
      parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex
        (Polynomial.X ^
            polynomialParameterOrder
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd) *
          polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) :=
      congrArg
        (parameterRamificationHom
          (K := K) alignedSmithRamificationIndex)
        hprimitive
    _ =
      Polynomial.X ^
          (alignedSmithRamificationIndex *
            polynomialParameterOrder
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
      rw [map_mul, parameterRamificationHom_X_pow]

/-- At aligned residual order zero, the Smith quotient coefficient is
exactly the ramified primitive part. -/
theorem alignedSmith_zeroResidual_quotient_eq_ramifiedPrimitive
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (N : ℕ)
    (hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hzero :
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        N
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) = 0) :
    let Pram :=
      parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P
    let hsmith :=
      alignedSmith_coefficientDivisibility_of_nonnegative
        (K := K) P N hlegal
    smithConformalCoefficientQuotient
        (2 * N) (2 * N) Pram hsmith d =
      parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex
        (polynomialParameterPrimitivePart
          (MvPolynomial.coeff d P)
          (MvPolynomial.mem_support_iff.mp hd)) := by
  dsimp
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Pram]
    exact
      mem_parameterRamificationFamily_support_of_mem
        P hd
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam
  have hfactor :=
    alignedRamification_sourceCoefficient_factorisation
      P hd
  have hdelta :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  let v := smithFamilyCoefficientOrder P d
  have hv :
      v =
        polynomialParameterOrder
          (MvPolynomial.coeff d P)
          (MvPolynomial.mem_support_iff.mp hd) := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_eq P hd
  have hzeroV := hzero
  change
    alignedSmithCoefficientValue
      v N
      (smithSeparatorDelta 1 1
        (smithAxisProjection d)) = 0
    at hzeroV
  have hNat :
      N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex * v =
        4 * N := by
    unfold alignedSmithCoefficientValue at hzeroV
    rw [hdelta] at hzeroV
    change
      (alignedSmithRamificationIndex : ℤ) * (v : ℤ) +
          (N : ℤ) *
            ((smithConformalRawExponent 2 2 d : ℤ) - 4) =
        0
      at hzeroV
    have hz :
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) * (v : ℤ) =
          (4 : ℤ) * (N : ℤ) := by
      nlinarith
    exact_mod_cast hz
  have heq :
      Polynomial.X ^ (4 * N) *
          parameterRamificationHom
            (K := K)
            alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) =
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    calc
      _ =
        Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d +
              alignedSmithRamificationIndex * v) *
          parameterRamificationHom
            (K := K)
            alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
                rw [hNat]
      _ =
        smithConformalCoefficientFactor
              (K := K) (2 * N) (2 * N) d *
            MvPolynomial.coeff d Pram := by
              rw [smithConformalCoefficientFactor_two_mul]
              have hfactor' :
                  MvPolynomial.coeff d Pram =
                    Polynomial.X ^
                        (alignedSmithRamificationIndex * v) *
                      parameterRamificationHom
                        (K := K)
                        alignedSmithRamificationIndex
                        (polynomialParameterPrimitivePart
                          (MvPolynomial.coeff d P)
                          (MvPolynomial.mem_support_iff.mp hd)) := by
                simpa [Pram, hv] using hfactor
              rw [hfactor']
              rw [pow_add]
              ring
      _ =
        smithConformalMultiplier
              (K := K) (2 * N) (2 * N) *
            smithConformalCoefficientQuotient
              (2 * N) (2 * N) Pram hsmith d := hspec
      _ =
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
              simp [smithConformalMultiplier,
                smithConformalMultiplierExponent_two_mul]
  exact
    (polynomial_X_pow_mul_cancel
      (K := K) (4 * N) heq).symm

/-- Hence a zero-residual source coefficient survives on the transformed
special fibre. -/
theorem alignedSmith_zeroResidual_mem_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (N : ℕ)
    (hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hzero :
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        N
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) = 0) :
    let Pram :=
      parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P
    let hsmith :=
      alignedSmith_coefficientDivisibility_of_nonnegative
        (K := K) P N hlegal
    let Q :=
      integralSmithConformalFamily
        (2 * N) (2 * N) Pram hsmith
    d ∈ (polynomialFamilySpecialFiber Q).support := by
  dsimp
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Pram]
    exact
      mem_parameterRamificationFamily_support_of_mem
        P hd
  have hq :=
    alignedSmith_zeroResidual_quotient_eq_ramifiedPrimitive
      P N hlegal hd hzero
  have hconst :
      Polynomial.constantCoeff
        (MvPolynomial.coeff d Q) ≠ 0 := by
    rw [coeff_integralSmithConformalFamily_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam]
    rw [hq]
    exact
      alignedRamification_primitive_constantCoeff_ne_zero
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd)
  have hdQ :
      d ∈ Q.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply hconst
    rw [hz]
    simp
  exact
    (mem_polynomialFamilySpecialFiber_support_iff
      Q d).2 ⟨hdQ, hconst⟩

/-! ## Coefficient wall -> symmetric minimality -/

/-- A coefficient genuine first wall gives an actual negative-grade monomial
on the transformed special fibre. -/
theorem genuineCoefficientWall_specialFiber_has_negativeGrade
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hcoeff :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P) :
    let N := alignedSmithGenuineFirstWall P a b hwall
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall
    ∃ d ∈ (polynomialFamilySpecialFiber Q).support,
      smithSeparatorDelta 1 1
        (smithAxisProjection d) < 0 := by
  dsimp
  let N := alignedSmithGenuineFirstWall P a b hwall
  rcases
      alignedSmithCoefficientWall_member_value_zero
        P hcoeff with
    ⟨d, hd, hneg, hzero⟩
  have hlegal :
      ∀ e ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P e)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection e)) := by
    intro e he
    dsimp [N]
    exact
      alignedSmithGenuineFirstWall_coefficient_nonnegative
        P a b hwall he
  have hspecial :=
    alignedSmith_zeroResidual_mem_specialFiber
      P N hlegal hd hzero
  have hspecial' :
      d ∈
        (polynomialFamilySpecialFiber
          (alignedSmithGenuineFirstWallFamily
            (K := K) P a b hwall)).support := by
    simpa [alignedSmithGenuineFirstWallFamily, N] using hspecial
  exact ⟨d, hspecial', hneg⟩

/-- Therefore a coefficient genuine first wall is symmetric-Smith minimal
with old minimum/base zero. -/
theorem genuineCoefficientWall_specialFiber_symmetricMinimal
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hcoeff :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P) :
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber Q))
      0
      (fun _ => (0 : ℤ)) := by
  dsimp
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P a b hwall
  rcases
      genuineCoefficientWall_specialFiber_has_negativeGrade
        P a b hwall hcoeff with
    ⟨d, hdF, hneg⟩
  refine
    ⟨smithAxisProjection d, ?_, ?_⟩
  · unfold smithProjectedSupport
    apply Finset.mem_image.mpr
    exact ⟨d, hdF, rfl⟩
  · unfold smithIntegralSeparatorTilt
    unfold finiteIntegralRescaledTilt
    unfold smithRescaledOldMinimum
    simp
    exact le_of_lt hneg

/-! ## Section wall -> nonzero transformed special coordinate -/

/-- Exact ramified factorisation of a nonzero section coordinate. -/
theorem alignedRamification_sectionCoordinate_factorisation
    (c : Polynomial K)
    (hc : c ≠ 0) :
    parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex c =
      Polynomial.X ^
          (alignedSmithRamificationIndex *
            sectionCoordinateParameterOrder c) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            c hc) := by
  have horder :
      sectionCoordinateParameterOrder c =
        polynomialParameterOrder c hc := by
    unfold sectionCoordinateParameterOrder
    simp [hc]
  have hprimitive :=
    polynomialParameterPrimitivePart_spec c hc
  calc
    parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex c =
      parameterRamificationHom
        (K := K)
        alignedSmithRamificationIndex
        (Polynomial.X ^
            polynomialParameterOrder c hc *
          polynomialParameterPrimitivePart c hc) :=
      congrArg
        (parameterRamificationHom
          (K := K) alignedSmithRamificationIndex)
        hprimitive
    _ =
      Polynomial.X ^
          (alignedSmithRamificationIndex *
            polynomialParameterOrder c hc) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart c hc) := by
      rw [map_mul, parameterRamificationHom_X_pow]
    _ =
      Polynomial.X ^
          (alignedSmithRamificationIndex *
            sectionCoordinateParameterOrder c) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart c hc) := by
      rw [horder]

/-- At a section wall the transformed section coordinate is primitive, hence
has nonzero special value. -/
theorem alignedSmith_sectionWall_transformed_constantCoeff_ne_zero
    (a : Fin 4 → Polynomial K)
    (N : ℕ)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex a))
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hine : a i ≠ 0)
    (hwall :
      (i = 3 ∧
        alignedSmithSectionValueFour
          (sectionCoordinateParameterOrder (a i))
          N = 0) ∨
      (i ≠ 3 ∧
        alignedSmithSectionValueTwo
          (sectionCoordinateParameterOrder (a i))
          N = 0)) :
    Polynomial.constantCoeff
      (integralSmithConformalSection
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex a)
        hdiv i) ≠ 0 := by
  let q :=
    integralSmithConformalSection
      (2 * N) (2 * N)
      (parameterRamificationSection
        (K := K)
        alignedSmithRamificationIndex a)
      hdiv i
  have hspec :=
    Classical.choose_spec (hdiv i)
  have hram :=
    alignedRamification_sectionCoordinate_factorisation
      (a i) hine
  have hexp :
      smithConformalSourceExponent (2 * N) (2 * N) i =
        alignedSmithRamificationIndex *
          sectionCoordinateParameterOrder (a i) := by
    fin_cases i <;>
      simp [smithConformalSourceExponent,
        alignedSmithSectionValueTwo,
        alignedSmithSectionValueFour,
        alignedSmithRamificationIndex] at hi0 hwall ⊢ <;>
      omega
  have heq :
      Polynomial.X ^
          (smithConformalSourceExponent
            (2 * N) (2 * N) i) *
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (a i) hine) =
      Polynomial.X ^
          (smithConformalSourceExponent
            (2 * N) (2 * N) i) * q := by
    calc
      _ =
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (a i) := by
            rw [hram, ← hexp]
      _ =
        (parameterRamificationSection
          (K := K)
          alignedSmithRamificationIndex a) i := rfl
      _ =
        smithConformalDerivativeCoefficient
            (K := K) (2 * N) (2 * N) i * q := by
              simpa [q] using hspec
      _ =
        Polynomial.X ^
            (smithConformalSourceExponent
              (2 * N) (2 * N) i) * q := by
              rfl
  have hq :
      q =
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (a i) hine) := by
    exact
      (polynomial_X_pow_mul_cancel
        (K := K)
        (smithConformalSourceExponent
          (2 * N) (2 * N) i)
        heq).symm
  change Polynomial.constantCoeff q ≠ 0
  rw [hq]
  exact
    alignedRamification_primitive_constantCoeff_ne_zero
      (a i) hine

/-- A genuine left-section wall exposes a nonzero transverse special
coordinate on the transformed left marked section. -/
theorem genuineLeftSectionWall_exposes_nonzero_specialCoordinate
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hsection :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls a) :
    ∃ i : Fin 4,
      i ≠ 0 ∧
      Polynomial.constantCoeff
        (alignedSmithGenuineFirstWallSectionLeft
          (K := K) P a b hwall i) ≠ 0 := by
  rcases
      alignedSmithSectionWall_member_value_zero
        a hsection with
    ⟨i, hi0, hine, hiwall⟩
  refine ⟨i, hi0, ?_⟩
  unfold alignedSmithGenuineFirstWallSectionLeft
  exact
    alignedSmith_sectionWall_transformed_constantCoeff_ne_zero
      a
      (alignedSmithGenuineFirstWall P a b hwall)
      (alignedSmithGenuineFirstWall_integralSection_left
        P a b hwall)
      hi0 hine hiwall

/-- A genuine right-section wall exposes a nonzero transverse special
coordinate on the transformed right marked section. -/
theorem genuineRightSectionWall_exposes_nonzero_specialCoordinate
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hsection :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls b) :
    ∃ i : Fin 4,
      i ≠ 0 ∧
      Polynomial.constantCoeff
        (alignedSmithGenuineFirstWallSectionRight
          (K := K) P a b hwall i) ≠ 0 := by
  rcases
      alignedSmithSectionWall_member_value_zero
        b hsection with
    ⟨i, hi0, hine, hiwall⟩
  refine ⟨i, hi0, ?_⟩
  unfold alignedSmithGenuineFirstWallSectionRight
  exact
    alignedSmith_sectionWall_transformed_constantCoeff_ne_zero
      b
      (alignedSmithGenuineFirstWall P a b hwall)
      (alignedSmithGenuineFirstWall_integralSection_right
        P a b hwall)
      hi0 hine hiwall

/-! ## Zero-grade support and minimal exact order -/

/-- Source monomials of symmetric Smith derivative exactly zero. -/
noncomputable def zeroSmithSourceSupport
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset (Fin 4 →₀ ℕ) := by
  classical
  exact
    P.support.filter
      (fun d =>
        smithSeparatorDelta 1 1
          (smithAxisProjection d) = 0)

theorem mem_zeroSmithSourceSupport
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ} :
    d ∈ zeroSmithSourceSupport P ↔
      d ∈ P.support ∧
        smithSeparatorDelta 1 1
          (smithAxisProjection d) = 0 := by
  classical
  simp [zeroSmithSourceSupport]

theorem zeroSmithSourceSupport_nonempty_of_noGenuineWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    (zeroSmithSourceSupport P).Nonempty := by
  rcases
      exists_zeroSmithDerivative_of_noGenuineWall
        P a b Delta hdef hnone with
    ⟨d, hd, hz⟩
  exact
    ⟨d,
      (mem_zeroSmithSourceSupport P).2
        ⟨hd, hz⟩⟩

/-- Minimal exact parameter order among zero-grade source monomials. -/
noncomputable def minimalZeroSmithParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : (zeroSmithSourceSupport P).Nonempty) :
    ℕ :=
  ((zeroSmithSourceSupport P).image
      (smithFamilyCoefficientOrder P)).min'
    (hne.image _)

theorem minimalZeroSmithParameterOrder_mem_image
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : (zeroSmithSourceSupport P).Nonempty) :
    minimalZeroSmithParameterOrder P hne ∈
      (zeroSmithSourceSupport P).image
        (smithFamilyCoefficientOrder P) := by
  unfold minimalZeroSmithParameterOrder
  exact
    Finset.min'_mem _ (hne.image _)

/-- A zero-grade source monomial attaining the minimal exact order. -/
theorem exists_zeroSmithSource_minimalOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : (zeroSmithSourceSupport P).Nonempty) :
    ∃ d : Fin 4 →₀ ℕ,
      d ∈ P.support ∧
      smithSeparatorDelta 1 1
          (smithAxisProjection d) = 0 ∧
      smithFamilyCoefficientOrder P d =
        minimalZeroSmithParameterOrder P hne := by
  have hmem :=
    minimalZeroSmithParameterOrder_mem_image P hne
  rcases Finset.mem_image.mp hmem with
    ⟨d, hd0, horder⟩
  have hd :=
    (mem_zeroSmithSourceSupport P).1 hd0
  exact
    ⟨d, hd.1, hd.2, horder⟩

/-- Every zero-grade source coefficient has order at least the selected
minimum. -/
theorem minimalZeroSmithParameterOrder_le
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : (zeroSmithSourceSupport P).Nonempty)
    {d : Fin 4 →₀ ℕ}
    (hd0 : d ∈ zeroSmithSourceSupport P) :
    minimalZeroSmithParameterOrder P hne ≤
      smithFamilyCoefficientOrder P d := by
  unfold minimalZeroSmithParameterOrder
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨d, hd0, rfl⟩

/-! ## No-wall one-shot primitive normalisation -/

/-- Integer Smith step used to expose a primitive zero-grade coefficient. -/
def noWallPrimitiveSmithStep
    (m : ℕ) : ℕ :=
  10 * m

/-- In the no-wall branch, every source coefficient is legal at the
primitive-exposure step. -/
theorem noWallPrimitiveSmithStep_coefficient_nonnegative
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (m : ℕ)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    0 ≤
      alignedSmithCoefficientValue
        (smithFamilyCoefficientOrder P d)
        (noWallPrimitiveSmithStep m)
        (smithSeparatorDelta 1 1
          (smithAxisProjection d)) := by
  exact
    alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
      (smithFamilyCoefficientOrder P d)
      (noWallPrimitiveSmithStep m)
      _
      (no_negativeSmithDerivative_of_noGenuineWall
        P a b hnone d hd)

/-- At the primitive-exposure step every normalised coefficient has at
least `20*m` residual parameter order. -/
theorem noWallPrimitiveSmithStep_residual_ge
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hne : (zeroSmithSourceSupport P).Nonempty)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let m := minimalZeroSmithParameterOrder P hne
    let N := noWallPrimitiveSmithStep m
    4 * N + alignedSmithRamificationIndex * m ≤
      N * smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder P d := by
  dsimp
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  have hnonneg :=
    no_negativeSmithDerivative_of_noGenuineWall
      P a b hnone d hd
  by_cases hz :
      smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0
  · have hd0 :
      d ∈ zeroSmithSourceSupport P :=
      (mem_zeroSmithSourceSupport P).2 ⟨hd, hz⟩
    have hmle :=
      minimalZeroSmithParameterOrder_le
        P hne hd0
    have hraw :
        smithConformalRawExponent 2 2 d = 4 := by
      have hrel :=
        smithSeparatorDelta_projection_eq_raw_sub_four d
      rw [hz] at hrel
      exact_mod_cast (by omega : (smithConformalRawExponent 2 2 d : ℤ) = 4)
    dsimp [N, m, noWallPrimitiveSmithStep]
    rw [hraw]
    norm_num [alignedSmithRamificationIndex]
    omega
  · have hdelta2 :=
      smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
        (smithAxisProjection d) hnonneg hz
    have hrel :=
      smithSeparatorDelta_projection_eq_raw_sub_four d
    have hraw6 :
        6 ≤ smithConformalRawExponent 2 2 d := by
      rw [hrel] at hdelta2
      exact_mod_cast (by omega :
        (6 : ℤ) ≤
          (smithConformalRawExponent 2 2 d : ℤ))
    dsimp [N, m, noWallPrimitiveSmithStep]
    norm_num [alignedSmithRamificationIndex]
    nlinarith

/-- Generic margin theorem: if every Smith numerator has `r` powers beyond
the multiplier, the integral Smith family has common factor `X^r`. -/
theorem alignedSmith_commonFactor_of_margin
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (N r : ℕ)
    (hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)))
    (hmargin :
      ∀ d ∈ P.support,
        4 * N + r ≤
          N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex *
              smithFamilyCoefficientOrder P d) :
    let Pram :=
      parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P
    let hsmith :=
      alignedSmith_coefficientDivisibility_of_nonnegative
        (K := K) P N hlegal
    let Q :=
      integralSmithConformalFamily
        (2 * N) (2 * N) Pram hsmith
    HasCommonParameterFactor r Q := by
  dsimp
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
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
  have htotal :
      Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) ∣
        smithConformalCoefficientFactor
            (K := K) (2 * N) (2 * N) d *
          MvPolynomial.coeff d Pram := by
    rcases hramdiv with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [smithConformalCoefficientFactor_two_mul]
    rw [hu]
    calc
      _ =
        (Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d) *
          Polynomial.X ^
            (alignedSmithRamificationIndex * v)) * u := by
              ring
      _ =
        Polynomial.X ^
            (N * smithConformalRawExponent 2 2 d +
              alignedSmithRamificationIndex * v) * u := by
                rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ (4 * N + r) : Polynomial K) ∣
        Polynomial.X ^
          (N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex * v) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ (hmargin d hdP)
  have hbig :=
    dvd_trans hsmall htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam
  have hquot :
      (Polynomial.X ^ (4 * N + r) : Polynomial K) ∣
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    have hraw :
      (Polynomial.X ^ (4 * N + r) : Polynomial K) ∣
        smithConformalMultiplier (2 * N) (2 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
      rw [← hspec]
      exact hbig
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent_two_mul] using hraw
  have hq :
      Polynomial.X ^ r ∣
        smithConformalCoefficientQuotient
          (2 * N) (2 * N) Pram hsmith d :=
    polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
      (K := K)
      (4 * N) r
      (smithConformalCoefficientQuotient
        (2 * N) (2 * N) Pram hsmith d)
      hquot
  rw [coeff_integralSmithConformalFamily_of_mem
    (2 * N) (2 * N) Pram hsmith hdRam]
  exact hq

/-- Concrete common factor in the no-wall primitive normalization. -/
theorem noWallPrimitiveSmithStep_commonFactor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hne : (zeroSmithSourceSupport P).Nonempty) :
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
    let Q :=
      integralSmithConformalFamily
        (2 * N) (2 * N) Pram hsmith
    HasCommonParameterFactor
      (alignedSmithRamificationIndex * m) Q := by
  dsimp
  apply
    alignedSmith_commonFactor_of_margin
      (K := K)
      P
      (noWallPrimitiveSmithStep
        (minimalZeroSmithParameterOrder P hne))
      (alignedSmithRamificationIndex *
        minimalZeroSmithParameterOrder P hne)
  · intro d hd
    exact
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone
        (minimalZeroSmithParameterOrder P hne)
        hd
  · intro d hd
    exact
      noWallPrimitiveSmithStep_residual_ge
        P a b Delta hdef hnone hne hd

/-- The chosen minimal zero-grade coefficient in the Smith family is
exactly `X^(20*m)` times a primitive ramified factor. -/
theorem noWall_minimalZeroSmith_coefficient_exact
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hne : (zeroSmithSourceSupport P).Nonempty) :
    ∃ d : Fin 4 →₀ ℕ,
      ∃ hd : d ∈ P.support,
        smithSeparatorDelta 1 1
            (smithAxisProjection d) = 0 ∧
        smithFamilyCoefficientOrder P d =
            minimalZeroSmithParameterOrder P hne ∧
        let m := minimalZeroSmithParameterOrder P hne
        let N := noWallPrimitiveSmithStep m
        let hlegal :
          ∀ e ∈ P.support,
            0 ≤
              alignedSmithCoefficientValue
                (smithFamilyCoefficientOrder P e)
                N
                (smithSeparatorDelta 1 1
                  (smithAxisProjection e)) :=
          fun e he =>
            noWallPrimitiveSmithStep_coefficient_nonnegative
              P a b hnone m he
        let Pram :=
          parameterRamificationFamily
            (K := K)
            alignedSmithRamificationIndex P
        let hsmith :=
          alignedSmith_coefficientDivisibility_of_nonnegative
            (K := K) P N hlegal
        let Q :=
          integralSmithConformalFamily
            (2 * N) (2 * N) Pram hsmith
        MvPolynomial.coeff d Q =
          Polynomial.X ^
              (alignedSmithRamificationIndex * m) *
            parameterRamificationHom
              (K := K)
              alignedSmithRamificationIndex
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d P)
                (MvPolynomial.mem_support_iff.mp hd)) := by
  rcases
      exists_zeroSmithSource_minimalOrder
        P hne with
    ⟨d, hd, hz, horder⟩
  refine ⟨d, hd, hz, horder, ?_⟩
  dsimp
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ e ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P e)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection e)) :=
    fun e he =>
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone m he
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Pram]
    exact
      mem_parameterRamificationFamily_support_of_mem
        P hd
  rw [coeff_integralSmithConformalFamily_of_mem
    (2 * N) (2 * N) Pram hsmith hdRam]
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (2 * N) (2 * N) Pram hsmith hdRam
  have hfactor :=
    alignedRamification_sourceCoefficient_factorisation
      P hd
  have hraw :
      smithConformalRawExponent 2 2 d = 4 := by
    have hrel :=
      smithSeparatorDelta_projection_eq_raw_sub_four d
    rw [hz] at hrel
    exact_mod_cast (by omega :
      (smithConformalRawExponent 2 2 d : ℤ) = 4)
  have hpm :
      polynomialParameterOrder
          (MvPolynomial.coeff d P)
          (MvPolynomial.mem_support_iff.mp hd) =
        m := by
    exact
      (smithFamilyCoefficientOrder_eq P hd).symm.trans
        horder
  have hfactor' :
      MvPolynomial.coeff d Pram =
        Polynomial.X ^
            (alignedSmithRamificationIndex * m) *
          parameterRamificationHom
            (K := K)
            alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [Pram, hpm] using hfactor
  have heq :
      Polynomial.X ^ (4 * N) *
          (Polynomial.X ^
              (alignedSmithRamificationIndex * m) *
            parameterRamificationHom
              (K := K)
              alignedSmithRamificationIndex
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d P)
                (MvPolynomial.mem_support_iff.mp hd))) =
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
    calc
      _ =
        smithConformalCoefficientFactor
              (K := K) (2 * N) (2 * N) d *
            MvPolynomial.coeff d Pram := by
              rw [smithConformalCoefficientFactor_two_mul,
                hraw, hfactor']
              ring
      _ =
        smithConformalMultiplier
              (K := K) (2 * N) (2 * N) *
            smithConformalCoefficientQuotient
              (2 * N) (2 * N) Pram hsmith d := hspec
      _ =
        Polynomial.X ^ (4 * N) *
          smithConformalCoefficientQuotient
            (2 * N) (2 * N) Pram hsmith d := by
              simp [smithConformalMultiplier,
                smithConformalMultiplierExponent_two_mul]
  exact
    (polynomial_X_pow_mul_cancel
      (K := K) (4 * N) heq).symm

/-! ## The primitive no-wall family -/

/-- Once-ramified, Smith-normalised, and common-factor-primitive family in
the no-wall branch. -/
noncomputable def noWallPrimitiveSmithFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    MvPolynomial (Fin 4) (Polynomial K) := by
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
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  exact
    commonParameterFactorFamily
      (alignedSmithRamificationIndex * m)
      Q hcommon

/-- The primitive no-wall family contains a zero-grade monomial on its
special fibre. -/
theorem noWallPrimitiveSmithFamily_specialFiber_zeroGrade
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    ∃ d ∈
        (polynomialFamilySpecialFiber
          (noWallPrimitiveSmithFamily
            P a b Delta hdef hnone)).support,
      smithSeparatorDelta 1 1
        (smithAxisProjection d) = 0 := by
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P a b Delta hdef hnone
  rcases
      noWall_minimalZeroSmith_coefficient_exact
        P a b Delta hdef hnone hne with
    ⟨d, hd, hz, horder, hexact⟩
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ e ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P e)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection e)) :=
    fun e he =>
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone m he
  let Pram :=
    parameterRamificationFamily
      (K := K)
      alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  let R :=
    commonParameterFactorFamily
      (alignedSmithRamificationIndex * m)
      Q hcommon
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Pram]
    exact
      mem_parameterRamificationFamily_support_of_mem
        P hd
  have hcoeffQ :
      MvPolynomial.coeff d Q =
        Polynomial.X ^
            (alignedSmithRamificationIndex * m) *
          parameterRamificationHom
            (K := K)
            alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [m, N, hlegal, Pram, hsmith, Q] using hexact
  have hprimitiveNe :
      parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) ≠ 0 := by
    intro hu
    apply
      alignedRamification_primitive_constantCoeff_ne_zero
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd)
    rw [hu]
    simp
  have hdQ :
      d ∈ Q.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [hcoeffQ]
    exact mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero)
      hprimitiveNe
  have hspec :=
    commonParameterCoefficientQuotient_spec_of_mem
      (alignedSmithRamificationIndex * m)
      Q hcommon hdQ
  have hquotEq :
      commonParameterCoefficientQuotient
          (alignedSmithRamificationIndex * m)
          Q hcommon d =
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
    apply
      polynomial_X_pow_mul_cancel
        (K := K)
        (alignedSmithRamificationIndex * m)
    calc
      Polynomial.X ^
            (alignedSmithRamificationIndex * m) *
          commonParameterCoefficientQuotient
            (alignedSmithRamificationIndex * m)
            Q hcommon d =
        MvPolynomial.coeff d Q := hspec.symm
      _ =
        Polynomial.X ^
            (alignedSmithRamificationIndex * m) *
          parameterRamificationHom
            (K := K)
            alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) :=
          hcoeffQ
  have hcoeffR :
      MvPolynomial.coeff d R =
        parameterRamificationHom
          (K := K)
          alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
    dsimp [R]
    rw [coeff_commonParameterFactorFamily_of_mem
      (alignedSmithRamificationIndex * m)
      Q hcommon hdQ]
    exact hquotEq
  have hconst :
      Polynomial.constantCoeff
        (MvPolynomial.coeff d R) ≠ 0 := by
    rw [hcoeffR]
    exact
      alignedRamification_primitive_constantCoeff_ne_zero
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd)
  have hdR :
      d ∈ R.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    apply hconst
    rw [hzero]
    simp
  have hdSpecial :
      d ∈ (polynomialFamilySpecialFiber R).support :=
    (mem_polynomialFamilySpecialFiber_support_iff
      R d).2 ⟨hdR, hconst⟩
  have hdSpecial' :
      d ∈
        (polynomialFamilySpecialFiber
          (noWallPrimitiveSmithFamily
            P a b Delta hdef hnone)).support := by
    simpa [noWallPrimitiveSmithFamily,
      hne, m, N, hlegal, Pram, hsmith, Q, hcommon, R] using
      hdSpecial
  exact ⟨d, hdSpecial', hz⟩

/-- Hence the primitive no-wall special fibre is symmetric-Smith minimal. -/
theorem noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber
          (noWallPrimitiveSmithFamily
            P a b Delta hdef hnone)))
      0
      (fun _ => (0 : ℤ)) := by
  rcases
      noWallPrimitiveSmithFamily_specialFiber_zeroGrade
        P a b Delta hdef hnone with
    ⟨d, hd, hz⟩
  refine ⟨smithAxisProjection d, ?_, ?_⟩
  · unfold smithProjectedSupport
    apply Finset.mem_image.mpr
    exact ⟨d, hd, rfl⟩
  · unfold smithIntegralSeparatorTilt
    unfold finiteIntegralRescaledTilt
    unfold smithRescaledOldMinimum
    simp [hz]

/-! ## Defect/collision/homogeneity of the primitive no-wall family -/

/-- Full-family homogeneity survives the no-wall primitive normalization. -/
theorem noWallPrimitiveSmithFamily_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    (noWallPrimitiveSmithFamily
      P a b Delta hdef hnone).IsHomogeneous D := by
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
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  have hPram : Pram.IsHomogeneous D := by
    dsimp [Pram]
    exact hP.map _
  have hQ : Q.IsHomogeneous D := by
    dsimp [Q]
    exact
      integralSmithConformalFamily_isHomogeneous
        Pram hPram hsmith
  unfold noWallPrimitiveSmithFamily
  dsimp only
  exact
    commonParameterFactorFamily_isHomogeneous
      Q hQ hcommon

/-- Exact defect of the primitive no-wall family. -/
theorem noWallPrimitiveSmithFamily_hasHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P a b Delta hdef hnone
    let m := minimalZeroSmithParameterOrder P hne
    HasPolynomialFamilyHessianDefect
      (K := K)
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone)
      (alignedSmithRamificationIndex * Delta -
        4 * (alignedSmithRamificationIndex * m)) := by
  dsimp
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
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  have hram :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Pram]
    exact
      parameterRamificationFamily_hasHessianDefect
        alignedSmithRamificationIndex Delta P hdef
  have hQ :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      integralSmithConformalFamily_preservesHessianDefect
        (2 * N) (2 * N)
        (alignedSmithRamificationIndex * Delta)
        Pram hsmith hram
  unfold noWallPrimitiveSmithFamily
  dsimp only
  exact
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (alignedSmithRamificationIndex * m)
      Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQ

/-- Exact collision survives the primitive no-wall normalization whenever
the moving sections are integral for the selected Smith step.

In the no-wall branch all transverse section coordinates are identically
zero, so that integrality is automatic. -/
theorem noWallPrimitiveSmithFamily_preservesExactCollision
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
        P a b) :
    ∃ a' b' : Fin 4 → Polynomial K,
      HasPolynomialFamilyExactGradientCollision
        (noWallPrimitiveSmithFamily
          P a b Delta hdef hnone)
        a' b' := by
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
        alignedSmithRamificationIndex P a b hcoll
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
  have hout :
      HasPolynomialFamilyExactGradientCollision
        (commonParameterFactorFamily
          (alignedSmithRamificationIndex * m)
          Q hcommon)
        a' b' :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      (alignedSmithRamificationIndex * m)
      Q hcommon a' b' hsmithColl
  refine ⟨a', b', ?_⟩
  simpa [noWallPrimitiveSmithFamily,
    hne, m, N, hlegal, Pram, hsmith, Q, hcommon] using hout

/-! ## Consolidated endpoint output -/

/-- A concrete residual marked-section boundary certificate. -/
def HasAlignedSmithSectionBoundary
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) : Prop :=
  (∃ i : Fin 4,
      i ≠ 0 ∧
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls a ∧
      Polynomial.constantCoeff
        (alignedSmithGenuineFirstWallSectionLeft
          (K := K) P a b hwall i) ≠ 0) ∨
  (∃ i : Fin 4,
      i ≠ 0 ∧
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithSectionWalls b ∧
      Polynomial.constantCoeff
        (alignedSmithGenuineFirstWallSectionRight
          (K := K) P a b hwall i) ≠ 0)

/-- Potential-side Smith endpoint closure.

At a genuine wall, either the transformed special fibre is symmetric
minimal or an actual marked section exposes a nonzero transverse special
coordinate.

If there is no genuine wall, the one-shot primitive normalisation has a
symmetric-minimal special fibre. -/
theorem alignedSmith_primitiveEndpoint_dichotomy
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    (∃ hwall : HasAlignedSmithGenuineWall P a b,
        IsSymmetricSmithPoleMinimal
            (smithProjectedSupport
              (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber
                (alignedSmithGenuineFirstWallFamily
                  (K := K) P a b hwall)))
            0
            (fun _ => (0 : ℤ)) ∨
          HasAlignedSmithSectionBoundary P a b hwall) ∨
      (∃ hnone :
          ¬ HasAlignedSmithGenuineWall P a b,
        IsSymmetricSmithPoleMinimal
          (smithProjectedSupport
            (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber
              (noWallPrimitiveSmithFamily
                P a b Delta hdef hnone)))
          0
          (fun _ => (0 : ℤ))) := by
  classical
  by_cases hwall :
      HasAlignedSmithGenuineWall P a b
  · left
    refine ⟨hwall, ?_⟩
    rcases
        alignedSmithGenuineFirstWall_cases
          P a b hwall with
      hcoeff | hsectionA | hsectionB
    · left
      exact
        genuineCoefficientWall_specialFiber_symmetricMinimal
          P a b hwall hcoeff
    · right
      left
      rcases
          genuineLeftSectionWall_exposes_nonzero_specialCoordinate
            P a b hwall hsectionA with
        ⟨i, hi0, hne⟩
      exact ⟨i, hi0, hsectionA, hne⟩
    · right
      right
      rcases
          genuineRightSectionWall_exposes_nonzero_specialCoordinate
            P a b hwall hsectionB with
        ⟨i, hi0, hne⟩
      exact ⟨i, hi0, hsectionB, hne⟩
  · right
    exact
      ⟨hwall,
        noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
          P a b Delta hdef hwall⟩

end

end HC4.Valuation
