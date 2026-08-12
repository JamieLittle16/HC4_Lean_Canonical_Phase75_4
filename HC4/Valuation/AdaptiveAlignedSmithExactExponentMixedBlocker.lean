import HC4.Valuation.AdaptiveAlignedSmithSameExponentCompetition
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHomogeneousRigidity
import Mathlib.Tactic

/-!
# Exact-exponent mixedness of aligned Smith blockers

The canonical zero scalar functional is useful as a finite classifier, but it
is too coarse to justify the statement that the two mixed ordinary-degree
witnesses lie over the blocker exponent itself.

This file proves the stronger statement directly from the endpoint residual.

For each transverse concrete blocker, the longitudinal coefficient fibre over
the stored blocker exponent `e` has the source factor

    A = X * (X - 1) * R.

After right recentering this fibre is `taylor 1 A`.  It is nonzero but
vanishes at `X = -1`, hence it cannot be a single monomial.  Therefore it has
two distinct longitudinal exponents.  Since their three transverse
coordinates are fixed, both source monomials project to exactly the same
Smith exponent `e`, while their ordinary degrees differ.

For the pure-longitudinal constructor the same conclusion follows one
derivative higher: the recentered axis fibre has nonzero derivative, but that
derivative vanishes at `X = -1`.  A single nonzero monomial cannot have this
property in characteristic zero.

Thus every canonical aligned blocker is either already in the general
surviving Smith shape, or has *exact same-exponent mixedness*.  No arbitrary
zero-base mixed pair is used in the final interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-! ## Elementary univariate support lemmas -/

/-- A nonzero polynomial which is not a single nonzero monomial has two
distinct support exponents. -/
theorem polynomial_exists_two_support_of_not_monomial
    (P : Polynomial K)
    (hP : P ≠ 0)
    (hnot :
      ∀ n : ℕ, ∀ a : K, a ≠ 0 →
        P ≠ Polynomial.monomial n a) :
    ∃ n₀ ∈ P.support, ∃ n₁ ∈ P.support, n₀ ≠ n₁ := by
  have hsupp : P.support.Nonempty :=
    Polynomial.support_nonempty.mpr hP
  rcases hsupp with ⟨n₀, hn₀⟩
  by_cases hsecond :
      ∃ n₁ ∈ P.support, n₀ ≠ n₁
  · rcases hsecond with ⟨n₁, hn₁, hne⟩
    exact ⟨n₀, hn₀, n₁, hn₁, hne⟩
  · have hc₀ : P.coeff n₀ ≠ 0 :=
      Polynomial.mem_support_iff.mp hn₀
    have hmono :
        P = Polynomial.monomial n₀ (P.coeff n₀) := by
      apply Polynomial.ext
      intro n
      by_cases hn : n = n₀
      · subst n
        simp
      · have hcn : P.coeff n = 0 := by
          by_contra hcn
          have hnmem : n ∈ P.support :=
            Polynomial.mem_support_iff.mpr hcn
          exact hsecond ⟨n, hnmem, Ne.symm hn⟩
        rw [hcn]
        symm
        exact
          Polynomial.coeff_monomial_of_ne
            (P.coeff n₀) hn
    exact False.elim ((hnot n₀ (P.coeff n₀) hc₀) hmono)

/-- A nonzero polynomial vanishing at `-1` cannot be a single nonzero
monomial. -/
theorem polynomial_exists_two_support_of_eval_neg_one_eq_zero
    (P : Polynomial K)
    (hP : P ≠ 0)
    (heval : Polynomial.eval (-1 : K) P = 0) :
    ∃ n₀ ∈ P.support, ∃ n₁ ∈ P.support, n₀ ≠ n₁ := by
  apply polynomial_exists_two_support_of_not_monomial P hP
  intro n a ha hmono
  rw [hmono] at heval
  simp [ha] at heval

/-! ## Fixed transverse exponent bookkeeping -/

/-- Every longitudinal monomial over the fixed Smith transverse exponent
projects back to that exact Smith exponent.  We package the equality as its
three coordinate equalities, which is the stable API already exported by the
Newton layer. -/
theorem cons_smithTransverseExponent_has_projection
    (e : SmithSupportExponent)
    (n : ℕ) :
    ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = e.b ∧
    ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = e.c ∧
    ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = e.d :=
  smithSupportExponentOf_cons_smithTransverseExponent e n

/-- Changing only the longitudinal exponent changes ordinary degree by the
same amount. -/
theorem ordinaryDegree4_cons_smithTransverseExponent_eq
    (e : SmithSupportExponent)
    (n : ℕ) :
    HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n) =
      n + e.b + e.c + e.d := by
  calc
    HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n)
        =
      ((smithTransverseExponent e.b e.c e.d).cons n).degree :=
        (finsuppDegree_eq_ordinaryDegree4
          ((smithTransverseExponent e.b e.c e.d).cons n)).symm
    _ =
      Finsupp.weight (1 : Fin 4 → ℕ)
        ((smithTransverseExponent e.b e.c e.d).cons n) :=
        congrFun Finsupp.degree_eq_weight_one
          ((smithTransverseExponent e.b e.c e.d).cons n)
    _ = n + e.b + e.c + e.d :=
      weight_one_cons_smithTransverseExponent e.b e.c e.d n

theorem ordinaryDegree4_cons_smithTransverseExponent_ne
    (e : SmithSupportExponent)
    {n₀ n₁ : ℕ}
    (hne : n₀ ≠ n₁) :
    HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n₀) ≠
      HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n₁) := by
  rw [ordinaryDegree4_cons_smithTransverseExponent_eq,
      ordinaryDegree4_cons_smithTransverseExponent_eq]
  omega

/-- Exact same-exponent mixed ordinary-degree support in a polynomial.

This is deliberately `Prop`-valued.  The next stages only need existence of
the two support layers; they never compute with a chosen witness.  Encoding
the certificate in `Prop` also lets us eliminate the finite-support
existentials used to construct it without any `Exists`-to-`Type`
elimination.

The two monomials are built with the same fixed transverse Smith exponent
`e`, so exact equality of the projected Smith exponent is built into the
statement itself.
-/
def ExactSmithExponentMixedDegreeData
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent) : Prop :=
  ∃ n₀ n₁ : ℕ,
    n₀ ≠ n₁ ∧
    ((smithTransverseExponent e.b e.c e.d).cons n₀) ∈ F.support ∧
    ((smithTransverseExponent e.b e.c e.d).cons n₁) ∈ F.support ∧
    HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n₀) ≠
      HC4.Polynomial.ordinaryDegree4
        ((smithTransverseExponent e.b e.c e.d).cons n₁)

/-! ## Transverse blocker fibres -/

/-- The two-endpoint factor over one fixed transverse Smith exponent produces
exact same-exponent mixed ordinary-degree support after right recentering. -/
theorem exactSmithExponentMixedDegreeData_of_twoEndpointFactor
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (A R : Polynomial K)
    (hA : A ≠ 0)
    (hAeq :
      A = longitudinalCoefficientPolynomial e.b e.c e.d F)
    (hfactor :
      A =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom (K := K) F) e := by
  let G := longitudinalRightRecenterHom (K := K) F
  let Q := longitudinalCoefficientPolynomial e.b e.c e.d G

  have htranslate :
      Q =
        Polynomial.taylor 1
          (longitudinalCoefficientPolynomial e.b e.c e.d F) := by
    dsimp [Q, G]
    exact
      longitudinalCoefficientPolynomial_longitudinalRightRecenterHom
        e.b e.c e.d F

  have hsourceNe :
      longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 := by
    rw [← hAeq]
    exact hA

  have hQne : Q ≠ 0 := by
    rw [htranslate]
    exact polynomial_taylor_one_ne_zero
      (longitudinalCoefficientPolynomial e.b e.c e.d F) hsourceNe

  have hQneg : Polynomial.eval (-1 : K) Q = 0 := by
    rw [htranslate, Polynomial.taylor_eval]
    rw [← hAeq, hfactor]
    simp

  rcases
      polynomial_exists_two_support_of_eval_neg_one_eq_zero
        Q hQne hQneg with
    ⟨n₀, hn₀, n₁, hn₁, hne⟩

  have hd₀ :
      ((smithTransverseExponent e.b e.c e.d).cons n₀) ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact Polynomial.mem_support_iff.mp hn₀

  have hd₁ :
      ((smithTransverseExponent e.b e.c e.d).cons n₁) ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact Polynomial.mem_support_iff.mp hn₁

  refine ⟨n₀, n₁, hne, ?_, ?_, ?_⟩
  · simpa [G] using hd₀
  · simpa [G] using hd₁
  · exact ordinaryDegree4_cons_smithTransverseExponent_ne e hne

/-! ## Pure-longitudinal fibre -/

section CharZero

variable [CharZero K]

/-- If a nonzero polynomial has nonzero derivative and that derivative
vanishes at `-1`, then the polynomial has at least two support exponents. -/
theorem polynomial_exists_two_support_of_derivative_eval_neg_one_eq_zero
    (P : Polynomial K)
    (hP : P ≠ 0)
    (hderiv : P.derivative ≠ 0)
    (heval : Polynomial.eval (-1 : K) P.derivative = 0) :
    ∃ n₀ ∈ P.support, ∃ n₁ ∈ P.support, n₀ ≠ n₁ := by
  apply polynomial_exists_two_support_of_not_monomial P hP
  intro n a ha hmono
  have hmonoDerivNe :
      (Polynomial.monomial n a).derivative ≠ 0 := by
    rw [← hmono]
    exact hderiv
  have hmonoEvalNe :
      Polynomial.eval (-1 : K)
          (Polynomial.monomial n a).derivative ≠ 0 :=
    derivative_monomial_eval_neg_one_ne_zero
      n a ha hmonoDerivNe
  rw [hmono] at heval
  exact hmonoEvalNe heval

/-- The sole pure-longitudinal residual also creates exact same-exponent
mixedness after right recentering. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.exactExponentMixedDegreeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual
      (K := K) B) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      B.exponent := by
  let F := B.aligned.endpoint.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let Q := longitudinalCoefficientPolynomial
    B.exponent.b B.exponent.c B.exponent.d G

  rcases P.pattern with ⟨hb, hc, hd⟩

  have hQaxis :
      Q = longitudinalAxisRestriction G := by
    dsimp [Q]
    rw [hb, hc, hd]
    exact longitudinalCoefficientPolynomial_zero_eq_axisRestriction G

  have haxisTranslate :
      longitudinalAxisRestriction G =
        Polynomial.taylor 1 P.axis := by
    dsimp [G, F]
    rw [longitudinalAxisRestriction_longitudinalRightRecenterHom]
    rw [← P.axis_eq]

  have hQtranslate :
      Q = Polynomial.taylor 1 P.axis :=
    hQaxis.trans haxisTranslate

  have hQne : Q ≠ 0 := by
    rw [hQtranslate]
    exact polynomial_taylor_one_ne_zero P.axis P.axis_ne_zero

  have hAderiv_ne : P.axis.derivative ≠ 0 := by
    rw [P.derivative_factor]
    exact
      mul_ne_zero
        (mul_ne_zero
          (by simp)
          (Polynomial.X_sub_C_ne_zero 1))
        P.residual_ne_zero

  have hQderivative :
      Q.derivative = Polynomial.taylor 1 P.axis.derivative := by
    rw [hQtranslate]
    exact derivative_taylor_one P.axis

  have hQderiv_ne : Q.derivative ≠ 0 := by
    rw [hQderivative]
    exact polynomial_taylor_one_ne_zero
      P.axis.derivative hAderiv_ne

  have hQderiv_neg :
      Polynomial.eval (-1 : K) Q.derivative = 0 := by
    rw [hQderivative, Polynomial.taylor_eval]
    rw [P.derivative_factor]
    simp

  rcases
      polynomial_exists_two_support_of_derivative_eval_neg_one_eq_zero
        Q hQne hQderiv_ne hQderiv_neg with
    ⟨n₀, hn₀, n₁, hn₁, hne⟩

  have hd₀ :
      ((smithTransverseExponent
        B.exponent.b B.exponent.c B.exponent.d).cons n₀) ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact Polynomial.mem_support_iff.mp hn₀

  have hd₁ :
      ((smithTransverseExponent
        B.exponent.b B.exponent.c B.exponent.d).cons n₁) ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact Polynomial.mem_support_iff.mp hn₁

  refine ⟨n₀, n₁, hne, ?_, ?_, ?_⟩
  · simpa [G, F] using hd₀
  · simpa [G, F] using hd₁
  · exact
      ordinaryDegree4_cons_smithTransverseExponent_ne
        B.exponent hne

/-! ## Concrete blocker and canonical blocker interfaces -/

/-- Every fully normalized concrete blocker has exact same-exponent
mixedness after right recentering. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.exactExponentMixedDegreeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (R :
      AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
        (K := K) B) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      B.exponent := by
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      let P :
          AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B :=
        {
          axis := A
          residual := C
          pattern := hpattern
          axis_ne_zero := hA
          axis_eq := hAeq
          residual_ne_zero := hC
          derivative_factor := hfactor
          degree_drop := hdegree
          normal := normal
        }
      exact P.exactExponentMixedDegreeData

  | lowNegativeFirst A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        exactSmithExponentMixedDegreeData_of_twoEndpointFactor
          B.aligned.endpoint.rawSpecialFiber B.exponent
          A C hA hAeq hfactor

  | lowNegativeSecond A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        exactSmithExponentMixedDegreeData_of_twoEndpointFactor
          B.aligned.endpoint.rawSpecialFiber B.exponent
          A C hA hAeq hfactor

  | wLinear A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        exactSmithExponentMixedDegreeData_of_twoEndpointFactor
          B.aligned.endpoint.rawSpecialFiber B.exponent
          A C hA hAeq hfactor

/-- Strong canonical blocker interface.  Once the blocker pattern is used
rather than the coarse stored outcome, every blocker has exact
same-exponent mixedness after right recentering. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.exactExponentMixedDegree
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    ExactSmithExponentMixedDegreeData
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      B.exponent := by
  rcases B.concreteResidualNormalForm with ⟨R⟩
  exact R.exactExponentMixedDegreeData

/-- **Corrected canonical blocker interface.**

A blocker is either already in the general surviving Smith-grade shape, or
its *own exact projected Smith exponent* supports at least two distinct
ordinary degrees after right recentering.

This is strictly stronger than the earlier zero-base mixed-pair endpoint and
is the correct stationary-face input for the forced-departure analysis.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_exactExponentMixedDegree
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        B.exponent := by
  rcases B.concreteResidualNormalForm_or_survivingShape with
    hconcrete | hsurviving
  · rcases hconcrete with ⟨R⟩
    exact Or.inr R.exactExponentMixedDegreeData
  · exact Or.inl hsurviving

end CharZero

end

end HC4.Valuation
