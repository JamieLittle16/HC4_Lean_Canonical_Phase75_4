import HC4.Valuation.AdaptiveAlignedSmithHomogeneousCoefficientRigidity
import Mathlib.Tactic

/-!
# Pure-longitudinal homogeneous blocker rigidity

The transverse degree-pure blocker constructors are already impossible.
This file eliminates the sole remaining concrete constructor: the
pure-longitudinal derivative residual.

Let `F` be the raw special fibre and let

    G = longitudinalRightRecenterHom F.

For a pure-longitudinal residual the source axis polynomial `A` satisfies

    A' = X * (X - 1) * C,     C ≠ 0.

The longitudinal axis fibre of `G` is `taylor 1 A`.  If `G` is ordinary
homogeneous, the coefficient-rigidity theorem from the previous file says
that this nonzero axis fibre is a single monomial `a X^n`.

The derivative commutes with the translation `X ↦ X + 1`, so the derivative
of the recentered axis is `taylor 1 A'`.  The displayed endpoint factor
therefore makes that derivative vanish at `X = -1`, because this corresponds
to evaluating `A'` at `0`.

On the other hand `A' ≠ 0`; Taylor translation preserves nonzeroness, so the
recentered monomial has nonzero derivative.  In characteristic zero the
derivative of a nonconstant monomial is nonzero at `-1`.  Contradiction.

Consequently a canonical degree-pure blocker cannot remain a concrete
blocker at all: the only remaining outcome of its stored mixed-degree
classifier is the already-existing general surviving Smith-grade shape.

Thus the canonical blocker competition sharpens to

    surviving shape | explicit mixed-degree endpoint.

No new geometric restart is manufactured here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The zero-transverse longitudinal coefficient polynomial is the axis
restriction.  This packages an equality repeatedly used by the mixed-degree
axis library. -/
theorem longitudinalCoefficientPolynomial_zero_eq_axisRestriction
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomial 0 0 0 F =
      longitudinalAxisRestriction F := by
  rw [longitudinalAxisRestriction_eq_coefficient_zero]
  simp [longitudinalCoefficientPolynomial, smithTransverseExponent]

/-- Right longitudinal recentering translates the axis restriction by the
same univariate Taylor operator as every fixed transverse fibre. -/
theorem longitudinalAxisRestriction_longitudinalRightRecenterHom
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestriction
        (longitudinalRightRecenterHom (K := K) F) =
      Polynomial.taylor 1 (longitudinalAxisRestriction F) := by
  rw [← longitudinalCoefficientPolynomial_zero_eq_axisRestriction
      (longitudinalRightRecenterHom (K := K) F)]
  rw [longitudinalCoefficientPolynomial_longitudinalRightRecenterHom]
  rw [longitudinalCoefficientPolynomial_zero_eq_axisRestriction]

/-- Formal differentiation commutes with the longitudinal translation used
by the recentering map. -/
theorem derivative_taylor_one
    (A : Polynomial K) :
    (Polynomial.taylor 1 A).derivative =
      Polynomial.taylor 1 A.derivative := by
  rw [Polynomial.taylor_apply]
  rw [Polynomial.derivative_comp]
  rw [Polynomial.derivative_X_add_C]
  simp [Polynomial.taylor_apply]

/-- A nonzero derivative of a nonzero monomial cannot vanish at `-1` in
characteristic zero. -/
theorem derivative_monomial_eval_neg_one_ne_zero
    (n : ℕ)
    (a : K)
    (ha : a ≠ 0)
    (hderiv : (Polynomial.monomial n a).derivative ≠ 0) :
    Polynomial.eval (-1 : K)
        (Polynomial.monomial n a).derivative ≠ 0 := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at hderiv
  have hncast : (n : K) ≠ 0 :=
    (Nat.cast_ne_zero).2 hn
  rw [Polynomial.derivative_monomial]
  simp [ha, hncast]

/-- **Pure-longitudinal homogeneous blocker contradiction.**

A retained pure-longitudinal blocker residual is incompatible with ordinary
homogeneity of the right-recentered raw special fibre.
-/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.impossible_of_recenteredHomogeneous
    {degreeCap D : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual
      (K := K) B)
    (hhom :
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber).IsHomogeneous D) :
    False := by
  let F := B.aligned.endpoint.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let Q := longitudinalCoefficientPolynomial 0 0 0 G

  have hsourceAxis :
      longitudinalCoefficientPolynomial 0 0 0 F = P.axis := by
    calc
      longitudinalCoefficientPolynomial 0 0 0 F =
          longitudinalAxisRestriction F :=
        longitudinalCoefficientPolynomial_zero_eq_axisRestriction F
      _ = P.axis := P.axis_eq.symm

  have htranslate :
      Q = Polynomial.taylor 1 P.axis := by
    dsimp [Q, G]
    calc
      longitudinalCoefficientPolynomial 0 0 0
          (longitudinalRightRecenterHom (K := K) F) =
          Polynomial.taylor 1
            (longitudinalCoefficientPolynomial 0 0 0 F) :=
        longitudinalCoefficientPolynomial_longitudinalRightRecenterHom
          0 0 0 F
      _ = Polynomial.taylor 1 P.axis := by rw [hsourceAxis]

  have hQne : Q ≠ 0 := by
    rw [htranslate]
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
      Q.derivative =
        Polynomial.taylor 1 P.axis.derivative := by
    rw [htranslate]
    exact derivative_taylor_one P.axis

  have hQderiv_ne : Q.derivative ≠ 0 := by
    rw [hQderivative]
    exact
      polynomial_taylor_one_ne_zero
        P.axis.derivative hAderiv_ne

  have hQderiv_neg_one_zero :
      Polynomial.eval (-1 : K) Q.derivative = 0 := by
    rw [hQderivative]
    rw [Polynomial.taylor_eval]
    rw [P.derivative_factor]
    simp

  rcases
      homogeneous_longitudinalCoefficient_eq_monomial
        G D 0 0 0 hhom hQne with
    ⟨n, a, ha, hmono⟩

  have hmonoDeriv_ne :
      (Polynomial.monomial n a).derivative ≠ 0 := by
    rw [← hmono]
    exact hQderiv_ne

  have hmonoQ :
      Q = Polynomial.monomial n a := by
    simpa [Q] using hmono

  have hQderiv_neg_one_ne :
      Polynomial.eval (-1 : K) Q.derivative ≠ 0 := by
    rw [hmonoQ]
    exact
      derivative_monomial_eval_neg_one_ne_zero
        n a ha hmonoDeriv_ne

  exact hQderiv_neg_one_ne hQderiv_neg_one_zero

/-- A canonical degree-pure blocker is impossible outright.  The earlier
API could only conclude a surviving shape because it destructed the coarse
stored `outcome`; the blocker `pattern` now reconstructs a concrete residual
directly, and every such residual contradicts recentered homogeneity. -/
theorem AdaptiveAlignedSmithDegreePureBlockerEndpoint.impossible
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithDegreePureBlockerEndpoint
      (K := K) degreeCap) :
    False := by
  rcases E.blocker.concreteResidualNormalForm with ⟨R⟩
  rcases
      R.pureLongitudinal_of_recenteredHomogeneous
        E.recentered_homogeneous with
    ⟨P⟩
  exact
    P.impossible_of_recenteredHomogeneous
      E.recentered_homogeneous

/-- A degree-pure canonical blocker has no concrete blocker constructor left;
it is necessarily already in the general surviving Smith-grade shape. -/
theorem AdaptiveAlignedSmithDegreePureBlockerEndpoint.survivingShape
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithDegreePureBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape E.blocker.exponent := by
  rcases E.blocker.concreteResidualNormalForm_or_survivingShape with
    hconcrete | hsurviving
  · rcases hconcrete with ⟨R⟩
    rcases
        R.pureLongitudinal_of_recenteredHomogeneous
          E.recentered_homogeneous with
      ⟨P⟩
    exact False.elim <|
      P.impossible_of_recenteredHomogeneous
        E.recentered_homogeneous
  · exact hsurviving

/-- **Canonical blocker closure.**

Every canonical blocker is genuinely mixed-degree after right recentering.
The degree-pure tied alternative is impossible, and the old
`survivingShape` escape was only information loss in the stored coarse
outcome.  This is the strongest blocker-facing endpoint needed by the final
dispatcher. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.mixedDegreeEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    Nonempty
      (AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
        (K := K) degreeCap) := by
  rcases B.zeroBaseDegreePure_or_mixedPair with hpure | hmixed
  · rcases
        zeroBaseDegreePure_exists_homogeneous
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)
          hpure with
      ⟨D, hhom⟩
    let E :
        AdaptiveAlignedSmithDegreePureBlockerEndpoint
          (K := K) degreeCap :=
      {
        blocker := B
        degree := D
        recentered_homogeneous := hhom
      }
    exact False.elim E.impossible
  · exact B.toMixedDegreeEndpoint hmixed

/-- Identity-preserving version of `mixedDegreeEndpoint`.  The older
`Nonempty` wrapper forgets which blocker was used to build the endpoint;
for final assembly we retain that equality explicitly. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.exists_mixedDegreeEndpoint_eq
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    ∃ M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
        (K := K) degreeCap,
      M.blocker = B := by
  rcases B.zeroBaseDegreePure_or_mixedPair with hpure | hmixed
  · rcases
        zeroBaseDegreePure_exists_homogeneous
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)
          hpure with
      ⟨D, hhom⟩
    let E :
        AdaptiveAlignedSmithDegreePureBlockerEndpoint
          (K := K) degreeCap :=
      {
        blocker := B
        degree := D
        recentered_homogeneous := hhom
      }
    exact False.elim E.impossible
  · rcases hmixed with ⟨d₀, hd₀, d₁, hd₁, hdegree⟩
    exact
      ⟨{
        blocker := B
        d₀ := d₀
        d₁ := d₁
        d₀_mem := hd₀
        d₁_mem := hd₁
        degree_ne := hdegree
      }, rfl⟩

/-- **Canonical blocker sharpening.**

After eliminating the degree-pure concrete blocker, the canonical zero-base
blocker competition has only two genuine outputs:

* the already-existing general surviving Smith-grade shape;
* an explicit tied mixed-degree endpoint.

We return directly to the zero-base trichotomy rather than destructing the
earlier `Nonempty` degree-pure wrapper, so the identity of the original
blocker `B` is never lost.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_mixedDegreeEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      Nonempty
        (AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
          (K := K) degreeCap) := by
  rcases
      B.survivingShape_or_zeroBaseDegreePure_or_mixedPair with
    hsurviving | hpure | hmixed

  · exact Or.inl hsurviving

  · rcases
        zeroBaseDegreePure_exists_homogeneous
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)
          hpure with
      ⟨D, hhom⟩

    let E :
        AdaptiveAlignedSmithDegreePureBlockerEndpoint
          (K := K) degreeCap :=
      {
        blocker := B
        degree := D
        recentered_homogeneous := hhom
      }

    have hshape :
        HasGeneralSurvivingSmithGradeShape E.blocker.exponent :=
      E.survivingShape

    simpa [E] using Or.inl hshape

  · exact Or.inr (B.toMixedDegreeEndpoint hmixed)

end

end HC4.Valuation
