import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianAllMinors
import Mathlib.Tactic

/-!
# Quadratic competitors forced by the rank-one blocker Hessian

The green blocker frontier now leaves only one exceptional alternative:

* the first longitudinal departure is present; and
* every `2 x 2` minor of the finite right-recentered Hessian vanishes.

For a transverse-linear blocker this is already strong enough to force a
new quadratic transverse coefficient.

Write the relevant right-recentered transverse-linear coefficient fibre as
`A(x₀)`.  On the distinguished longitudinal axis the `(0,j)` Hessian minor is

    H₀₀ Hⱼⱼ - H₀ⱼ² = 0,

while

    H₀ⱼ|axis = A',
    Hⱼⱼ|axis = 2 B,

where `B` is the longitudinal coefficient fibre over transverse exponent
`2 e_j`.  The concrete blocker residual has source factor

    X (X - 1) R

with exact degree drop, so after right recentering `A' != 0`.  Therefore
`B != 0`, and hence the corresponding quadratic projected Smith exponent is
really present.

Thus the all-minors residual can only be

* pure longitudinal; or
* accompanied by one of `y²`, `z²`, `w²` in projected support.

The first two are the old symmetric quadratic targets.  The `w²` output has
strictly positive Smith grade and will be handled by the valuation-tilt
machinery in the next adapter.

No JC2 input occurs here.
-/

namespace HC4.Newton

noncomputable section

universe u

variable {K : Type u} [Field K]

/-! ## Axis restriction as a ring homomorphism -/

/-- Ring-hom form of `longitudinalAxisRestriction`.  Keeping the map bundled
lets us apply it directly to the polynomial Hessian-minor identities. -/
noncomputable def longitudinalAxisRestrictionRingHom :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  (Polynomial.mapRingHom
      (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))).comp
    (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom

@[simp]
theorem longitudinalAxisRestrictionRingHom_apply
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestrictionRingHom (K := K) F =
      longitudinalAxisRestriction F := by
  rfl

/-! ## Longitudinal coefficient fibres of Hessian entries -/

/-- Differentiating in the distinguished source coordinate differentiates
every fixed-transverse longitudinal coefficient polynomial. -/
theorem longitudinalCoefficientPolynomialAt_pderiv_zero
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomialAt m
        (MvPolynomial.pderiv (0 : Fin 4) F) =
      (longitudinalCoefficientPolynomialAt m F).derivative := by
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    Polynomial.coeff_derivative,
    coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    coeff_pderiv_mixedDegree]
  have hexponent :
      m.cons a + Finsupp.single (0 : Fin 4) 1 =
        m.cons (a + 1) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hexponent]
  simp [mul_comm]

/-- The mixed `(0,j)` Hessian entry restricts to the derivative of the
transverse-linear longitudinal coefficient fibre. -/
theorem longitudinalAxisRestriction_hessian_zero_succ
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestriction
        (HC4.Polynomial.hessian F (0 : Fin 4) j.succ) =
      (longitudinalCoefficientPolynomialAt
        (Finsupp.single j 1) F).derivative := by
  rw [HC4.Polynomial.hessian_apply]
  rw [← longitudinalCoefficient_single_eq_axisRestriction_pderiv
    j (MvPolynomial.pderiv (0 : Fin 4) F)]
  exact longitudinalCoefficientPolynomialAt_pderiv_zero
    (Finsupp.single j 1) F

/-- Taking a transverse derivative of a transverse-linear coefficient fibre
exposes twice the corresponding transverse-quadratic fibre. -/
theorem longitudinalCoefficientPolynomial_single_pderiv_succ
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomialAt (Finsupp.single j 1)
        (MvPolynomial.pderiv j.succ F) =
      Polynomial.C (2 : K) *
        longitudinalCoefficientPolynomialAt (Finsupp.single j 2) F := by
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    Polynomial.coeff_C_mul,
    coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    coeff_pderiv_mixedDegree]
  have hexponent :
      (Finsupp.single j 1).cons a +
          Finsupp.single j.succ 1 =
        (Finsupp.single j 2).cons a := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · by_cases hjk : j = k
      · subst k
        simp
      · simp [hjk]
  rw [hexponent]
  simp [mul_comm]

/-- The `(j,j)` Hessian entry restricts to twice the quadratic transverse
coefficient fibre. -/
theorem longitudinalAxisRestriction_hessian_succ_succ
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestriction
        (HC4.Polynomial.hessian F j.succ j.succ) =
      Polynomial.C (2 : K) *
        longitudinalCoefficientPolynomialAt
          (Finsupp.single j 2) F := by
  rw [HC4.Polynomial.hessian_apply]
  rw [← longitudinalCoefficient_single_eq_axisRestriction_pderiv
    j (MvPolynomial.pderiv j.succ F)]
  exact longitudinalCoefficientPolynomial_single_pderiv_succ j F

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-! ## Extracting the principal binary Hessian minor -/

/-- In the identity coordinate chart, the all-minors certificate contains
exactly the principal Hessian minor on coordinates `(0,j)`. -/
theorem adaptiveAlignedRightRecenteredSpecialHessian_principal_zero_succ
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).AllTwoByTwoMinorsZero)
    (j : Fin 3) :
    let G := longitudinalRightRecenterHom (K := K) E.rawSpecialFiber
    HC4.Polynomial.hessian G 0 0 *
        HC4.Polynomial.hessian G j.succ j.succ -
      HC4.Polynomial.hessian G 0 j.succ *
        HC4.Polynomial.hessian G 0 j.succ = 0 := by
  dsimp only
  have h := hall (Equiv.refl (Fin 4))
    (0 : Fin 4) (0 : Fin 4) j.succ j.succ
  fin_cases j <;>
    simpa [HC4.Newton.GeneralFourBlock.AllTwoByTwoMinorsZero,
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, GeneralFourBlock.matrix] using h

/-! ## A transverse-linear blocker forces a quadratic competitor -/

/-- Generic algebraic heart of the transverse blocker argument.

If the blocker fibre over transverse exponent `e_j` has the two-endpoint
factor with exact degree drop, and every finite Hessian `2 x 2` minor
vanishes, then the right-recentered fibre over transverse exponent `2 e_j`
is nonzero. -/
theorem rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
    [CharZero K]
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (e : SmithSupportExponent)
    (j : Fin 3)
    (htrans :
      smithTransverseExponent e.b e.c e.d = Finsupp.single j 1)
    (A R : Polynomial K)
    (hAeq :
      A = longitudinalCoefficientPolynomial
        e.b e.c e.d E.rawSpecialFiber)
    (hdegree : R.natDegree + 2 = A.natDegree)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).AllTwoByTwoMinorsZero) :
    longitudinalCoefficientPolynomialAt (Finsupp.single j 2)
        (longitudinalRightRecenterHom (K := K) E.rawSpecialFiber) ≠ 0 := by
  let F := E.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let Q := longitudinalCoefficientPolynomialAt (Finsupp.single j 1) G

  have hAat :
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F = A := by
    simpa [F, longitudinalCoefficientPolynomial, htrans] using hAeq.symm

  have hAdegree : 2 ≤ A.natDegree := by
    omega

  have hAderiv : A.derivative ≠ 0 := by
    intro hzero
    have hconst : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero hzero
    have hdeg0 : A.natDegree = 0 := by
      rw [hconst]
      simp
    omega

  have hQeq : Q = Polynomial.taylor 1 A := by
    dsimp [Q, G]
    rw [longitudinalCoefficientPolynomialAt_longitudinalRightRecenterHom,
      hAat]

  have hQderiv : Q.derivative ≠ 0 := by
    rw [hQeq, derivative_taylor_one]
    exact polynomial_taylor_one_ne_zero A.derivative hAderiv

  intro hquadZero

  have hminor :=
    adaptiveAlignedRightRecenteredSpecialHessian_principal_zero_succ
      E hall j

  have haxis := congrArg
    (longitudinalAxisRestrictionRingHom (K := K)) hminor

  have hdiagZero :
      longitudinalAxisRestriction
          (HC4.Polynomial.hessian G j.succ j.succ) = 0 := by
    rw [longitudinalAxisRestriction_hessian_succ_succ]
    rw [hquadZero]
    simp

  have hcross :
      longitudinalAxisRestriction
          (HC4.Polynomial.hessian G (0 : Fin 4) j.succ) =
        Q.derivative := by
    exact longitudinalAxisRestriction_hessian_zero_succ j G

  have hsquare : Q.derivative * Q.derivative = 0 := by
    simp only [map_sub, map_mul, map_zero,
      longitudinalAxisRestrictionRingHom_apply] at haxis
    change
      longitudinalAxisRestriction (HC4.Polynomial.hessian G 0 0) *
          longitudinalAxisRestriction
            (HC4.Polynomial.hessian G j.succ j.succ) -
        longitudinalAxisRestriction
            (HC4.Polynomial.hessian G 0 j.succ) *
          longitudinalAxisRestriction
            (HC4.Polynomial.hessian G 0 j.succ) = 0 at haxis
    rw [hdiagZero, hcross] at haxis
    simpa using haxis

  rcases mul_eq_zero.mp hsquare with hzero | hzero
  · exact hQderiv hzero
  · exact hQderiv hzero

/-! ## Projected-support packaging -/

/-- A quadratic competitor forced in the exceptional all-minors branch.
The first two alternatives are the two axis-square members of the symmetric
quadratic target; the third is the positive-grade `w²` competitor. -/
def HasRightRecenteredQuadraticAxisCompetitor
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop :=
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  ({ b := 2, c := 0, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G ∨
    ({ b := 0, c := 2, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G ∨
    ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G

/-- A concrete blocker with rank-at-most-one finite recentered Hessian is
pure longitudinal or forces a genuine transverse quadratic competitor. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.pureLongitudinal_or_quadraticCompetitor_of_allMinors
    [CharZero K]
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (R : AdaptiveAlignedSmithConcreteBlockerResidualNormalForm (K := K) B)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    IsPureLongitudinalSmithPattern B.exponent ∨
      HasRightRecenteredQuadraticAxisCompetitor B := by
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact Or.inl hpattern

  | lowNegativeFirst A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      right
      left
      have hquad :=
        rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
          B.aligned.endpoint B.exponent 1
          (smithTransverseExponent_eq_single_one_of_lowNegativeFirst
            B.exponent hpattern)
          A C hAeq hdegree hall
      have hcoeff :
          longitudinalCoefficientPolynomial 0 2 0 G ≠ 0 := by
        simpa [G, longitudinalCoefficientPolynomial,
          smithTransverseExponent] using hquad
      exact
        (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
          G ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)).mp hcoeff

  | lowNegativeSecond A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      left
      have hquad :=
        rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
          B.aligned.endpoint B.exponent 0
          (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
            B.exponent hpattern)
          A C hAeq hdegree hall
      have hcoeff :
          longitudinalCoefficientPolynomial 2 0 0 G ≠ 0 := by
        simpa [G, longitudinalCoefficientPolynomial,
          smithTransverseExponent] using hquad
      exact
        (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
          G ({ b := 2, c := 0, d := 0 } : SmithSupportExponent)).mp hcoeff

  | wLinear A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      right
      right
      have hquad :=
        rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
          B.aligned.endpoint B.exponent 2
          (smithTransverseExponent_eq_single_two_of_wLinear
            B.exponent hpattern)
          A C hAeq hdegree hall
      have hcoeff :
          longitudinalCoefficientPolynomial 0 0 2 G ≠ 0 := by
        simpa [G, longitudinalCoefficientPolynomial,
          smithTransverseExponent] using hquad
      exact
        (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
          G ({ b := 0, c := 0, d := 2 } : SmithSupportExponent)).mp hcoeff

/-- Blocker-facing form: the all-minors residual is already reduced to the
pure-longitudinal pattern or a real quadratic projected-support competitor. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_or_quadraticCompetitor_of_allMinors
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    IsPureLongitudinalSmithPattern B.exponent ∨
      HasRightRecenteredQuadraticAxisCompetitor B := by
  rcases B.concreteResidualNormalForm with ⟨R⟩
  exact R.pureLongitudinal_or_quadraticCompetitor_of_allMinors hall

/-- **Sharpened blocker Hessian frontier.**

The only exceptional branch left after the two green Schur architectures now
retains first longitudinal departure and is either genuinely pure
longitudinal or already contains a transverse quadratic competitor. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFrontier_with_quadraticCompetitor
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty (ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) ∨
      (HasFirstExactSmithExponentLongitudinalDeparture
          (polynomialFamilySpecialFiber B.aligned.endpoint.rightRecenteredFamily)
          B.exponent ∧
        (IsPureLongitudinalSmithPattern B.exponent ∨
          HasRightRecenteredQuadraticAxisCompetitor B)) := by
  rcases B.rightRecenteredHessianFrontier_with_allMinors hdefect with
    hschur | hzero | hres
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · exact Or.inr (Or.inr
      ⟨hres.1,
        B.pureLongitudinal_or_quadraticCompetitor_of_allMinors hres.2⟩)

end

end HC4.Valuation
