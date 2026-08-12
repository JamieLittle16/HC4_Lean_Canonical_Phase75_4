import HC4.Valuation.AdaptiveAlignedSmithWSquarePacket
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import Mathlib.Tactic

/-!
# Pure-longitudinal blocker curvature and transverse-support frontier

After all transverse quadratic competitors have been absorbed into the
persistent-packet machinery, the only exceptional all-minors blocker is the
pure-longitudinal Smith pattern.

This file extracts two pieces of structure that were already implicit in the
normalised blocker residual but had not yet been packaged for the final
argument.

First, the pure pattern reconstructs an honest
`AdaptiveAlignedSmithPureLongitudinalResidual` directly, without passing
through any coarse blocker outcome.

Second, if

    A' = X (X - 1) C,     C != 0,

then `A'' != 0` in characteristic zero.  Right recentering is Taylor
translation by `1`, so the longitudinal `(0,0)` Hessian entry of the
recentered special fibre has nonzero restriction to the distinguished axis.
This is the nonzero pivot needed to read the all-minors identities at the
first positive transverse layer.

Finally we package the elementary finite-support dichotomy: a polynomial is
transverse-free, or its Smith projected support contains an exponent of
strictly positive total transverse degree.  The transverse-free alternative
immediately implies the coordinate-`3` freeness required by the already-green
generic kernel restart.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Recovering the pure residual from the canonical blocker -/

/-- Once the canonical blocker exponent is known to be pure longitudinal,
the concrete residual reconstructed from the blocker data must be the pure
constructor.  The three transverse constructors have incompatible exponent
patterns. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinalResidual_of_pattern
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hpure : IsPureLongitudinalSmithPattern B.exponent) :
    Nonempty (AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) := by
  rcases B.concreteResidualNormalForm with ⟨R⟩
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        ⟨{
          axis := A
          residual := C
          pattern := hpattern
          axis_ne_zero := hA
          axis_eq := hAeq
          residual_ne_zero := hC
          derivative_factor := hfactor
          degree_drop := hdegree
          normal := normal
        }⟩
  | lowNegativeFirst A C hpattern hA hAeq hC hfactor hdegree normal =>
      exfalso
      rcases hpure with ⟨hb0, hc0, hd0⟩
      rcases hpattern with ⟨hb, hc, hd⟩
      omega
  | lowNegativeSecond A C hpattern hA hAeq hC hfactor hdegree normal =>
      exfalso
      rcases hpure with ⟨hb0, hc0, hd0⟩
      rcases hpattern with ⟨hb, hc, hd⟩
      omega
  | wLinear A C hpattern hA hAeq hC hfactor hdegree normal =>
      exfalso
      rcases hpure with ⟨hb0, hc0, hd0⟩
      rcases hpattern with ⟨hb, hc, hd⟩
      omega

/-! ## Nonzero longitudinal curvature -/

/-- The first derivative in a pure-longitudinal blocker residual is nonzero. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.axis_derivative_ne_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) :
    P.axis.derivative ≠ 0 := by
  rw [P.derivative_factor]
  exact
    mul_ne_zero
      (mul_ne_zero
        (by simp)
        (Polynomial.X_sub_C_ne_zero 1))
      P.residual_ne_zero

/-- The endpoint factor `X(X-1)` forces the longitudinal axis to have
nonzero second derivative.  The proof avoids degree arithmetic: if the
second derivative vanished, the first derivative would be constant; its
value at `0` is zero by the endpoint factor, forcing the first derivative to
vanish identically. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.axis_secondDerivative_ne_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) :
    P.axis.derivative.derivative ≠ 0 := by
  intro hsecond
  have hconst :
      P.axis.derivative = Polynomial.C (P.axis.derivative.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hsecond
  have heval0 : Polynomial.eval (0 : K) P.axis.derivative = 0 := by
    rw [P.derivative_factor]
    simp
  have hcoeff0 : P.axis.derivative.coeff 0 = 0 := by
    rw [hconst] at heval0
    simpa using heval0
  apply P.axis_derivative_ne_zero
  rw [hconst, hcoeff0]
  simp

/-- Right recentering preserves the nonzero second longitudinal derivative. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.rightRecentered_axis_secondDerivative_ne_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) :
    let G := longitudinalRightRecenterHom
      (K := K) B.aligned.endpoint.rawSpecialFiber
    (longitudinalAxisRestriction G).derivative.derivative ≠ 0 := by
  dsimp only
  rw [longitudinalAxisRestriction_longitudinalRightRecenterHom]
  rw [← P.axis_eq]
  rw [derivative_taylor_one, derivative_taylor_one]
  exact
    polynomial_taylor_one_ne_zero
      P.axis.derivative.derivative
      P.axis_secondDerivative_ne_zero

/-- The finite right-recentered Hessian therefore has a genuinely nonzero
longitudinal pivot after restriction to the distinguished axis. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.rightRecentered_hessian_zero_zero_axis_ne_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) :
    let G := longitudinalRightRecenterHom
      (K := K) B.aligned.endpoint.rawSpecialFiber
    longitudinalAxisRestriction
        (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) ≠ 0 := by
  dsimp only
  rw [HC4.Polynomial.hessian_apply]
  rw [longitudinalAxisRestriction_pderiv_zero]
  rw [longitudinalAxisRestriction_pderiv_zero]
  exact P.rightRecentered_axis_secondDerivative_ne_zero

/-! ## The finite transverse-support dichotomy -/

/-- Strictly positive total transverse degree for a projected Smith
exponent. -/
def HasPositiveTotalTransverseDegree (e : SmithSupportExponent) : Prop :=
  0 < e.b + e.c + e.d

/-- A polynomial is either completely transverse-free or has an actual
projected-support exponent of positive total transverse degree. -/
theorem transverseFree_or_exists_positiveTransverseProjectedSupport
    (F : MvPolynomial (Fin 4) K) :
    (∀ d ∈ F.support,
      d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
      HasPositiveTotalTransverseDegree e) := by
  classical
  by_cases hfree :
      ∀ d ∈ F.support,
        d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0
  · exact Or.inl hfree
  · right
    push_neg at hfree
    rcases hfree with ⟨d, hd, htrans⟩
    let e := smithSupportExponentOf (1 : Fin 4) 2 3 d
    refine ⟨e, smithSupportExponentOf_mem_projectedSupport F d hd, ?_⟩
    dsimp [HasPositiveTotalTransverseDegree, e, smithSupportExponentOf]
    omega

/-- The transverse-free side of the preceding dichotomy is already enough
for the generic coordinate-`3` kernel restart. -/
theorem transverseFree_implies_free_three
    (F : MvPolynomial (Fin 4) K)
    (hfree :
      ∀ d ∈ F.support,
        d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) :
    ∀ d ∈ F.support, d (3 : Fin 4) = 0 := by
  intro d hd
  exact (hfree d hd).2.2

/-- Dispatcher-facing pure-blocker support frontier.  The exceptional
all-minors pure blocker now comes with both the nonzero longitudinal Hessian
pivot and an exhaustive finite support alternative. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_curvature_and_support_frontier
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hpure : IsPureLongitudinalSmithPattern B.exponent) :
    ∃ P : AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B,
      (let G := longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber
       longitudinalAxisRestriction
          (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) ≠ 0) ∧
      ((∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
          d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
       (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3
            B.aligned.endpoint.rawSpecialFiber,
          HasPositiveTotalTransverseDegree e)) := by
  rcases B.pureLongitudinalResidual_of_pattern hpure with ⟨P⟩
  refine ⟨P, P.rightRecentered_hessian_zero_zero_axis_ne_zero, ?_⟩
  exact transverseFree_or_exists_positiveTransverseProjectedSupport
    B.aligned.endpoint.rawSpecialFiber

end

end HC4.Valuation
