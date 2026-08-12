import HC4.Valuation.AdaptiveAlignedSmithRankTwoZeroSchurComplete
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# Aligned Smith blocker residual normal form

The assembled aligned-Smith classifier has one remaining local output not yet
connected to a geometric continuation: an explicit blocker exponent carrying
`MixedDegreeSmithExponentOutcome`.

The mixed-degree axis-collision library already proves the only honest inner
recursion available from those blocker certificates.  Every nonzero
longitudinal residual `B` admits a finite endpoint normal form

    B = (X - 1)^q * C,

with `C ≠ 0`, `C(1) ≠ 0`, and exact degree accounting.  The proof is by
well-founded descent on `natDegree` and does not manufacture a new HC4
family.

This file merely attaches that already-proved terminating algebraic
normalization to the new aligned blocker endpoint.

It deliberately does *not* claim that the terminal polynomial `C` is itself
a new geometric state.  The next blocker interface must use `C(1) ≠ 0` to
produce an actual wall-level progress or terminal event.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Concrete blocker residual data after the complete inner endpoint-factor
normalization.

The four constructors mirror the four residual-carrying constructors of
`MixedDegreeSmithExponentOutcome`.  All original factorization and degree
data are retained, together with the terminal endpoint residual normal form.
-/
inductive AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) : Type u
  | pureLongitudinal
      (A C : Polynomial K)
      (hpattern : IsPureLongitudinalSmithPattern B.exponent)
      (hA : A ≠ 0)
      (hAeq :
        A =
          longitudinalAxisRestriction
            B.aligned.endpoint.rawSpecialFiber)
      (hC : C ≠ 0)
      (hfactor :
        A.derivative =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * C)
      (hdegree :
        C.natDegree < A.derivative.natDegree)
      (normal : EndpointResidualNormalForm C)
  | lowNegativeFirst
      (A R : Polynomial K)
      (hpattern : IsLowNegativeFirstSmithPattern B.exponent)
      (hA : A ≠ 0)
      (hAeq :
        A =
          longitudinalCoefficientPolynomial
            B.exponent.b B.exponent.c B.exponent.d
            B.aligned.endpoint.rawSpecialFiber)
      (hR : R ≠ 0)
      (hfactor :
        A =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R)
      (hdegree :
        R.natDegree + 2 = A.natDegree)
      (normal : EndpointResidualNormalForm R)
  | lowNegativeSecond
      (A R : Polynomial K)
      (hpattern : IsLowNegativeSecondSmithPattern B.exponent)
      (hA : A ≠ 0)
      (hAeq :
        A =
          longitudinalCoefficientPolynomial
            B.exponent.b B.exponent.c B.exponent.d
            B.aligned.endpoint.rawSpecialFiber)
      (hR : R ≠ 0)
      (hfactor :
        A =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R)
      (hdegree :
        R.natDegree + 2 = A.natDegree)
      (normal : EndpointResidualNormalForm R)
  | wLinear
      (A R : Polynomial K)
      (hpattern : IsWLinearSmithPattern B.exponent)
      (hA : A ≠ 0)
      (hAeq :
        A =
          longitudinalCoefficientPolynomial
            B.exponent.b B.exponent.c B.exponent.d
            B.aligned.endpoint.rawSpecialFiber)
      (hR : R ≠ 0)
      (hfactor :
        A =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R)
      (hdegree :
        R.natDegree + 2 = A.natDegree)
      (normal : EndpointResidualNormalForm R)

/-- A canonical blocker endpoint therefore has exactly the honest residual
handoff supported by the current library:

* either one of the four concrete blocker residuals has been completely
  normalized by finite endpoint-factor descent; or
* the stored mixed-degree outcome is the already-existing general surviving
  Smith-grade shape.

The second alternative is intentionally retained rather than ruled out by
proof irrelevance or constructor assumptions. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.concreteResidualNormalForm_or_survivingShape
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    Nonempty
        (AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
          (K := K) B) ∨
      HasGeneralSurvivingSmithGradeShape B.exponent := by
  cases B.outcome with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree =>
      left
      rcases exists_endpointResidualNormalForm C hC with ⟨hnormal⟩
      exact
        ⟨.pureLongitudinal
          A C hpattern hA hAeq hC hfactor hdegree hnormal⟩
  | lowNegativeFirst A R hpattern hA hAeq hR hfactor hdegree =>
      left
      rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
      exact
        ⟨.lowNegativeFirst
          A R hpattern hA hAeq hR hfactor hdegree hnormal⟩
  | lowNegativeSecond A R hpattern hA hAeq hR hfactor hdegree =>
      left
      rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
      exact
        ⟨.lowNegativeSecond
          A R hpattern hA hAeq hR hfactor hdegree hnormal⟩
  | wLinear A R hpattern hA hAeq hR hfactor hdegree =>
      left
      rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
      exact
        ⟨.wLinear
          A R hpattern hA hAeq hR hfactor hdegree hnormal⟩
  | surviving hshape =>
      exact Or.inr hshape

/-- The stored blocker `pattern` is already strong enough to recover one of
its four concrete residual normal forms directly.  In particular, the
`surviving` constructor of the coarser `MixedDegreeSmithExponentOutcome`
does not represent a genuine extra blocker branch: for an exponent that is
known to be one of the four blocker patterns, the normalized axis data
reconstructs the corresponding residual again.

This theorem deliberately leaves the older
`concreteResidualNormalForm_or_survivingShape` API in place for downstream
compatibility, while providing the stronger canonical fact for the final
dispatcher. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.concreteResidualNormalForm
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    Nonempty
      (AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
        (K := K) B) := by
  rcases B.aligned.rawSpecialFiber_axisData with
    ⟨hcoll, hzero, hvalue⟩
  rcases B.pattern with hpure | hrest
  · rcases
        projectedSupport_pureLongitudinal_twoEndpointResidualData
          B.aligned.endpoint.rawSpecialFiber B.exponent B.mem hpure
          hcoll hzero hvalue with
      ⟨A, C, hA, hAeq, hC, hfactor, hdegree⟩
    rcases exists_endpointResidualNormalForm C hC with ⟨hnormal⟩
    exact
      ⟨.pureLongitudinal
        A C hpure hA hAeq hC hfactor hdegree hnormal⟩
  · rcases hrest with hfirst | hrest
    · rcases
          projectedSupport_transverseLinear_twoEndpointResidualData
            B.aligned.endpoint.rawSpecialFiber B.exponent B.mem 1
            (smithTransverseExponent_eq_single_one_of_lowNegativeFirst
              B.exponent hfirst)
            hcoll hzero with
        ⟨A, R, hA, hAeq, hR, hfactor, hdegree⟩
      rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
      exact
        ⟨.lowNegativeFirst
          A R hfirst hA hAeq hR hfactor hdegree hnormal⟩
    · rcases hrest with hsecond | hw
      · rcases
            projectedSupport_transverseLinear_twoEndpointResidualData
              B.aligned.endpoint.rawSpecialFiber B.exponent B.mem 0
              (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
                B.exponent hsecond)
              hcoll hzero with
          ⟨A, R, hA, hAeq, hR, hfactor, hdegree⟩
        rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
        exact
          ⟨.lowNegativeSecond
            A R hsecond hA hAeq hR hfactor hdegree hnormal⟩
      · rcases
            projectedSupport_transverseLinear_twoEndpointResidualData
              B.aligned.endpoint.rawSpecialFiber B.exponent B.mem 2
              (smithTransverseExponent_eq_single_two_of_wLinear
                B.exponent hw)
              hcoll hzero with
          ⟨A, R, hA, hAeq, hR, hfactor, hdegree⟩
        rcases exists_endpointResidualNormalForm R hR with ⟨hnormal⟩
        exact
          ⟨.wLinear
            A R hw hA hAeq hR hfactor hdegree hnormal⟩

/-- Every concrete blocker normalization exposes a terminal polynomial that
is nonzero and, crucially, nonzero at the right endpoint `X = 1`.

This is the precise algebraic datum the next geometric blocker adapter must
consume. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.exists_terminalResidual
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (h :
      Nonempty
        (AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
          (K := K) B)) :
    ∃ C : Polynomial K,
      C ≠ 0 ∧ Polynomial.eval 1 C ≠ 0 := by
  rcases h with ⟨R⟩
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        ⟨normal.terminal,
          normal.terminal_ne_zero,
          normal.terminal_eval_one_ne_zero⟩
  | lowNegativeFirst A R hpattern hA hAeq hR hfactor hdegree normal =>
      exact
        ⟨normal.terminal,
          normal.terminal_ne_zero,
          normal.terminal_eval_one_ne_zero⟩
  | lowNegativeSecond A R hpattern hA hAeq hR hfactor hdegree normal =>
      exact
        ⟨normal.terminal,
          normal.terminal_ne_zero,
          normal.terminal_eval_one_ne_zero⟩
  | wLinear A R hpattern hA hAeq hR hfactor hdegree normal =>
      exact
        ⟨normal.terminal,
          normal.terminal_ne_zero,
          normal.terminal_eval_one_ne_zero⟩

end

end HC4.Valuation
