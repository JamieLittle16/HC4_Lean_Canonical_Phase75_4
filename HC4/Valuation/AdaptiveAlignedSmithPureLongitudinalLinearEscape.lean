import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalCurvature
import Mathlib.Tactic

/-!
# Linear transverse support escapes the pure-longitudinal rank-one branch

The only remaining blocker after the green Schur/zero-Schur and quadratic
packet routes is pure longitudinal with all finite recentered Hessian
`2 x 2` minors zero.

This file removes one more apparent residual case without introducing new
geometry.  If the right-recentered special fibre contains any transverse
linear projected exponent

    (1,0,0), (0,1,0), or (0,0,1),

then the same normalized collision data that built the canonical blocker
builds the corresponding transverse-linear residual at that exponent.  The
already-green rank-one Hessian calculation therefore forces the matching
square exponent

    (2,0,0), (0,2,0), or (0,0,2).

All three square competitors already enter persistent packet machinery.
Consequently the genuinely unresolved pure-longitudinal support alternative
has positive transverse support but *no* transverse-linear projected support.
Equivalently, its first positive transverse degree is at least two.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## The three transverse-linear projected support points -/

/-- The right-recentered fibre contains at least one pure transverse-linear
projected Smith exponent. -/
def HasRightRecenteredTransverseLinearCompetitor
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop :=
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  ({ b := 1, c := 0, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G ∨
    ({ b := 0, c := 1, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G ∨
    ({ b := 0, c := 0, d := 1 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3 G

/-- Absence of all three pure transverse-linear projected support points. -/
def IsRightRecenteredTransverseLinearFree
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop :=
  ¬ HasRightRecenteredTransverseLinearCompetitor B

/-! ## Retargeting the green transverse-linear Hessian argument -/

/-- A right-recentered `(1,0,0)` support point forces `(2,0,0)` under the
all-minors hypothesis, even when the canonical blocker itself is the pure
longitudinal exponent. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.firstLinear_forces_firstSquare_of_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (hlin :
      ({ b := 1, c := 0, d := 0 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)) :
    ({ b := 2, c := 0, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber) := by
  let F := B.aligned.endpoint.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let e : SmithSupportExponent := { b := 1, c := 0, d := 0 }

  have heF : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F := by
    have hlin' := hlin
    rw [smithProjectedSupport_longitudinalRightRecenterHom
      B.aligned.endpoint.rawSpecialFiber] at hlin'
    simpa [e, F] using hlin'

  have hpattern : IsLowNegativeSecondSmithPattern e := by
    exact ⟨rfl, rfl, rfl⟩

  rcases B.aligned.rawSpecialFiber_axisData with
    ⟨hcoll, hzero, _hvalue⟩

  rcases
      projectedSupport_transverseLinear_twoEndpointResidualData
        F e heF 0
        (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
          e hpattern)
        hcoll hzero with
    ⟨A, R, _hA, hAeq, _hR, _hfactor, hdegree⟩

  have hquad :=
    rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
      B.aligned.endpoint e 0
      (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
        e hpattern)
      A R hAeq hdegree hall

  have hcoeff : longitudinalCoefficientPolynomial 2 0 0 G ≠ 0 := by
    simpa [G, longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hquad

  exact
    (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
      G ({ b := 2, c := 0, d := 0 } : SmithSupportExponent)).mp hcoeff

/-- A right-recentered `(0,1,0)` support point forces `(0,2,0)`. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.secondLinear_forces_secondSquare_of_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (hlin :
      ({ b := 0, c := 1, d := 0 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)) :
    ({ b := 0, c := 2, d := 0 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber) := by
  let F := B.aligned.endpoint.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let e : SmithSupportExponent := { b := 0, c := 1, d := 0 }

  have heF : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F := by
    have hlin' := hlin
    rw [smithProjectedSupport_longitudinalRightRecenterHom
      B.aligned.endpoint.rawSpecialFiber] at hlin'
    simpa [e, F] using hlin'

  have hpattern : IsLowNegativeFirstSmithPattern e := by
    exact ⟨rfl, rfl, rfl⟩

  rcases B.aligned.rawSpecialFiber_axisData with
    ⟨hcoll, hzero, _hvalue⟩

  rcases
      projectedSupport_transverseLinear_twoEndpointResidualData
        F e heF 1
        (smithTransverseExponent_eq_single_one_of_lowNegativeFirst
          e hpattern)
        hcoll hzero with
    ⟨A, R, _hA, hAeq, _hR, _hfactor, hdegree⟩

  have hquad :=
    rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
      B.aligned.endpoint e 1
      (smithTransverseExponent_eq_single_one_of_lowNegativeFirst
        e hpattern)
      A R hAeq hdegree hall

  have hcoeff : longitudinalCoefficientPolynomial 0 2 0 G ≠ 0 := by
    simpa [G, longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hquad

  exact
    (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
      G ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)).mp hcoeff

/-- A right-recentered `(0,0,1)` support point forces `(0,0,2)`. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.thirdLinear_forces_thirdSquare_of_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (hlin :
      ({ b := 0, c := 0, d := 1 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)) :
    ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
      smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber) := by
  let F := B.aligned.endpoint.rawSpecialFiber
  let G := longitudinalRightRecenterHom (K := K) F
  let e : SmithSupportExponent := { b := 0, c := 0, d := 1 }

  have heF : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F := by
    have hlin' := hlin
    rw [smithProjectedSupport_longitudinalRightRecenterHom
      B.aligned.endpoint.rawSpecialFiber] at hlin'
    simpa [e, F] using hlin'

  have hpattern : IsWLinearSmithPattern e := by
    exact ⟨rfl, rfl, rfl⟩

  rcases B.aligned.rawSpecialFiber_axisData with
    ⟨hcoll, hzero, _hvalue⟩

  rcases
      projectedSupport_transverseLinear_twoEndpointResidualData
        F e heF 2
        (smithTransverseExponent_eq_single_two_of_wLinear
          e hpattern)
        hcoll hzero with
    ⟨A, R, _hA, hAeq, _hR, _hfactor, hdegree⟩

  have hquad :=
    rightRecentered_quadraticCoefficient_ne_zero_of_transverseBlocker_of_allMinors
      B.aligned.endpoint e 2
      (smithTransverseExponent_eq_single_two_of_wLinear
        e hpattern)
      A R hAeq hdegree hall

  have hcoeff : longitudinalCoefficientPolynomial 0 0 2 G ≠ 0 := by
    simpa [G, longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hquad

  exact
    (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
      G ({ b := 0, c := 0, d := 2 } : SmithSupportExponent)).mp hcoeff

/-- Any transverse-linear support in the all-minors branch therefore forces
one of the already-green quadratic axis competitors. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.quadraticCompetitor_of_transverseLinear_of_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (hlin : HasRightRecenteredTransverseLinearCompetitor B) :
    HasRightRecenteredQuadraticAxisCompetitor B := by
  rcases hlin with hfirst | hsecond | hthird
  · exact Or.inl (B.firstLinear_forces_firstSquare_of_allMinors hall hfirst)
  · exact Or.inr (Or.inl
      (B.secondLinear_forces_secondSquare_of_allMinors hall hsecond))
  · exact Or.inr (Or.inr
      (B.thirdLinear_forces_thirdSquare_of_allMinors hall hthird))

/-- Hence any transverse-linear support is already consumed by one of the
persistent quadratic packet constructions. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.quadraticPacket_of_transverseLinear_of_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (hlin : HasRightRecenteredTransverseLinearCompetitor B) :
    Nonempty
        (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
          (K := K) B) ∨
      Nonempty
        (AdaptiveAlignedSmithWSquarePacketEndpoint
          (K := K) B) := by
  have hcomp :=
    B.quadraticCompetitor_of_transverseLinear_of_allMinors hall hlin
  rcases B.packet_or_wSquare_of_quadraticCompetitor hcomp with
    hpacket | hw
  · exact Or.inl hpacket
  · exact Or.inr (B.wSquarePacket hw)

/-! ## The exact remaining support frontier -/

/-- Positive transverse support with all three transverse-linear projected
exponents absent.  This is the genuinely new finite case left after the
existing packet machinery has been exhausted. -/
def HasRightRecenteredHigherTransverseSupport
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop :=
  IsRightRecenteredTransverseLinearFree B ∧
    ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber),
      HasPositiveTotalTransverseDegree e

/-- For a pure-longitudinal blocker, finite support is now exhausted by:

* complete transverse freeness;
* an already-consumed persistent quadratic packet; or
* positive transverse support whose first possible degree is at least two.

The third alternative is the sole finite-support lemma still to eliminate
using the nonzero longitudinal curvature and all-minors identities. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_transverseFree_or_quadraticPacket_or_higherSupport
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hpure : IsPureLongitudinalSmithPattern B.exponent)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    (∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
        d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
      Nonempty
        (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
          (K := K) B) ∨
      Nonempty
        (AdaptiveAlignedSmithWSquarePacketEndpoint
          (K := K) B) ∨
      HasRightRecenteredHigherTransverseSupport B := by
  rcases B.pureLongitudinal_curvature_and_support_frontier hpure with
    ⟨_P, _hcurv, hfree | hpos⟩
  · exact Or.inl hfree
  · have hposG :
        ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom
              (K := K) B.aligned.endpoint.rawSpecialFiber),
          HasPositiveTotalTransverseDegree e := by
      rcases hpos with ⟨e, he, hdeg⟩
      refine ⟨e, ?_, hdeg⟩
      have hsupport :=
        smithProjectedSupport_longitudinalRightRecenterHom
          B.aligned.endpoint.rawSpecialFiber
      rw [hsupport]
      exact he

    by_cases hlin : HasRightRecenteredTransverseLinearCompetitor B
    · rcases B.quadraticPacket_of_transverseLinear_of_allMinors hall hlin with
        hplanar | hw
      · exact Or.inr (Or.inl hplanar)
      · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr ⟨hlin, hposG⟩))

end

end HC4.Valuation
