import HC4.Valuation.AdaptiveAlignedSmithClosingChartProvenance
import HC4.Valuation.AdaptiveSmithWallExposure
import HC4.Newton.TerminalOneZeroAffineRecovery
import HC4.Newton.TerminalTwoZeroKellerReduction
import HC4.Newton.TerminalTwoZeroGradientConjugacy
import Mathlib.Tactic

/-!
# Marked-axis terminal reduction

The lossless adaptive closing source carries a distinguished exact collision
whose special points are `0` and `-e₀`.  This extra marked-point information
is stronger than the arbitrary-point terminal interfaces.

This file records three consequences.

* Any integral diagonal source exposure which actually transports a section
  with nonzero special value in one coordinate must assign weight zero to
  that coordinate.  In particular the longitudinal marked axis can never
  acquire a positive source weight.
* A standard one-zero terminal face cannot carry the canonical collision
  `0 ~ -e₀`, without any use of planar JC2: equality of gradients already
  recovers the unique zero-weight coordinate.
* In the standard two-zero terminal face, the same canonical collision
  produces a genuine collision of the honest planar Keller map supplied by
  the two-zero normal form.  This identifies exactly why the remaining
  two-zero endpoint is the genuine planar injectivity obstruction.

No JC2 hypothesis is used in this module.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- If an integral adaptive source section has nonzero special value in a
coordinate, that coordinate must have source weight zero. -/
theorem integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
    (W : Fin 4 → ℕ)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasIntegralAdaptiveSmithSection W a)
    (i : Fin 4)
    (ha : Polynomial.constantCoeff (a i) ≠ 0) :
    W i = 0 := by
  by_contra hne
  have hpos : 1 ≤ W i := Nat.one_le_iff_ne_zero.mpr hne
  have hXpow : Polynomial.X ^ W i ∣ a i := hdiv i
  have hXstep :
      (Polynomial.X : Polynomial K) ∣ (Polynomial.X : Polynomial K) ^ W i := by
    simpa only [pow_one] using
      (polynomial_X_pow_dvd_X_pow_of_le (K := K) 1 (W i) hpos)
  have hXdiv : (Polynomial.X : Polynomial K) ∣ a i := by
    exact dvd_trans hXstep hXpow
  exact ha (Polynomial.X_dvd_iff.mp hXdiv)

/-- The longitudinal component of the honest right-recentered marked section
has special value `-1`, hence in particular is nonzero. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredRightSection_constantCoeff_zero_ne
    [CharZero K]
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    Polynomial.constantCoeff
        (E.rightRecenteredRightSection (0 : Fin 4)) ≠ 0 := by
  have h := congrFun E.rightRecenteredRightSection_specialPoint (0 : Fin 4)
  change
    Polynomial.constantCoeff
        (E.rightRecenteredRightSection (0 : Fin 4)) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) (0 : Fin 4) at h
  rw [h]
  simp [coordinateAxisPoint]

/-- Consequently any honest integral source diagonal which transports the
right-recentered marked section must assign longitudinal source weight zero.
This is the formal marked-axis obstruction to a strictly-positive terminal
source lattice. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.longitudinalSourceWeight_zero_of_integralRightSection
    [CharZero K]
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (W : Fin 4 → ℕ)
    (hdiv :
      HasIntegralAdaptiveSmithSection
        W E.rightRecenteredRightSection) :
    W (0 : Fin 4) = 0 := by
  exact
    integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
      W E.rightRecenteredRightSection hdiv (0 : Fin 4)
      E.rightRecenteredRightSection_constantCoeff_zero_ne

end

end HC4.Valuation

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The canonical negative longitudinal axis point used by the adaptive
right-recentered collision. -/
noncomputable def negativeLongitudinalAxisPoint : Fin 4 → K :=
  fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i

/-- **One-zero marked-axis elimination, without JC2.**

In a standard one-zero terminal face, equality of full gradients already
recovers coordinate `0` unconditionally.  Hence the canonical collision
between `0` and `-e₀` is impossible before any planar injectivity theorem is
used. -/
theorem standardOneZero_negativeLongitudinalAxis_collision_impossible
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K))) :
    False := by
  have hgrad :
      mvGradientMap F (fun _ : Fin 4 => (0 : K)) =
        mvGradientMap F (negativeLongitudinalAxisPoint (K := K)) :=
    mvGradientMap_eq_of_exactCollision
      F (fun _ : Fin 4 => (0 : K))
      (negativeLongitudinalAxisPoint (K := K)) hcoll
  have h0 :=
    standardOneZero_gradient_eq_recovers_zero
      ha had hhom hMA hgrad
  have hbad : (0 : K) = -1 := by
    simpa [negativeLongitudinalAxisPoint, coordinateAxisPoint] using h0
  exact (by simp : (0 : K) ≠ -1) hbad

/-- An explicit collision of a genuine planar Keller map. -/
structure PlanarKellerCollisionData (K : Type*) [Field K] where
  map : HC4.PlanarPolynomialMap K
  leftPoint : HC4.Point2 K
  rightPoint : HC4.Point2 K
  distinct : leftPoint ≠ rightPoint
  keller : HC4.HasNonzeroConstantPlanarJacobian map
  collision :
    HC4.planarPolynomialMapEval map leftPoint =
      HC4.planarPolynomialMapEval map rightPoint

/-- **Two-zero marked-axis reduction to a planar Keller collision.**

A standard two-zero Monge--Ampère terminal face carrying the canonical
collision `0 ~ -e₀` produces an honest planar Keller map with a collision at
two distinct base points.  No JC2 assumption is used: this theorem is the
precise reduction *to* the remaining planar injectivity problem. -/
theorem standardTwoZero_negativeLongitudinalAxis_hasPlanarKellerCollision
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K))) :
    Nonempty (PlanarKellerCollisionData K) := by
  rcases
      standardTwoZero_mongeAmpere_hasPlanarKellerModel
        hd hhom hMA with
    ⟨A, C, hA, hC, hKeller⟩
  let G : HC4.PlanarPolynomialMap K :=
    standardPlanarPairMap A C
  let p : Fin 4 → K := fun _ => 0
  let q : Fin 4 → K := negativeLongitudinalAxisPoint (K := K)
  let u : HC4.Point2 K := standardBasePoint p
  let v : HC4.Point2 K := standardBasePoint q

  have hgrad : mvGradientMap F p = mvGradientMap F q :=
    mvGradientMap_eq_of_exactCollision F p q hcoll
  have hpositive :
      standardFibrePoint (mvGradientMap F p) =
        standardFibrePoint (mvGradientMap F q) :=
    congrArg standardFibrePoint hgrad
  have hplanar :
      HC4.planarPolynomialMapEval G u =
        HC4.planarPolynomialMapEval G v := by
    calc
      HC4.planarPolynomialMapEval G u =
          standardFibrePoint (mvGradientMap F p) := by
            symm
            exact standardTwoZero_gradient_positive_eq_planar hA hC p
      _ = standardFibrePoint (mvGradientMap F q) := hpositive
      _ = HC4.planarPolynomialMapEval G v := by
            exact standardTwoZero_gradient_positive_eq_planar hA hC q

  have huv : u ≠ v := by
    intro huv'
    have h0 := congrFun huv' (0 : Fin 2)
    have hbad : (0 : K) = -1 := by
      simpa [u, v, p, q, standardBasePoint,
        negativeLongitudinalAxisPoint, coordinateAxisPoint] using h0
    exact (by simp : (0 : K) ≠ -1) hbad

  exact ⟨{
    map := G
    leftPoint := u
    rightPoint := v
    distinct := huv
    keller := hKeller
    collision := hplanar
  }⟩

end

end HC4.Newton
