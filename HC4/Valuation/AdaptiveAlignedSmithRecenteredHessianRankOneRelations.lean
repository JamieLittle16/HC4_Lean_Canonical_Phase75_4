import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianShearCharts
import Mathlib.Tactic

/-!
# Rank-one determinantal residual of the recentered adaptive blocker Hessian

The green coordinate-chart and shear-chart modules leave one algebraic
residual branch: no determinant-preserving chart exposes a nonzero active
`2 x 2` Hessian minor at parameter zero.

This file packages that branch without prematurely identifying it with a
matrix-rank API over the polynomial coefficient ring.

There are two elementary active-plane moves.

* `swap02` exchanges displayed coordinates `0` and `2`.  It preserves the
  full four-block determinant and turns the principal `(2,1)` minor into the
  active `(0,1)` minor.
* `shear02`, already green, replaces `e₀` by `e₀ + e₂`.  Once the two
  adjacent principal minors vanish, a nonzero three-index cross minor becomes
  a nonzero active determinant.

Consequently, if neither ordinary charts nor these elementary transformed
charts enter the existing Schur/zero-Schur machinery, then for *every*
coordinate permutation `rho` the constant recentered Hessian satisfies

    Δ₀₁ = 0,
    Δ₂₁ = 0,
    H₀₂ H₁₁ - H₀₁ H₁₂ = 0.

Because `rho` is arbitrary these are the division-free principal and
three-index determinantal relations of a rank-one symmetric matrix.  We keep
that statement explicit as a named predicate; the next file can either turn
it into a global all-`2 x 2`-minors certificate or consume it directly with
the Hessian integrability/linear-power machinery.

No JC2 input occurs here.
-/

namespace HC4.Newton

noncomputable section

universe v

variable {R : Type v} [CommRing R]

namespace GeneralFourBlock

/-- Exchange displayed coordinates `0` and `2` in a symmetric four-block.
The corresponding coordinate order is `(2,1,0,3)`. -/
noncomputable def swap02 (H : GeneralFourBlock R) : GeneralFourBlock R where
  a := H.x
  b := H.r
  d := H.d
  p := H.p
  q := H.y
  r := H.b
  s := H.s
  x := H.a
  y := H.q
  z := H.z

/-- Simultaneously swapping rows and columns `0` and `2` preserves the full
four-block determinant. -/
theorem swap02_determinantCore (H : GeneralFourBlock R) :
    H.swap02.determinantCore = H.determinantCore := by
  unfold swap02 determinantCore
  ring

/-- The active determinant after swapping `0` and `2` is the old `(2,1)`
principal minor. -/
theorem swap02_activeDet (H : GeneralFourBlock R) :
    H.swap02.activeDet = H.x * H.d - H.r * H.r := by
  unfold swap02 activeDet
  ring

end GeneralFourBlock

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u v

variable {K : Type u} [Field K]

/-! ## Parameter-zero swap chart -/

/-- Constant coefficient of the swapped active determinant is exactly the
second displayed principal Hessian minor at parameter zero. -/
theorem swap02_activeDet_coeff_zero
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    H.swap02.activeDet.coeff 0 =
      H.x.coeff 0 * H.d.coeff 0 - H.r.coeff 0 * H.r.coeff 0 := by
  rw [GeneralFourBlock.swap02_activeDet]
  simp [Polynomial.coeff_zero_eq_eval_zero]

/-- A nonzero second principal constant minor can itself be used as an active
chart after the determinant-preserving `0 <-> 2` swap. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredSwap02Schur_or_zeroSchur_of_secondPrincipal
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (rho : Equiv.Perm (Fin 4))
    (hdefect : 0 < B.aligned.endpoint.defect)
    (h21 :
      let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
        rho B.aligned.endpoint
      H.x.coeff 0 * H.d.coeff 0 -
        H.r.coeff 0 * H.r.coeff 0 ≠ 0) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) := by
  let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
    rho B.aligned.endpoint
  let Hs := H.swap02

  have hactive : Hs.activeDet.coeff 0 ≠ 0 := by
    dsimp [Hs]
    rw [swap02_activeDet_coeff_zero]
    simpa [H] using h21

  have hfull :
      Hs.determinantCore =
        Polynomial.X ^ B.aligned.endpoint.defect := by
    dsimp [Hs]
    rw [GeneralFourBlock.swap02_determinantCore]
    dsimp [H]
    exact B.rightRecenteredHessianFourBlock_determinantCore rho

  exact B.schur_or_zeroSchur_of_exactBlock
    Hs hdefect hfull hactive

/-! ## Division-free rank-one residual predicate -/

/-- The constant recentered Hessian satisfies the rank-one determinantal
relations exposed by every coordinate ordering.

The predicate is deliberately stated in terms of coefficient `0` of the
honest Hessian series.  By the green special-fibre theorem these coefficients
are literally the entries of the Hessian of the right-recentered special
fibre.

For each `rho` we retain:

* the active `(0,1)` principal minor;
* the `(2,1)` principal minor;
* the three-index cross minor joining those two planes.

Since `rho` is arbitrary, this records all corresponding coordinate
relations without choosing divisions or pivots. -/
def HasAdaptiveAlignedRightRecenteredHessianRankOneRelations
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) : Prop :=
  ∀ rho : Equiv.Perm (Fin 4),
    let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E
    H.activeDet.coeff 0 = 0 ∧
      H.x.coeff 0 * H.d.coeff 0 -
          H.r.coeff 0 * H.r.coeff 0 = 0 ∧
      H.p.coeff 0 * H.d.coeff 0 -
          H.b.coeff 0 * H.r.coeff 0 = 0

/-- **Exhaustive recentered blocker Hessian frontier.**

At positive defect, every canonical blocker is in one of the two already
proved Schur architectures, or else its honest recentered special-fibre
Hessian satisfies the full permutation family of division-free rank-one
relations above.

The proof is purely eliminative:

1. a nonzero coordinate-principal active minor enters the green Schur split;
2. if some second displayed principal minor is nonzero, `swap02` exposes it;
3. once both principal minors vanish, a nonzero cross minor is exposed by the
   already-green `shear02` chart;
4. if none of those escapes occurs, all three relations vanish for every
   permutation.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredSchur_or_zeroSchur_or_rankOneRelations
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) ∨
      HasAdaptiveAlignedRightRecenteredHessianRankOneRelations
        B.aligned.endpoint := by
  classical
  rcases
      B.rightRecenteredSchur_or_zeroSchur_or_allActiveMinorsZero hdefect with
    hschur | hzero | hprincipal
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · by_cases hsecond :
        ∃ rho : Equiv.Perm (Fin 4),
          let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
            rho B.aligned.endpoint
          H.x.coeff 0 * H.d.coeff 0 -
            H.r.coeff 0 * H.r.coeff 0 ≠ 0
    · rcases hsecond with ⟨rho, h21⟩
      rcases
          B.rightRecenteredSwap02Schur_or_zeroSchur_of_secondPrincipal
            rho hdefect h21 with
        hschur | hzero
      · exact Or.inl hschur
      · exact Or.inr (Or.inl hzero)
    · by_cases hcross :
          ∃ rho : Equiv.Perm (Fin 4),
            let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
              rho B.aligned.endpoint
            H.p.coeff 0 * H.d.coeff 0 -
              H.b.coeff 0 * H.r.coeff 0 ≠ 0
      · rcases hcross with ⟨rho, hcrossrho⟩
        have h01 :
            (adaptiveAlignedEndpointRightRecenteredHessianFourBlock
              rho B.aligned.endpoint).activeDet.coeff 0 = 0 := by
          rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
          exact hprincipal rho

        have h21 :
            let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
              rho B.aligned.endpoint
            H.x.coeff 0 * H.d.coeff 0 -
              H.r.coeff 0 * H.r.coeff 0 = 0 := by
          dsimp only
          by_contra hne
          apply hsecond
          exact ⟨rho, hne⟩

        rcases
            B.rightRecenteredShear02Schur_or_zeroSchur_of_cross
              rho hdefect h01 h21 hcrossrho with
          hschur | hzero
        · exact Or.inl hschur
        · exact Or.inr (Or.inl hzero)

      · right
        right
        intro rho
        let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
          rho B.aligned.endpoint

        have h01 : H.activeDet.coeff 0 = 0 := by
          dsimp [H]
          rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
          exact hprincipal rho

        have h21 :
            H.x.coeff 0 * H.d.coeff 0 -
              H.r.coeff 0 * H.r.coeff 0 = 0 := by
          by_contra hne
          apply hsecond
          refine ⟨rho, ?_⟩
          simpa [H] using hne

        have hcross0 :
            H.p.coeff 0 * H.d.coeff 0 -
              H.b.coeff 0 * H.r.coeff 0 = 0 := by
          by_contra hne
          apply hcross
          refine ⟨rho, ?_⟩
          simpa [H] using hne

        exact ⟨h01, h21, hcross0⟩

/-- The residual rank-one branch retains the exact same first longitudinal
departure which led to the Hessian analysis.  This packages the two facts the
next rigidity theorem should consume together, so no provenance is lost in
the final dispatcher. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFrontier_with_firstDeparture
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) ∨
      (HasFirstExactSmithExponentLongitudinalDeparture
          (polynomialFamilySpecialFiber
            B.aligned.endpoint.rightRecenteredFamily)
          B.exponent ∧
        HasAdaptiveAlignedRightRecenteredHessianRankOneRelations
          B.aligned.endpoint) := by
  rcases B.rightRecenteredSchur_or_zeroSchur_or_rankOneRelations hdefect with
    hschur | hzero | hrankOne
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · exact Or.inr (Or.inr
      ⟨B.firstLongitudinalDeparture_on_rightRecenteredFamily,
        hrankOne⟩)

end

end HC4.Valuation
