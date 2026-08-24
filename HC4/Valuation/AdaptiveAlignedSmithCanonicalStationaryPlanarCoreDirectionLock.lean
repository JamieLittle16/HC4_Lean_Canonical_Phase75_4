import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreMixedLayerCross
import Mathlib.Tactic

/-!
# Direction lock from the mixed top-layer Hessian equation

The previous stage gives, for the maximal layer `H = a L^D` and the next
homogeneous layer `G`, the exact cross equation

    binaryHessianDetCross H G = 0.

For `D >= 2`, the Hessian of `a L^D` is a nonzero scalar-polynomial multiple
of the rank-one matrix `c c^T`, where

    L = c₀ X₀ + c₁ X₁.

Consequently the cross equation is the same nonzero factor times

    (c₁ ∂₀ - c₀ ∂₁)^2 G.

This file performs that cancellation exactly.  It deliberately does *not*
replace `D_perp^2 G = 0` by `D_perp G = 0`: that implication is false for a
general homogeneous binary form.  The next stage classifies the genuine
second-order kernel.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The constant direction transverse to the linear form
`c₀ X₀ + c₁ X₁`. -/
def binaryLinearFormTransverseDeriv
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  binaryDirectionalDeriv (c 1) (-c 0) (0 : Fin 2) 1 P

/-- A coordinate derivative of the canonical gradient-ratio linear form is
its corresponding scalar coefficient. -/
theorem pderiv_gradientRatioLinearForm_fin
    {n : ℕ}
    (c : Fin n → K)
    (i : Fin n) :
    MvPolynomial.pderiv i (gradientRatioLinearForm c) =
      MvPolynomial.C (c i) := by
  classical
  simp [gradientRatioLinearForm, MvPolynomial.pderiv_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

/-- Derivative of a positive power of the canonical linear form. -/
theorem pderiv_gradientRatioLinearForm_pow_succ
    {nvar : ℕ}
    (c : Fin nvar → K)
    (i : Fin nvar) :
    ∀ n : ℕ,
      MvPolynomial.pderiv i ((gradientRatioLinearForm c) ^ (n + 1)) =
        MvPolynomial.C (((n + 1 : ℕ) : K) * c i) *
          (gradientRatioLinearForm c) ^ n := by
  intro n
  induction n with
  | zero =>
      simp [pderiv_gradientRatioLinearForm_fin]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      rw [pow_succ, MvPolynomial.pderiv_mul]
      rw [ih, pderiv_gradientRatioLinearForm_fin]
      have hscalar :
          (((n + 1 : ℕ) : K) * c i + c i) =
            (((n + 2 : ℕ) : K) * c i) := by
        push_cast
        ring
      rw [pow_succ]
      rw [← hscalar, MvPolynomial.C_add]
      ring

/-- Hessian entry of `a * L^(n+2)`. -/
theorem hessian_C_mul_gradientRatioLinearForm_pow_add_two
    (a : K)
    (c : Fin 2 → K)
    (n : ℕ)
    (i j : Fin 2) :
    HC4.Polynomial.hessian
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) i j =
      MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) * c i * c j) *
        (gradientRatioLinearForm c) ^ n := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c i (n + 1)]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c j n]
  push_cast
  simp only [MvPolynomial.C_mul]
  ring

/-- Expanded second derivative in the direction transverse to `c`. -/
theorem binaryLinearFormTransverseDeriv_sq_expand
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K) :
    binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) =
      MvPolynomial.C (c 1 * c 1) *
          directionalSecondDerivative (0 : Fin 2) G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G +
        MvPolynomial.C (c 0 * c 0) *
          directionalSecondDerivative (1 : Fin 2) G := by
  unfold binaryLinearFormTransverseDeriv
  rw [binaryDirectionalDeriv_self_expand]
  unfold binaryDirectionalDeriv directionalSecondDerivative
    directionalMixedDerivative
  simp only [MvPolynomial.C_neg]
  rw [pderiv_comm_backport (0 : Fin 2) 1 G]
  simp only [MvPolynomial.C_mul]
  ring

/-- Exact factorisation of the mixed Hessian polarisation against a power of
one binary linear form. -/
theorem binaryHessianDetCross_linearPower_factor
    (a : K)
    (c : Fin 2 → K)
    (n : ℕ)
    (G : MvPolynomial (Fin 2) K) :
    binaryHessianDetCross
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) G =
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
          (gradientRatioLinearForm c) ^ n) *
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) := by
  have h00 := hessian_C_mul_gradientRatioLinearForm_pow_add_two
    a c n (0 : Fin 2) 0
  have h11 := hessian_C_mul_gradientRatioLinearForm_pow_add_two
    a c n (1 : Fin 2) 1
  have h01 := hessian_C_mul_gradientRatioLinearForm_pow_add_two
    a c n (1 : Fin 2) 0
  have hsq := binaryLinearFormTransverseDeriv_sq_expand c G
  rw [hsq]
  unfold binaryHessianDetCross directionalSecondDerivative
    directionalMixedDerivative
  simp only [← HC4.Polynomial.hessian_apply]
  rw [h00, h11, h01]
  push_cast
  simp only [MvPolynomial.C_mul]
  ring_nf

/-- The mixed top-layer equation forces the next homogeneous layer to have
zero second derivative in the constant direction transverse to the top
linear form. -/
theorem binaryLinearPower_cross_zero_implies_transverse_sq_zero
    (H G : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hD : 2 ≤ D)
    (hHne : H ≠ 0)
    (a : K)
    (c : Fin 2 → K)
    (normalForm :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (hcross : binaryHessianDetCross H G = 0) :
    binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, D = n + 2 := by
    refine ⟨D - 2, ?_⟩
    omega
  let L : MvPolynomial (Fin 2) K := gradientRatioLinearForm c
  have ha : a ≠ 0 := by
    intro ha
    apply hHne
    rw [normalForm, ha]
    simp
  have hL : L ≠ 0 := by
    intro hL
    apply hHne
    rw [normalForm]
    change MvPolynomial.C a * L ^ (n + 2) = 0
    rw [hL]
    simp
  have hn2 : (((n + 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  have hn1 : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hs :
      a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha hn2) hn1
  have hfactor :
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        L ^ n : MvPolynomial (Fin 2) K) ≠ 0 := by
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hs) (pow_ne_zero n hL)
  have hfac := binaryHessianDetCross_linearPower_factor a c n G
  rw [← normalForm] at hfac
  have hprod :
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        L ^ n) *
          binaryLinearFormTransverseDeriv c
            (binaryLinearFormTransverseDeriv c G) = 0 := by
    rw [← hfac, hcross]
  exact (mul_eq_zero.mp hprod).resolve_left hfactor

/-- Frontier after locking the next layer to second order in the transverse
direction of the top linear form. -/
inductive BinarySingularHessianTopLayerDirectionLockFrontier
    (Q : MvPolynomial (Fin 2) K) : Type (u + 1)
  | lowDegree
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
  | nonlinearCollapsed
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (Q_eq_H : Q = H)
  | nonlinearNextLayer
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero :
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) = 0)

/-- Every nonzero binary singular-Hessian polynomial reaches the direction
lock frontier. -/
theorem binarySingularHessian_topLayerDirectionLockFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianTopLayerDirectionLockFrontier Q) := by
  rcases binarySingularHessian_topLayerCrossFrontier Q hQ hdet with ⟨F⟩
  cases F with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
        a c normalForm Q_eq_H⟩
  | nonlinearNextLayer D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D G_eq G_ne_zero remainder_maximal
      G_homogeneous cross_zero =>
      have hsquare := binaryLinearPower_cross_zero_implies_transverse_sq_zero
        H G D hD H_ne_zero a c normalForm cross_zero
      exact ⟨.nonlinearNextLayer D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D G_eq G_ne_zero
        remainder_maximal G_homogeneous hsquare⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing direction-lock theorem for the actual stationary HC4
binary face. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.topLayerDirectionLockFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianTopLayerDirectionLockFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_topLayerDirectionLockFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
