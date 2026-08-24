import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreForcedCompensator
import Mathlib.Tactic

/-!
# Exact transverse order of the forced stationary compensator

The forced-compensator stage produces, in the genuinely curved branch,

    H = a L^D,
    D_perp^2 G = 0,
    D_perp G != 0,
    B(H,K) = - det Hess G,

with `K` a strictly lower nonlinear homogeneous layer.

This file packages the invariant needed for the final finite staircase.
For the constant derivation

    D_perp = c₁ ∂₀ - c₀ ∂₁

we define the exact transverse order of a polynomial by

    D_perp^r P != 0,
    D_perp^(r+1) P = 0.

The curved layer `G` has exact order one.  The main theorem here proves that
its forced compensator `K` has exact order two:

    D_perp^2 K != 0,
    D_perp^3 K = 0.

The proof is coordinate free.  The factorisation already proved for the
linear-power top layer gives

    B(H,K) = A L^(D-2) D_perp^2 K.

Nonvanishing of `det Hess G` immediately gives `D_perp^2 K != 0`.  To prove
the third derivative vanishes, first note that `D_perp(det Hess G)=0` whenever
`D_perp^2 G=0`.  This follows from the two negative-square identities of the
curvature stage.  Differentiate the compensation equation.  Since
`D_perp L=0`, all factors except `D_perp^2 K` are constant along `D_perp`;
nonvanishing of the top Hessian factor then cancels and yields
`D_perp^3 K=0`.

Thus the finite-descent branch now carries the exact transverse-order jump

    1  -->  2.

The generic staircase theorem can iterate this invariant without choosing a
complementary source coordinate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Iterated transverse derivation -/

/-- Iteration of the constant direction transverse to
`gradientRatioLinearForm c`. -/
def iteratedBinaryLinearFormTransverseDeriv
    (c : Fin 2 → K) :
    ℕ → MvPolynomial (Fin 2) K → MvPolynomial (Fin 2) K
  | 0, P => P
  | n + 1, P =>
      binaryLinearFormTransverseDeriv c
        (iteratedBinaryLinearFormTransverseDeriv c n P)

@[simp] theorem iteratedBinaryLinearFormTransverseDeriv_zero
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    iteratedBinaryLinearFormTransverseDeriv c 0 P = P := rfl

@[simp] theorem iteratedBinaryLinearFormTransverseDeriv_succ
    (c : Fin 2 → K)
    (n : ℕ)
    (P : MvPolynomial (Fin 2) K) :
    iteratedBinaryLinearFormTransverseDeriv c (n + 1) P =
      binaryLinearFormTransverseDeriv c
        (iteratedBinaryLinearFormTransverseDeriv c n P) := rfl

/-- Exact order `r` for the constant transverse derivation. -/
def HasExactBinaryLinearFormTransverseOrder
    (c : Fin 2 → K)
    (r : ℕ)
    (P : MvPolynomial (Fin 2) K) : Prop :=
  iteratedBinaryLinearFormTransverseDeriv c r P ≠ 0 ∧
    iteratedBinaryLinearFormTransverseDeriv c (r + 1) P = 0

/-- Homogeneity is preserved under repeated transverse differentiation, with
ordinary degree dropping by the number of differentiations. -/
theorem iteratedBinaryLinearFormTransverseDeriv_isHomogeneous
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K)
    (E r : ℕ)
    (hhom : P.IsHomogeneous E) :
    (iteratedBinaryLinearFormTransverseDeriv c r P).IsHomogeneous (E - r) := by
  induction r with
  | zero => simpa using hhom
  | succ r ih =>
      rw [iteratedBinaryLinearFormTransverseDeriv_succ]
      have h := binaryLinearFormTransverseDeriv_isHomogeneous
        c (iteratedBinaryLinearFormTransverseDeriv c r P) (E - r) ih
      have hdeg : (E - r) - 1 = E - (r + 1) := by omega
      simpa [hdeg] using h

/-! ## Elementary derivation identities -/

/-- The transverse constant derivation satisfies the Leibniz rule. -/
theorem binaryLinearFormTransverseDeriv_mul
    (c : Fin 2 → K)
    (P Q : MvPolynomial (Fin 2) K) :
    binaryLinearFormTransverseDeriv c (P * Q) =
      binaryLinearFormTransverseDeriv c P * Q +
        P * binaryLinearFormTransverseDeriv c Q := by
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
  simp only [MvPolynomial.pderiv_mul]
  ring

/-- Constants are killed by the transverse derivation. -/
@[simp] theorem binaryLinearFormTransverseDeriv_C
    (c : Fin 2 → K)
    (a : K) :
    binaryLinearFormTransverseDeriv c (MvPolynomial.C a) = 0 := by
  simp [binaryLinearFormTransverseDeriv, binaryDirectionalDeriv]

/-- The transverse derivation commutes with negation. -/
theorem binaryLinearFormTransverseDeriv_neg
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    binaryLinearFormTransverseDeriv c (-P) =
      - binaryLinearFormTransverseDeriv c P := by
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
  simp only [map_neg, MvPolynomial.C_neg]
  ring

/-- The top linear form itself is invariant along its transverse direction. -/
@[simp] theorem binaryLinearFormTransverseDeriv_gradientRatioLinearForm
    (c : Fin 2 → K) :
    binaryLinearFormTransverseDeriv c (gradientRatioLinearForm c) = 0 := by
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
  rw [pderiv_gradientRatioLinearForm_fin c (0 : Fin 2)]
  rw [pderiv_gradientRatioLinearForm_fin c (1 : Fin 2)]
  simp only [MvPolynomial.C_neg, ← MvPolynomial.C_mul]
  rw [mul_comm (c 1) (c 0)]
  simp

/-- Every power of the top linear form is invariant in the same transverse
direction. -/
@[simp] theorem binaryLinearFormTransverseDeriv_gradientRatioLinearForm_pow
    (c : Fin 2 → K)
    (n : ℕ) :
    binaryLinearFormTransverseDeriv c ((gradientRatioLinearForm c) ^ n) = 0 := by
  induction n with
  | zero =>
      simpa using binaryLinearFormTransverseDeriv_C c (1 : K)
  | succ n ih =>
      rw [pow_succ, binaryLinearFormTransverseDeriv_mul, ih]
      simp

/-- A constant multiple of a power of the top linear form is also locked. -/
@[simp] theorem binaryLinearFormTransverseDeriv_C_mul_gradientRatioLinearForm_pow
    (c : Fin 2 → K)
    (a : K)
    (n : ℕ) :
    binaryLinearFormTransverseDeriv c
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ n) = 0 := by
  rw [binaryLinearFormTransverseDeriv_mul]
  simp

/-- The transverse derivation commutes with the first binary partial. -/
theorem binaryLinearFormTransverseDeriv_pderiv_zero
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    binaryLinearFormTransverseDeriv c (MvPolynomial.pderiv (0 : Fin 2) P) =
      MvPolynomial.pderiv (0 : Fin 2)
        (binaryLinearFormTransverseDeriv c P) := by
  unfold binaryLinearFormTransverseDeriv
  exact (pderiv_binaryDirectionalDeriv_first
    (c 1) (-c 0) (0 : Fin 2) (1 : Fin 2) P).symm

/-- The transverse derivation commutes with the second binary partial. -/
theorem binaryLinearFormTransverseDeriv_pderiv_one
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K) :
    binaryLinearFormTransverseDeriv c (MvPolynomial.pderiv (1 : Fin 2) P) =
      MvPolynomial.pderiv (1 : Fin 2)
        (binaryLinearFormTransverseDeriv c P) := by
  unfold binaryLinearFormTransverseDeriv
  exact (pderiv_binaryDirectionalDeriv_second
    (c 1) (-c 0) (0 : Fin 2) (1 : Fin 2) P).symm

/-! ## The determinant is locked after second-order direction lock -/

/-- If the defining top linear form is nonzero, one of its two scalar
coefficients is nonzero. -/
theorem gradientRatioLinearForm_component_ne_zero
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0) :
    c 0 ≠ 0 ∨ c 1 ≠ 0 := by
  by_cases hc0 : c 0 = 0
  · right
    intro hc1
    have hc : c = 0 := by
      funext i
      fin_cases i
      · simpa using hc0
      · simpa using hc1
    apply hL
    rw [hc]
    simp [gradientRatioLinearForm]
  · exact Or.inl hc0

/-- Nonzero linear-power normal form forces the underlying linear form to be
nonzero. -/
theorem gradientRatioLinearForm_ne_zero_of_linearPower_ne_zero
    (H : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hDpos : 0 < D)
    (hHne : H ≠ 0)
    (a : K)
    (c : Fin 2 → K)
    (normalForm :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D) :
    gradientRatioLinearForm c ≠ 0 := by
  intro hL
  apply hHne
  have hDne : D ≠ 0 := Nat.ne_of_gt hDpos
  rw [normalForm, hL, zero_pow hDne]
  simp

/-- Once `D_perp^2 G = 0`, the Hessian determinant of `G` itself is invariant
along `D_perp`.  This is the coordinate-free form of the fact that a binary
polynomial affine in the transverse coordinate has determinant depending
only on the locked coordinate. -/
theorem binaryLinearFormTransverseDeriv_hessianDet_eq_zero_of_sq_zero
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0) :
    binaryLinearFormTransverseDeriv c
      (binaryDirectionalHessianDet (0 : Fin 2) 1 G) = 0 := by
  rcases gradientRatioLinearForm_component_ne_zero c hL with hc0 | hc1
  · have hid := binaryHessianDet_mul_c0_sq_eq_neg_sq c G hsq
    let P : MvPolynomial (Fin 2) K := binaryLinearFormTransverseDeriv c G
    let q : MvPolynomial (Fin 2) K := MvPolynomial.pderiv (0 : Fin 2) P
    have hP : binaryLinearFormTransverseDeriv c P = 0 := by
      simpa [P] using hsq
    have hq : binaryLinearFormTransverseDeriv c q = 0 := by
      dsimp [q]
      rw [binaryLinearFormTransverseDeriv_pderiv_zero]
      rw [hP]
      simp
    have hid' :
        MvPolynomial.C (c 0 * c 0) *
            binaryDirectionalHessianDet (0 : Fin 2) 1 G =
          -(q * q) := by
      simpa [P, q, pow_two] using hid
    have hd := congrArg (binaryLinearFormTransverseDeriv c) hid'
    rw [binaryLinearFormTransverseDeriv_mul,
      binaryLinearFormTransverseDeriv_C,
      binaryLinearFormTransverseDeriv_neg,
      binaryLinearFormTransverseDeriv_mul, hq] at hd
    simp only [zero_mul, zero_add, mul_zero, add_zero, neg_zero] at hd
    have hC :
        (MvPolynomial.C (c 0 * c 0) : MvPolynomial (Fin 2) K) ≠ 0 := by
      exact MvPolynomial.C_ne_zero.mpr (mul_ne_zero hc0 hc0)
    exact (mul_eq_zero.mp hd).resolve_left hC
  · have hid := binaryHessianDet_mul_c1_sq_eq_neg_sq c G hsq
    let P : MvPolynomial (Fin 2) K := binaryLinearFormTransverseDeriv c G
    let q : MvPolynomial (Fin 2) K := MvPolynomial.pderiv (1 : Fin 2) P
    have hP : binaryLinearFormTransverseDeriv c P = 0 := by
      simpa [P] using hsq
    have hq : binaryLinearFormTransverseDeriv c q = 0 := by
      dsimp [q]
      rw [binaryLinearFormTransverseDeriv_pderiv_one]
      rw [hP]
      simp
    have hid' :
        MvPolynomial.C (c 1 * c 1) *
            binaryDirectionalHessianDet (0 : Fin 2) 1 G =
          -(q * q) := by
      simpa [P, q, pow_two] using hid
    have hd := congrArg (binaryLinearFormTransverseDeriv c) hid'
    rw [binaryLinearFormTransverseDeriv_mul,
      binaryLinearFormTransverseDeriv_C,
      binaryLinearFormTransverseDeriv_neg,
      binaryLinearFormTransverseDeriv_mul, hq] at hd
    simp only [zero_mul, zero_add, mul_zero, add_zero, neg_zero] at hd
    have hC :
        (MvPolynomial.C (c 1 * c 1) : MvPolynomial (Fin 2) K) ≠ 0 := by
      exact MvPolynomial.C_ne_zero.mpr (mul_ne_zero hc1 hc1)
    exact (mul_eq_zero.mp hd).resolve_left hC

/-! ## Exact order two of the forced compensator -/

/-- The nonzero scalar-linear-form Hessian factor attached to a nonlinear
linear-power top layer. -/
theorem linearPowerTopHessianFactor_ne_zero
    (H : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hD : 2 ≤ D)
    (hHne : H ≠ 0)
    (a : K)
    (c : Fin 2 → K)
    (normalForm :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D) :
    ∃ n : ℕ,
      D = n + 2 ∧
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        (gradientRatioLinearForm c) ^ n : MvPolynomial (Fin 2) K) ≠ 0 := by
  refine ⟨D - 2, ?_, ?_⟩
  · omega
  · have ha : a ≠ 0 := by
      intro ha
      apply hHne
      rw [normalForm, ha]
      simp
    have hL : gradientRatioLinearForm c ≠ 0 :=
      gradientRatioLinearForm_ne_zero_of_linearPower_ne_zero
        H D (by omega) hHne a c normalForm
    have hn2 : ((((D - 2) + 2 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (by omega : (D - 2) + 2 ≠ 0)
    have hn1 : ((((D - 2) + 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (by omega : (D - 2) + 1 ≠ 0)
    exact mul_ne_zero
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hn2) hn1))
      (pow_ne_zero (D - 2) hL)

/-- **Forced compensator has exact transverse order two.** -/
theorem binaryForcedCompensator_hasExactTransverseOrder_two
    (H G Klower : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hD : 2 ≤ D)
    (hHne : H ≠ 0)
    (a : K)
    (c : Fin 2 → K)
    (normalForm :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (G_transverse_sq_zero :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
    (G_det_ne_zero :
      binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0)
    (compensation :
      binaryHessianDetCross H Klower =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G) :
    HasExactBinaryLinearFormTransverseOrder c 2 Klower := by
  have hL : gradientRatioLinearForm c ≠ 0 :=
    gradientRatioLinearForm_ne_zero_of_linearPower_ne_zero
      H D (by omega) hHne a c normalForm
  rcases linearPowerTopHessianFactor_ne_zero
      H D hD hHne a c normalForm with ⟨n, hDn, hfactor_ne⟩
  have hfac := binaryHessianDetCross_linearPower_factor a c n Klower
  have hnormal :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2) := by
    have h := normalForm
    rw [hDn] at h
    exact h
  rw [← hnormal] at hfac
  have hsq_ne :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c Klower) ≠ 0 := by
    intro hzero
    have hcross0 : binaryHessianDetCross H Klower = 0 := by
      rw [hfac, hzero]
      simp
    rw [hcross0] at compensation
    apply G_det_ne_zero
    exact neg_eq_zero.mp compensation.symm
  have hdet_locked :
      binaryLinearFormTransverseDeriv c
        (binaryDirectionalHessianDet (0 : Fin 2) 1 G) = 0 :=
    binaryLinearFormTransverseDeriv_hessianDet_eq_zero_of_sq_zero
      c G hL G_transverse_sq_zero
  let A : MvPolynomial (Fin 2) K :=
    MvPolynomial.C
        (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
      (gradientRatioLinearForm c) ^ n
  have hA : A ≠ 0 := by
    simpa [A] using hfactor_ne
  have hA_locked : binaryLinearFormTransverseDeriv c A = 0 := by
    dsimp only [A]
    exact binaryLinearFormTransverseDeriv_C_mul_gradientRatioLinearForm_pow
      c (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) n
  have hcomp' :
      A * binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c Klower) =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G := by
    rw [← hfac]
    exact compensation
  have hd := congrArg (binaryLinearFormTransverseDeriv c) hcomp'
  rw [binaryLinearFormTransverseDeriv_mul, hA_locked,
    binaryLinearFormTransverseDeriv_neg, hdet_locked] at hd
  simp only [zero_mul, zero_add, mul_zero, add_zero, neg_zero] at hd
  have hcube :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c Klower)) = 0 := by
    exact (mul_eq_zero.mp hd).resolve_left hA
  refine ⟨?_, ?_⟩
  · simpa [HasExactBinaryLinearFormTransverseOrder,
      iteratedBinaryLinearFormTransverseDeriv] using hsq_ne
  · simpa [HasExactBinaryLinearFormTransverseOrder,
      iteratedBinaryLinearFormTransverseDeriv] using hcube

/-! ## Assembly-facing order frontier -/

/-- Forced-compensator frontier with the curved branch upgraded by the exact
transverse orders of both the first curved layer and its compensator. -/
inductive BinarySingularHessianTransverseOrderFrontier
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
  | nonlinearNextAffine
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
      (E_le_one : E ≤ 1)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero :
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) = 0)
  | nonlinearNextLocked
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
      (E_ge_two : 2 ≤ E)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero :
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) = 0)
      (transverse_first_zero : binaryLinearFormTransverseDeriv c G = 0)
  | nonlinearNextCurvedOrderTwo
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
      (E_ge_two : 2 ≤ E)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (G_order_one : HasExactBinaryLinearFormTransverseOrder c 1 G)
      (next_det_ne_zero :
        binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0)
      (F : ℕ)
      (Klower : MvPolynomial (Fin 2) K)
      (F_eq : F = 2 * E - D)
      (F_ge_two : 2 ≤ F)
      (F_lt_E : F < E)
      (Klower_eq : Klower = binaryOrdinaryDegreeComponent R F)
      (Klower_ne_zero : Klower ≠ 0)
      (Klower_homogeneous : Klower.IsHomogeneous F)
      (compensation :
        binaryHessianDetCross H Klower =
          - binaryDirectionalHessianDet (0 : Fin 2) 1 G)
      (Klower_order_two : HasExactBinaryLinearFormTransverseOrder c 2 Klower)

/-- Every stationary binary singular-Hessian face reaches the exact
transverse-order frontier. -/
theorem binarySingularHessian_transverseOrderFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianTransverseOrderFrontier Q) := by
  rcases binarySingularHessian_forcedCompensatorFrontier Q hQ hdet with ⟨F0⟩
  cases F0 with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
        a c normalForm Q_eq_H⟩
  | nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero =>
      exact ⟨.nonlinearNextAffine D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero
        remainder_maximal G_homogeneous transverse_sq_zero⟩
  | nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero transverse_first_zero =>
      exact ⟨.nonlinearNextLocked D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
        remainder_maximal G_homogeneous transverse_sq_zero transverse_first_zero⟩
  | nonlinearNextCurvedCompensated D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero transverse_first_ne_zero
      next_det_ne_zero F Klower F_eq F_ge_two F_lt_E Klower_eq Klower_ne_zero
      compensation =>
      have hGorder : HasExactBinaryLinearFormTransverseOrder c 1 G := by
        constructor
        · simpa [HasExactBinaryLinearFormTransverseOrder,
            iteratedBinaryLinearFormTransverseDeriv] using
            transverse_first_ne_zero
        · simpa [HasExactBinaryLinearFormTransverseOrder,
            iteratedBinaryLinearFormTransverseDeriv] using
            transverse_sq_zero
      have hKorder : HasExactBinaryLinearFormTransverseOrder c 2 Klower :=
        binaryForcedCompensator_hasExactTransverseOrder_two
          H G Klower D hD H_ne_zero a c normalForm transverse_sq_zero
          next_det_ne_zero compensation
      have hKhom : Klower.IsHomogeneous F := by
        rw [Klower_eq]
        exact binaryOrdinaryDegreeComponent_isHomogeneous R F
      exact ⟨.nonlinearNextCurvedOrderTwo D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
        remainder_maximal G_homogeneous hGorder next_det_ne_zero
        F Klower F_eq F_ge_two F_lt_E Klower_eq Klower_ne_zero hKhom
        compensation hKorder⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing exact transverse-order frontier for the actual stationary
HC4 binary face. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.transverseOrderFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianTransverseOrderFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_transverseOrderFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
