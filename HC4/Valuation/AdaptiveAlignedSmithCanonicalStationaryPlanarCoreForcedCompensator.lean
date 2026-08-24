import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreNextLayerCurvature
import Mathlib.Tactic

/-!
# Forced lower compensator for a curved stationary binary layer

Assume the stationary binary core has maximal homogeneous layer `H` of degree
`D`, next maximal remainder layer `G` of degree `E < D`, and that the
second-order direction lock is curved:

    D_perp^2 G = 0,
    D_perp G != 0.

The curvature stage proves

    det Hess G != 0.

Since the full binary core has zero Hessian determinant, the homogeneous
curvature `det Hess G`, which lies in degree `2E - 4`, must be cancelled by
an exact lower cross term with `H`.  The only possible degree of that lower
layer is

    F = 2E - D.

This file proves that statement without assuming that the remainder has no
intermediate homogeneous layers.  The key algebraic ingredient is an exact
component-shift theorem:

    in_{a+b}(P Q) = P * in_b(Q)

whenever `P` is exactly weighted homogeneous of degree `a`.  Unlike the
maximal-component product lemma used earlier, the right factor is completely
unbounded.  This lets us extract the degree `2E-4` cross term even when the
remainder contains layers strictly between `E` and `F`.

The resulting compensator is nonzero and necessarily nonlinear:

    2 <= F < E,
    in_F(R) != 0,
    B(H, in_F(R)) = - det Hess G.

Thus every genuinely curved next layer forces a strictly lower nonlinear
layer.  This is the exact finite-descent datum needed by the closing stage.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Exact product extraction with an unbounded right factor -/

/-- Multiplication by an exactly weighted-homogeneous left factor shifts
*every* exact component of the right factor.  No upper weight bound on the
right factor is required. -/
theorem initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous_exact
    {σ : Type*} [DecidableEq σ]
    {w : σ → ℤ} {a b : ℤ}
    {P Q : MvPolynomial σ K}
    (hP : MvPolynomial.IsWeightedHomogeneous w P a) :
    initialForm w (a + b) (P * Q) =
      P * initialForm w b Q := by
  classical
  rw [P.as_sum]
  simp only [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdw : Finsupp.weight w d = a := by
    exact hP (MvPolynomial.mem_support_iff.mp hd)
  ext e
  rw [coeff_initialForm]
  simp only [MvPolynomial.coeff_monomial_mul']
  by_cases hde : d ≤ e
  · simp only [if_pos hde]
    rw [coeff_initialForm]
    have hsubadd : e - d + d = e := tsub_add_cancel_of_le hde
    have hw :
        Finsupp.weight w e =
          a + Finsupp.weight w (e - d) := by
      calc
        Finsupp.weight w e =
            Finsupp.weight w ((e - d) + d) := by rw [hsubadd]
        _ = Finsupp.weight w (e - d) + Finsupp.weight w d := by
              simp
        _ = Finsupp.weight w (e - d) + a := by rw [hdw]
        _ = a + Finsupp.weight w (e - d) := by ac_rfl
    rw [hw]
    by_cases hb : Finsupp.weight w (e - d) = b
    · simp [hb]
    · have hne :
          a + Finsupp.weight w (e - d) ≠ a + b := by
        intro h
        exact hb (add_left_cancel h)
      simp [hb, hne]
  · simp [hde]

/-! ## Exact cross extraction at an arbitrary integer degree -/

/-- Hessian entries commute with extraction of an arbitrary ordinary integer
component.  This is the integer-degree form needed below, where the candidate
compensator degree is initially `2E-D : ℤ` and is not yet known nonnegative. -/
theorem initialForm_binaryHessianEntry_eq_integerComponentHessian
    (R : MvPolynomial (Fin 2) K)
    (m : ℤ)
    (i j : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight (m - 2)
        (HC4.Polynomial.hessian R i j) =
      HC4.Polynomial.hessian
        (initialForm binaryOrdinaryIntegerWeight m R) i j := by
  have h := HC4.Polynomial.hessian_initialForm_entry
    binaryOrdinaryIntegerWeight m R i j
  have hshift :
      m - binaryOrdinaryIntegerWeight i - binaryOrdinaryIntegerWeight j =
        m - 2 := by
    change m - 1 - 1 = m - 2
    ring
  rw [hshift] at h
  exact h.symm

/-- Pure second derivatives commute with arbitrary integer ordinary
component extraction. -/
theorem initialForm_directionalSecondDerivative_eq_integerComponent
    (R : MvPolynomial (Fin 2) K)
    (m : ℤ)
    (i : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight (m - 2)
        (directionalSecondDerivative i R) =
      directionalSecondDerivative i
        (initialForm binaryOrdinaryIntegerWeight m R) := by
  simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
    (initialForm_binaryHessianEntry_eq_integerComponentHessian R m i i)

/-- Mixed second derivatives commute with arbitrary integer ordinary
component extraction. -/
theorem initialForm_directionalMixedDerivative_eq_integerComponent
    (R : MvPolynomial (Fin 2) K)
    (m : ℤ)
    (i j : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight (m - 2)
        (directionalMixedDerivative i j R) =
      directionalMixedDerivative i j
        (initialForm binaryOrdinaryIntegerWeight m R) := by
  simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
    (initialForm_binaryHessianEntry_eq_integerComponentHessian R m j i)

/-- **Exact arbitrary cross-layer extraction.**

If `H` is homogeneous of ordinary degree `D`, then the exact component of
`B(H,R)` at degree `(D-2)+(m-2)` depends only on the exact degree-`m`
component of `R`.  In contrast with the earlier maximal-layer extraction,
`R` may contain terms of arbitrarily larger degree. -/
theorem initialForm_binaryHessianDetCross_eq_integerComponent
    (H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (m : ℤ)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D) :
    initialForm binaryOrdinaryIntegerWeight
        (((D : ℤ) - 2) + (m - 2))
        (binaryHessianDetCross H R) =
      binaryHessianDetCross H
        (initialForm binaryOrdinaryIntegerWeight m R) := by
  let w := binaryOrdinaryIntegerWeight
  let Hd00 := directionalSecondDerivative (0 : Fin 2) H
  let Hd11 := directionalSecondDerivative (1 : Fin 2) H
  let Hd01 := directionalMixedDerivative (0 : Fin 2) 1 H
  let Rd00 := directionalSecondDerivative (0 : Fin 2) R
  let Rd11 := directionalSecondDerivative (1 : Fin 2) R
  let Rd01 := directionalMixedDerivative (0 : Fin 2) 1 R
  let J := initialForm binaryOrdinaryIntegerWeight m R
  have hH00 : MvPolynomial.IsWeightedHomogeneous w Hd00 ((D : ℤ) - 2) := by
    dsimp [w, Hd00]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (0 : Fin 2) 0)
  have hH11 : MvPolynomial.IsWeightedHomogeneous w Hd11 ((D : ℤ) - 2) := by
    dsimp [w, Hd11]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (1 : Fin 2) 1)
  have hH01 : MvPolynomial.IsWeightedHomogeneous w Hd01 ((D : ℤ) - 2) := by
    dsimp [w, Hd01]
    simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (1 : Fin 2) 0)
  have htop00_11 :
      initialForm w (((D : ℤ) - 2) + (m - 2)) (Hd00 * Rd11) =
        Hd00 * directionalSecondDerivative (1 : Fin 2) J := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous_exact hH00]
    dsimp [w, Rd11, J]
    rw [initialForm_directionalSecondDerivative_eq_integerComponent
      R m (1 : Fin 2)]
  have htop11_00 :
      initialForm w (((D : ℤ) - 2) + (m - 2)) (Rd00 * Hd11) =
        directionalSecondDerivative (0 : Fin 2) J * Hd11 := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous_exact hH11]
    dsimp [w, Rd00, J]
    rw [initialForm_directionalSecondDerivative_eq_integerComponent
      R m (0 : Fin 2)]
    ring
  have htop01_a :
      initialForm w (((D : ℤ) - 2) + (m - 2)) (Hd01 * Rd01) =
        Hd01 * directionalMixedDerivative (0 : Fin 2) 1 J := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous_exact hH01]
    dsimp [w, Rd01, J]
    rw [initialForm_directionalMixedDerivative_eq_integerComponent
      R m (0 : Fin 2) 1]
  have htop01_b :
      initialForm w (((D : ℤ) - 2) + (m - 2)) (Rd01 * Hd01) =
        directionalMixedDerivative (0 : Fin 2) 1 J * Hd01 := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous_exact hH01]
    dsimp [w, Rd01, J]
    rw [initialForm_directionalMixedDerivative_eq_integerComponent
      R m (0 : Fin 2) 1]
    ring
  unfold binaryHessianDetCross
  change initialForm w (((D : ℤ) - 2) + (m - 2))
      (Hd00 * Rd11 + Rd00 * Hd11 - Hd01 * Rd01 - Rd01 * Hd01) = _
  simp only [map_sub, initialForm_add]
  rw [htop00_11, htop11_00, htop01_a, htop01_b]

/-! ## Top determinant component of the remainder -/

/-- For a remainder of ordinary degree at most `E`, its exact Hessian-
determinant component in degree `2E-4` is the Hessian determinant of its
ordinary degree-`E` component. -/
theorem initialForm_binaryDirectionalHessianDet_eq_topComponent
    (R : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hR : IsWeightLE binaryOrdinaryIntegerWeight E R) :
    initialForm binaryOrdinaryIntegerWeight
        (((E : ℤ) - 2) + ((E : ℤ) - 2))
        (binaryDirectionalHessianDet (0 : Fin 2) 1 R) =
      binaryDirectionalHessianDet (0 : Fin 2) 1
        (binaryOrdinaryDegreeComponent R E) := by
  have h :=
    HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      binaryOrdinaryIntegerWeight (E : ℤ) R hR
  have hlevel :
      (Fintype.card (Fin 2) : ℤ) * (E : ℤ) -
          2 * ∑ i : Fin 2, binaryOrdinaryIntegerWeight i =
        ((E : ℤ) - 2) + ((E : ℤ) - 2) := by
    simp [binaryOrdinaryIntegerWeight] <;> ring
  rw [hlevel] at h
  simpa [binaryOrdinaryDegreeComponent,
    hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet] using h

/-! ## Negative ordinary components and affine components -/

/-- Ordinary binary weights are nonnegative, hence every negative integer
initial form vanishes. -/
theorem binaryOrdinaryInitialForm_eq_zero_of_neg
    (R : MvPolynomial (Fin 2) K)
    (m : ℤ)
    (hm : m < 0) :
    initialForm binaryOrdinaryIntegerWeight m R = 0 := by
  ext d
  rw [coeff_initialForm]
  simp only [MvPolynomial.coeff_zero]
  split
  · rename_i hweight
    have hdeg := binaryOrdinaryIntegerWeight_eq_degree d
    rw [hweight] at hdeg
    have hnonneg : (0 : ℤ) ≤ (d.degree : ℤ) := by positivity
    exfalso
    omega
  · rfl

/-- A degree-zero or degree-one ordinary component has zero pure second
derivative. -/
theorem directionalSecondDerivative_binaryOrdinaryDegreeComponent_eq_zero_of_le_one
    (R : MvPolynomial (Fin 2) K)
    (F : ℕ)
    (hF : F ≤ 1)
    (i : Fin 2) :
    directionalSecondDerivative i (binaryOrdinaryDegreeComponent R F) = 0 := by
  rw [← initialForm_directionalSecondDerivative_eq_component R F i]
  apply binaryOrdinaryInitialForm_eq_zero_of_neg
  omega

/-- A degree-zero or degree-one ordinary component has zero mixed second
derivative. -/
theorem directionalMixedDerivative_binaryOrdinaryDegreeComponent_eq_zero_of_le_one
    (R : MvPolynomial (Fin 2) K)
    (F : ℕ)
    (hF : F ≤ 1)
    (i j : Fin 2) :
    directionalMixedDerivative i j (binaryOrdinaryDegreeComponent R F) = 0 := by
  rw [← initialForm_directionalMixedDerivative_eq_component R F i j]
  apply binaryOrdinaryInitialForm_eq_zero_of_neg
  omega

/-- Consequently an affine ordinary component has zero Hessian polarisation
with every other polynomial. -/
theorem binaryHessianDetCross_degreeComponent_eq_zero_of_le_one
    (H R : MvPolynomial (Fin 2) K)
    (F : ℕ)
    (hF : F ≤ 1) :
    binaryHessianDetCross H (binaryOrdinaryDegreeComponent R F) = 0 := by
  have h00 :=
    directionalSecondDerivative_binaryOrdinaryDegreeComponent_eq_zero_of_le_one
      R F hF (0 : Fin 2)
  have h11 :=
    directionalSecondDerivative_binaryOrdinaryDegreeComponent_eq_zero_of_le_one
      R F hF (1 : Fin 2)
  have h01 :=
    directionalMixedDerivative_binaryOrdinaryDegreeComponent_eq_zero_of_le_one
      R F hF (0 : Fin 2) 1
  unfold binaryHessianDetCross
  rw [h00, h11, h01]
  ring

/-! ## The forced compensator theorem -/

/-- **Curved-layer compensation theorem.**

Let `Q = H + R`, with `H` homogeneous of degree `D`, `R` of degree at most
`E < D`, and `G = in_E(R)`.  Assume both the full Hessian determinant of `Q`
and the determinant of `H` vanish, while `det Hess G` is nonzero.  Then the
integer degree `2E-D` is forced to be nonnegative and in fact at least `2`.
Writing

    F = 2E - D,

one has

    2 <= F < E,
    in_F(R) != 0,
    B(H, in_F(R)) = - det Hess G.

No hypothesis excludes intermediate remainder layers. -/
theorem binaryCurvedNextLayer_forcesCompensator
    (Q H R G : MvPolynomial (Fin 2) K)
    (D E : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hR : IsWeightLE binaryOrdinaryIntegerWeight E R)
    (hED : E < D)
    (hG : G = binaryOrdinaryDegreeComponent R E)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0)
    (hGdet : binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0) :
    let F : ℕ := 2 * E - D
    2 ≤ F ∧ F < E ∧
      binaryOrdinaryDegreeComponent R F ≠ 0 ∧
      binaryHessianDetCross H (binaryOrdinaryDegreeComponent R F) =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G := by
  change 2 ≤ 2 * E - D ∧ 2 * E - D < E ∧
    binaryOrdinaryDegreeComponent R (2 * E - D) ≠ 0 ∧
    binaryHessianDetCross H (binaryOrdinaryDegreeComponent R (2 * E - D)) =
      - binaryDirectionalHessianDet (0 : Fin 2) 1 G
  let m : ℤ := 2 * (E : ℤ) - (D : ℤ)
  let level : ℤ := ((E : ℤ) - 2) + ((E : ℤ) - 2)
  have hQsum :
      binaryHessianDetCross H R +
          binaryDirectionalHessianDet (0 : Fin 2) 1 R = 0 := by
    have hexpand := binaryDirectionalHessianDet_add_cross H R
    have hsum :
        binaryHessianDetCross H R +
            binaryDirectionalHessianDet (0 : Fin 2) 1 R =
          binaryDirectionalHessianDet (0 : Fin 2) 1 (H + R) -
            binaryDirectionalHessianDet (0 : Fin 2) 1 H := by
      rw [hexpand]
      ring
    rw [hsum, ← hdecomp, hQdet, hHdet]
    ring
  have hcomponent := congrArg
    (fun P : MvPolynomial (Fin 2) K =>
      initialForm binaryOrdinaryIntegerWeight level P) hQsum
  have hlevelCross :
      (((D : ℤ) - 2) + (m - 2)) = level := by
    dsimp [m, level]
    ring
  have hcross := initialForm_binaryHessianDetCross_eq_integerComponent
    H R D m hH
  rw [hlevelCross] at hcross
  have hdetTop := initialForm_binaryDirectionalHessianDet_eq_topComponent
    R E hR
  dsimp [level] at hcomponent hcross hdetTop
  rw [initialForm_add, hcross, hdetTop, initialForm_zero] at hcomponent
  rw [← hG] at hcomponent
  have hcrossEq :
      binaryHessianDetCross H
          (initialForm binaryOrdinaryIntegerWeight m R) =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G := by
    linear_combination hcomponent
  have hmne :
      initialForm binaryOrdinaryIntegerWeight m R ≠ 0 := by
    intro hz
    have hcross0 :
        binaryHessianDetCross H
          (initialForm binaryOrdinaryIntegerWeight m R) = 0 := by
      rw [hz]
      simp [binaryHessianDetCross, directionalSecondDerivative,
        directionalMixedDerivative]
    rw [hcross0] at hcrossEq
    apply hGdet
    exact neg_eq_zero.mp hcrossEq.symm
  have hmnonneg : 0 ≤ m := by
    by_contra h
    have hmneg : m < 0 := by omega
    exact hmne (binaryOrdinaryInitialForm_eq_zero_of_neg R m hmneg)
  have hDEint : (D : ℤ) ≤ 2 * (E : ℤ) := by
    dsimp [m] at hmnonneg
    omega
  have hDE : D ≤ 2 * E := by
    exact_mod_cast hDEint
  let F : ℕ := 2 * E - D
  have hFcast : (F : ℤ) = m := by
    dsimp [F, m]
    omega
  have hcomponentEq :
      initialForm binaryOrdinaryIntegerWeight m R =
        binaryOrdinaryDegreeComponent R F := by
    unfold binaryOrdinaryDegreeComponent
    rw [hFcast]
  rw [hcomponentEq] at hmne hcrossEq
  have hFlt : F < E := by
    dsimp [F]
    omega
  have hcrossNe :
      binaryHessianDetCross H (binaryOrdinaryDegreeComponent R F) ≠ 0 := by
    intro hz
    rw [hz] at hcrossEq
    apply hGdet
    exact neg_eq_zero.mp hcrossEq.symm
  have hFtwo : 2 ≤ F := by
    by_contra h
    have hFle : F ≤ 1 := by omega
    exact hcrossNe
      (binaryHessianDetCross_degreeComponent_eq_zero_of_le_one H R F hFle)
  simpa [F] using
    (show 2 ≤ F ∧ F < E ∧
        binaryOrdinaryDegreeComponent R F ≠ 0 ∧
        binaryHessianDetCross H (binaryOrdinaryDegreeComponent R F) =
          - binaryDirectionalHessianDet (0 : Fin 2) 1 G from
      ⟨hFtwo, hFlt, hmne, hcrossEq⟩)

/-! ## Assembly-facing forced-compensator frontier -/

/-- The curvature frontier with the genuinely curved branch strengthened by
its exact forced lower compensator. -/
inductive BinarySingularHessianForcedCompensatorFrontier
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
  | nonlinearNextCurvedCompensated
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
      (transverse_first_ne_zero : binaryLinearFormTransverseDeriv c G ≠ 0)
      (next_det_ne_zero :
        binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0)
      (F : ℕ)
      (Klower : MvPolynomial (Fin 2) K)
      (F_eq : F = 2 * E - D)
      (F_ge_two : 2 ≤ F)
      (F_lt_E : F < E)
      (Klower_eq : Klower = binaryOrdinaryDegreeComponent R F)
      (Klower_ne_zero : Klower ≠ 0)
      (compensation :
        binaryHessianDetCross H Klower =
          - binaryDirectionalHessianDet (0 : Fin 2) 1 G)

/-- Every nonzero stationary binary singular-Hessian polynomial reaches the
forced-compensator frontier. -/
theorem binarySingularHessian_forcedCompensatorFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianForcedCompensatorFrontier Q) := by
  rcases binarySingularHessian_nextLayerCurvatureFrontier Q hQ hdet with ⟨F0⟩
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
  | nonlinearNextCurved D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero transverse_first_ne_zero
      next_det_ne_zero =>
      have hHhom : MvPolynomial.IsWeightedHomogeneous
          binaryOrdinaryIntegerWeight H D := by
        rw [H_eq]
        simpa [binaryOrdinaryDegreeComponent] using
          (initialForm_isWeightedHomogeneous
            binaryOrdinaryIntegerWeight D Q)
      have hRLE : IsWeightLE binaryOrdinaryIntegerWeight E R :=
        isWeightLE_binaryOrdinary_of_degree_le R E remainder_maximal
      have hdecomp : Q = H + R := by
        rw [R_eq]
        ring
      have hHdet :
          binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0 := by
        rw [H_eq]
        exact binaryOrdinaryDegreeComponent_det_zero_of_maximal
          Q D maximal hdet
      have hcomp := binaryCurvedNextLayer_forcesCompensator
        Q H R G D E hdecomp hHhom hRLE E_lt_D G_eq hdet hHdet
          next_det_ne_zero
      change 2 ≤ 2 * E - D ∧ 2 * E - D < E ∧
        binaryOrdinaryDegreeComponent R (2 * E - D) ≠ 0 ∧
        binaryHessianDetCross H (binaryOrdinaryDegreeComponent R (2 * E - D)) =
          - binaryDirectionalHessianDet (0 : Fin 2) 1 G at hcomp
      let F : ℕ := 2 * E - D
      let Klower : MvPolynomial (Fin 2) K := binaryOrdinaryDegreeComponent R F
      have hFtwo : 2 ≤ F := by simpa [F] using hcomp.1
      have hFlt : F < E := by simpa [F] using hcomp.2.1
      have hKne : Klower ≠ 0 := by
        dsimp [Klower]
        simpa [F] using hcomp.2.2.1
      have hcancel :
          binaryHessianDetCross H Klower =
            - binaryDirectionalHessianDet (0 : Fin 2) 1 G := by
        dsimp [Klower]
        simpa [F] using hcomp.2.2.2
      exact ⟨.nonlinearNextCurvedCompensated D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
        remainder_maximal G_homogeneous transverse_sq_zero
        transverse_first_ne_zero next_det_ne_zero F Klower rfl hFtwo hFlt rfl
        hKne hcancel⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing forced-compensator frontier for the actual stationary HC4
binary face. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.forcedCompensatorFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianForcedCompensatorFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_forcedCompensatorFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
