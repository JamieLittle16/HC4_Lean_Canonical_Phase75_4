import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreNextLayerCurvature
import HC4.Polynomial.MonomialHessian
import HC4.Polynomial.DerivativeBounds
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# Elimination of the curved stationary binary branch

The preceding module isolates a single genuinely curved alternative after
peeling the maximal homogeneous layer of a binary singular-Hessian core.
This file eliminates that alternative by a finite Newton first-contact
argument.  After a determinant-one shear straightens the top linear form,
any support leaving the top axis has a minimal rational contact slope.  The
corresponding exposed face is again singular-Hessian.  Its maximal transverse
endpoint is forced onto the opposite axis; a second endpoint then gives a
uniquely exposed nonzero cross-Hessian term.  The only remaining endpoint of
transverse degree one is excluded by the retained zero linear jet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Binary contact arithmetic -/

theorem finTwo_degree_eq_add_curved (d : Fin 2 →₀ ℕ) :
    d.degree = d 0 + d 1 := by
  have h := congrFun Finsupp.degree_eq_weight_one d
  rw [Finsupp.weight_apply, Finsupp.sum_fintype] at h
  · simpa using h
  · intro i
    simp

theorem finTwo_exponent_eq_of_degree_eq_of_coord_eq_curved
    (j : Fin 2) (d e : Fin 2 →₀ ℕ)
    (hdeg : d.degree = e.degree) (hj : d j = e j) : d = e := by
  have hsum : d 0 + d 1 = e 0 + e 1 := by
    rw [← finTwo_degree_eq_add_curved d, ← finTwo_degree_eq_add_curved e]
    exact hdeg
  apply Finsupp.ext
  intro i
  fin_cases j
  · have hj0 : d (0 : Fin 2) = e 0 := by simpa using hj
    fin_cases i
    · exact hj0
    · rw [hj0] at hsum
      exact Nat.add_left_cancel hsum
  · have hj1 : d (1 : Fin 2) = e 1 := by simpa using hj
    fin_cases i
    · rw [hj1] at hsum
      exact Nat.add_right_cancel hsum
    · exact hj1

theorem finTwo_degree_eq_coord_of_other_zero_curved
    (i j : Fin 2) (hij : i ≠ j) (d : Fin 2 →₀ ℕ)
    (hi : d i = 0) : d.degree = d j := by
  rw [finTwo_degree_eq_add_curved]
  fin_cases i <;> fin_cases j <;> simp_all

theorem finTwo_coord_le_degree_curved (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    d j ≤ d.degree := by
  rw [finTwo_degree_eq_add_curved]
  fin_cases j <;> simp

theorem finTwo_degree_eq_coord_add_other_curved
    (i j : Fin 2) (hij : i ≠ j) (d : Fin 2 →₀ ℕ) :
    d.degree = d i + d j := by
  rw [finTwo_degree_eq_add_curved]
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · rfl
  · fin_cases j
    · exact Nat.add_comm _ _
    · exact (hij rfl).elim

def binarySingleCoordinateWeight (j : Fin 2) : Fin 2 → ℤ :=
  fun i => if i = j then 1 else 0

theorem weight_binarySingleCoordinateWeight
    (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (binarySingleCoordinateWeight j) d = (d j : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · fin_cases j <;> simp [binarySingleCoordinateWeight]
  · intro i
    simp

def binaryFirstContactWeight
    (j : Fin 2) (scale bump : ℕ) : Fin 2 → ℤ :=
  fun i => (scale : ℤ) + if i = j then (bump : ℤ) else 0

def binaryFirstContactExponentWeight
    (j : Fin 2) (scale bump : ℕ) (d : Fin 2 →₀ ℕ) : ℤ :=
  (scale : ℤ) * (d.degree : ℤ) + (bump : ℤ) * (d j : ℤ)

theorem weight_binaryFirstContactWeight
    (j : Fin 2) (scale bump : ℕ) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (binaryFirstContactWeight j scale bump) d =
      binaryFirstContactExponentWeight j scale bump d := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · fin_cases j
    · simp [binaryFirstContactWeight, binaryFirstContactExponentWeight,
        finTwo_degree_eq_add_curved]
      ring
    · simp [binaryFirstContactWeight, binaryFirstContactExponentWeight,
        finTwo_degree_eq_add_curved]
      ring
  · intro i
    simp

/-- Coefficient extraction from an exact ordinary homogeneous component. -/
theorem coeff_binaryOrdinaryDegreeComponent_of_degree_curved
    (Q : MvPolynomial (Fin 2) K) (d : Fin 2 →₀ ℕ) (D : ℕ)
    (hdeg : d.degree = D) :
    MvPolynomial.coeff d (binaryOrdinaryDegreeComponent Q D) =
      MvPolynomial.coeff d Q := by
  unfold binaryOrdinaryDegreeComponent
  rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree, hdeg]
  simp

def binaryOutsideSupport
    (j : Fin 2) (Q : MvPolynomial (Fin 2) K) : Finset (Fin 2 →₀ ℕ) :=
  Q.support.filter fun d => 0 < d j

@[simp] theorem mem_binaryOutsideSupport
    {j : Fin 2} {Q : MvPolynomial (Fin 2) K} {d : Fin 2 →₀ ℕ} :
    d ∈ binaryOutsideSupport j Q ↔ d ∈ Q.support ∧ 0 < d j := by
  simp [binaryOutsideSupport]

def binaryContactSlope
    (D : ℕ) (j : Fin 2) (d : Fin 2 →₀ ℕ) : ℚ :=
  ((D - d.degree : ℕ) : ℚ) / (d j : ℚ)

theorem exists_minimal_binaryContactExponent
    {D : ℕ} {j : Fin 2} {Q : MvPolynomial (Fin 2) K}
    (hne : (binaryOutsideSupport j Q).Nonempty) :
    ∃ d₀ ∈ binaryOutsideSupport j Q,
      ∀ d ∈ binaryOutsideSupport j Q,
        binaryContactSlope D j d₀ ≤ binaryContactSlope D j d := by
  exact Finset.exists_min_image _ _ hne

theorem binaryContactSlope_le_iff_cross
    {D : ℕ} {j : Fin 2} {d₀ d : Fin 2 →₀ ℕ}
    (hd₀ : 0 < d₀ j) (hd : 0 < d j) :
    binaryContactSlope D j d₀ ≤ binaryContactSlope D j d ↔
      (D - d₀.degree) * d j ≤ (D - d.degree) * d₀ j := by
  have hd₀Q : (0 : ℚ) < (d₀ j : ℚ) := by exact_mod_cast hd₀
  have hdQ : (0 : ℚ) < (d j : ℚ) := by exact_mod_cast hd
  rw [binaryContactSlope, binaryContactSlope]
  rw [div_le_div_iff₀ hd₀Q hdQ]
  norm_cast

theorem selected_binaryContact_degree_lt
    {D : ℕ} {j : Fin 2} {Q : MvPolynomial (Fin 2) K}
    {d₀ : Fin 2 →₀ ℕ}
    (hd₀ : d₀ ∈ binaryOutsideSupport j Q)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    (htop : ∀ d ∈ Q.support, d.degree = D → d j = 0) :
    d₀.degree < D := by
  have hs := (mem_binaryOutsideSupport.mp hd₀).1
  have hj := (mem_binaryOutsideSupport.mp hd₀).2
  have hle := hmax d₀ hs
  apply lt_of_le_of_ne hle
  intro heq
  have hz := htop d₀ hs heq
  omega

theorem selected_binaryContact_level
    {D : ℕ} {j : Fin 2} {Q : MvPolynomial (Fin 2) K}
    {d₀ : Fin 2 →₀ ℕ}
    (hd₀ : d₀ ∈ binaryOutsideSupport j Q)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    (htop : ∀ d ∈ Q.support, d.degree = D → d j = 0) :
    let scale := d₀ j
    let bump := D - d₀.degree
    0 < scale ∧ 0 < bump ∧
      binaryFirstContactExponentWeight j scale bump d₀ =
        (scale * D : ℕ) := by
  intro scale bump
  have hs : 0 < d₀ j := (mem_binaryOutsideSupport.mp hd₀).2
  have hlt := selected_binaryContact_degree_lt hd₀ hmax htop
  have hle : d₀.degree ≤ D := Nat.le_of_lt hlt
  refine ⟨hs, Nat.sub_pos_of_lt hlt, ?_⟩
  unfold binaryFirstContactExponentWeight
  simp only [scale, bump]
  rw [Nat.cast_sub hle]
  push_cast
  ring

theorem selected_binaryContact_outside_le
    {D : ℕ} {j : Fin 2} {Q : MvPolynomial (Fin 2) K}
    {d₀ : Fin 2 →₀ ℕ}
    (hd₀ : d₀ ∈ binaryOutsideSupport j Q)
    (hmin : ∀ d ∈ binaryOutsideSupport j Q,
      binaryContactSlope D j d₀ ≤ binaryContactSlope D j d)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ binaryOutsideSupport j Q) :
    let scale := d₀ j
    let bump := D - d₀.degree
    binaryFirstContactExponentWeight j scale bump d ≤
      (scale * D : ℕ) := by
  intro scale bump
  have hd₀j : 0 < d₀ j := (mem_binaryOutsideSupport.mp hd₀).2
  have hdj : 0 < d j := (mem_binaryOutsideSupport.mp hd).2
  have hcross :
      (D - d₀.degree) * d j ≤ (D - d.degree) * d₀ j :=
    (binaryContactSlope_le_iff_cross hd₀j hdj).mp (hmin d hd)
  have hdeg : d.degree ≤ D := hmax d (mem_binaryOutsideSupport.mp hd).1
  have hNat :
      d₀ j * d.degree + (D - d₀.degree) * d j ≤ d₀ j * D := by
    calc
      d₀ j * d.degree + (D - d₀.degree) * d j
          ≤ d₀ j * d.degree + (D - d.degree) * d₀ j :=
            Nat.add_le_add_left hcross _
      _ = d₀ j * (d.degree + (D - d.degree)) := by ring
      _ = d₀ j * D := by rw [Nat.add_comm, Nat.sub_add_cancel hdeg]
  unfold binaryFirstContactExponentWeight
  simp only [scale, bump]
  exact_mod_cast hNat

theorem selected_binaryContact_isWeightLE
    {D : ℕ} {j : Fin 2} {Q : MvPolynomial (Fin 2) K}
    {d₀ : Fin 2 →₀ ℕ}
    (hd₀ : d₀ ∈ binaryOutsideSupport j Q)
    (hmin : ∀ d ∈ binaryOutsideSupport j Q,
      binaryContactSlope D j d₀ ≤ binaryContactSlope D j d)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D) :
    let scale := d₀ j
    let bump := D - d₀.degree
    IsWeightLE (binaryFirstContactWeight j scale bump)
      (scale * D : ℕ) Q := by
  intro scale bump d hd
  rw [weight_binaryFirstContactWeight]
  by_cases hj : d j = 0
  · unfold binaryFirstContactExponentWeight
    rw [hj]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hdeg := hmax d hd
    exact_mod_cast Nat.mul_le_mul_left (d₀ j) hdeg
  · have hdout : d ∈ binaryOutsideSupport j Q :=
      mem_binaryOutsideSupport.mpr ⟨hd, Nat.pos_of_ne_zero hj⟩
    exact selected_binaryContact_outside_le hd₀ hmin hmax hdout

/-! ## Monomial endpoint obstruction -/

def binaryExponentHessianCore
    (d : Fin 2 →₀ ℕ) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => (d i : K) * (d j : K) - if i = j then (d i : K) else 0

theorem det_binaryExponentHessianCore
    (d : Fin 2 →₀ ℕ) :
    (binaryExponentHessianCore (K := K) d).det =
      (d 0 : K) * (d 1 : K) * (1 - (d.degree : K)) := by
  rw [Matrix.det_fin_two]
  have hd := finTwo_degree_eq_add_curved d
  unfold binaryExponentHessianCore
  simp only [↓reduceIte]
  push_cast [hd]
  ring

/-- Evaluation at `(1,1)` of the Hessian of a binary monomial. -/
theorem eval_one_hessian_monomial_finTwo_curved
    (d : Fin 2 →₀ ℕ) (c : K) :
    (MvPolynomial.eval fun _ : Fin 2 => (1 : K)).mapMatrix
        (HC4.Polynomial.hessian (MvPolynomial.monomial d c)) =
      c • binaryExponentHessianCore (K := K) d := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    cases hdi : d i with
    | zero =>
        simp [HC4.Polynomial.hessian_apply, binaryExponentHessianCore,
          MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial, hdi]
    | succ n =>
        simp [HC4.Polynomial.hessian_apply, binaryExponentHessianCore,
          MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial,
          Finsupp.prod, hdi] <;> ring
  · simp [HC4.Polynomial.hessian_apply, binaryExponentHessianCore,
      MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial,
      Finsupp.prod, hij] <;> ring

/-- Evaluation at `(1,1)` of the binary monomial Hessian determinant. -/
theorem eval_one_binaryDirectionalHessianDet_monomial_curved
    (d : Fin 2 →₀ ℕ) (c : K) :
    MvPolynomial.eval (fun _ : Fin 2 => (1 : K))
        (binaryDirectionalHessianDet (0 : Fin 2) 1
          (MvPolynomial.monomial d c)) =
      c ^ 2 * (binaryExponentHessianCore (K := K) d).det := by
  rw [← hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet]
  unfold HC4.Polynomial.hessianDeterminant
  rw [RingHom.map_det]
  rw [eval_one_hessian_monomial_finTwo_curved]
  simpa using Matrix.det_smul (binaryExponentHessianCore (K := K) d) c

/-- For a binary monomial, the Hessian determinant vanishes only on an axis
(or in ordinary degree at most one). -/
theorem binaryDirectionalHessianDet_monomial_ne_zero_of_both_pos
    {d : Fin 2 →₀ ℕ} {c : K}
    (hc : c ≠ 0) (h0 : 0 < d 0) (h1 : 0 < d 1)
    (hdeg : 2 ≤ d.degree) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
      (MvPolynomial.monomial d c) ≠ 0 := by
  intro hz
  have heval := congrArg
    (MvPolynomial.eval fun _ : Fin 2 => (1 : K)) hz
  rw [eval_one_binaryDirectionalHessianDet_monomial_curved,
    det_binaryExponentHessianCore] at heval
  simp only [map_zero] at heval
  have hd0 : (d 0 : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt h0
  have hd1 : (d 1 : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt h1
  have hlast : (1 : K) - (d.degree : K) ≠ 0 := by
    intro hzero
    have heq : (d.degree : K) = 1 := (sub_eq_zero.mp hzero).symm
    have heqNat : d.degree = 1 := by exact_mod_cast heq
    omega
  exact (mul_ne_zero (pow_ne_zero 2 hc)
    (mul_ne_zero (mul_ne_zero hd0 hd1) hlast)) heval

theorem binaryMonomial_zeroHessian_forces_otherExponent_zero
    {i j : Fin 2} (hij : i ≠ j)
    {d : Fin 2 →₀ ℕ} {c : K}
    (hc : c ≠ 0) (hj : 0 < d j) (hdeg : 2 ≤ d.degree)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1
      (MvPolynomial.monomial d c) = 0) :
    d i = 0 := by
  by_contra hi0
  have hi : 0 < d i := Nat.pos_of_ne_zero hi0
  have h0 : 0 < d 0 := by fin_cases i <;> fin_cases j <;> simp_all
  have h1 : 0 < d 1 := by fin_cases i <;> fin_cases j <;> simp_all
  exact (binaryDirectionalHessianDet_monomial_ne_zero_of_both_pos
    hc h0 h1 hdeg) hdet

/-- A monomial with exponent at least two in one coordinate has nonzero pure
second derivative. -/
theorem directionalSecondDerivative_monomial_ne_zero_of_two_le
    (i : Fin 2) {d : Fin 2 →₀ ℕ} {c : K}
    (hc : c ≠ 0) (hi : 2 ≤ d i) :
    directionalSecondDerivative i (MvPolynomial.monomial d c) ≠ 0 := by
  intro hz
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) K => M i i)
    (eval_one_hessian_monomial_finTwo_curved (K := K) d c)
  have hentry' :
      MvPolynomial.eval (fun _ : Fin 2 => (1 : K))
          (HC4.Polynomial.hessian (MvPolynomial.monomial d c) i i) =
        c * ((d i : K) * (d i : K) - (d i : K)) := by
    simpa [RingHom.mapMatrix_apply, binaryExponentHessianCore] using hentry
  have heval := congrArg
    (MvPolynomial.eval fun _ : Fin 2 => (1 : K)) hz
  change MvPolynomial.eval (fun _ : Fin 2 => (1 : K))
      (HC4.Polynomial.hessian (MvPolynomial.monomial d c) i i) = 0 at heval
  rw [hentry'] at heval
  have hdi : (d i : K) ≠ 0 := by
    exact_mod_cast (show d i ≠ 0 by omega)
  have hdim1 : ((d i : K) - 1) ≠ 0 := by
    intro hzero
    have heq : (d i : K) = 1 := sub_eq_zero.mp hzero
    have heqNat : d i = 1 := by exact_mod_cast heq
    omega
  have hcore : (d i : K) * (d i : K) - (d i : K) ≠ 0 := by
    rw [show (d i : K) * (d i : K) - (d i : K) =
      (d i : K) * ((d i : K) - 1) by ring]
    exact mul_ne_zero hdi hdim1
  exact (mul_ne_zero hc hcore) heval

/-- In two variables, the symmetric Hessian cross term can be written in the
coordinate pair `(i,j)` for any distinct coordinates.  Keeping this as a
standalone lemma avoids elaborating the four `Fin 2` cases inside the large
first-contact theorem. -/
theorem binaryHessianDetCross_eq_directional_of_ne
    (i j : Fin 2) (hij : i ≠ j)
    (P R : MvPolynomial (Fin 2) K) :
    binaryHessianDetCross P R =
      directionalSecondDerivative i P * directionalSecondDerivative j R +
        directionalSecondDerivative i R * directionalSecondDerivative j P -
        directionalMixedDerivative i j P * directionalMixedDerivative i j R -
        directionalMixedDerivative i j R * directionalMixedDerivative i j P := by
  fin_cases i <;> fin_cases j <;>
    simp_all [binaryHessianDetCross, directionalSecondDerivative,
      directionalMixedDerivative, pderiv_comm_backport] <;> ring

/-- For the weight concentrated on `j`, the top component of the cross product
between the `i`-pure Hessian entry of a weakly bounded residual and the
`j`-pure Hessian entry of a homogeneous factor is obtained by taking the exact
`M`-component of the residual first.  Keeping the weight shifts in this small
lemma avoids elaborating them inside the large first-contact argument. -/
theorem initialForm_singleCoordinate_cross_secondDerivative
    (i j : Fin 2) (hij : i ≠ j)
    (N M : ℤ)
    (P R : MvPolynomial (Fin 2) K)
    (hP : MvPolynomial.IsWeightedHomogeneous
      (binarySingleCoordinateWeight j) P N)
    (hR : IsWeightLE (binarySingleCoordinateWeight j) M R) :
    initialForm (binarySingleCoordinateWeight j) (N + M - 2)
        (directionalSecondDerivative i R * directionalSecondDerivative j P) =
      directionalSecondDerivative i
          (initialForm (binarySingleCoordinateWeight j) M R) *
        directionalSecondDerivative j P := by
  let w := binarySingleCoordinateWeight j
  have hwi : w i = 0 := by
    simp [w, binarySingleCoordinateWeight, hij]
  have hwj : w j = 1 := by
    simp [w, binarySingleCoordinateWeight]
  have hPjjHom : MvPolynomial.IsWeightedHomogeneous w
      (directionalSecondDerivative j P) (N - 2) := by
    have h := HC4.Polynomial.hessian_entry_isWeightedHomogeneous hP j j
    have hshift : N - w j - w j = N - 2 := by
      rw [hwj]
      ring
    rw [hshift] at h
    simpa [w, directionalSecondDerivative, HC4.Polynomial.hessian_apply] using h
  have hRiiLE : IsWeightLE w M (directionalSecondDerivative i R) := by
    have h := hR.hessian_entry i i
    have hshift : M - w i - w i = M := by
      rw [hwi]
      ring
    rw [hshift] at h
    simpa [w, directionalSecondDerivative, HC4.Polynomial.hessian_apply] using h
  have hRiiComponent :
      initialForm w M (directionalSecondDerivative i R) =
        directionalSecondDerivative i (initialForm w M R) := by
    have h := HC4.Polynomial.hessian_initialForm_entry w M R i i
    have hshift : M - w i - w i = M := by
      rw [hwi]
      ring
    rw [hshift] at h
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using h.symm
  have hpull := initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous
    hPjjHom hRiiLE
  have hlevelEq : (N - 2) + M = N + M - 2 := by ring
  rw [hlevelEq] at hpull
  calc
    initialForm w (N + M - 2)
        (directionalSecondDerivative i R * directionalSecondDerivative j P) =
      initialForm w (N + M - 2)
        (directionalSecondDerivative j P * directionalSecondDerivative i R) := by
          rw [mul_comm]
    _ = directionalSecondDerivative j P *
          initialForm w M (directionalSecondDerivative i R) := hpull
    _ = directionalSecondDerivative j P *
          directionalSecondDerivative i (initialForm w M R) := by
            rw [hRiiComponent]
    _ = directionalSecondDerivative i (initialForm w M R) *
          directionalSecondDerivative j P := by ring

/-! ## Exact first-contact faces -/

theorem binaryDirectionalHessianDet_initialForm_eq_zero
    (w : Fin 2 → ℤ) (m : ℤ)
    (Q : MvPolynomial (Fin 2) K)
    (hQ : IsWeightLE w m Q)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    binaryDirectionalHessianDet (0 : Fin 2) 1 (initialForm w m Q) = 0 := by
  have hfull : HC4.Polynomial.hessianDeterminant Q = 0 := by
    rw [hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet]
    exact hdet
  have hinit :=
    HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
      w m Q hQ hfull
  rw [hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet] at hinit
  exact hinit

theorem binaryDirectionalHessianDet_isWeightLE_singleCoordinate
    (i j : Fin 2) (hij : i ≠ j)
    (M : ℤ) (Q : MvPolynomial (Fin 2) K)
    (hQ : IsWeightLE (binarySingleCoordinateWeight j) M Q) :
    IsWeightLE (binarySingleCoordinateWeight j) (2 * M - 2)
      (binaryDirectionalHessianDet (0 : Fin 2) 1 Q) := by
  have hii : IsWeightLE (binarySingleCoordinateWeight j) M
      (directionalSecondDerivative i Q) := by
    have h := hQ.hessian_entry i i
    have hshift :
        M - binarySingleCoordinateWeight j i - binarySingleCoordinateWeight j i = M := by
      simp [binarySingleCoordinateWeight, hij]
    rw [hshift] at h
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using h
  have hjj : IsWeightLE (binarySingleCoordinateWeight j) (M - 2)
      (directionalSecondDerivative j Q) := by
    have h := hQ.hessian_entry j j
    have hshift :
        M - binarySingleCoordinateWeight j j - binarySingleCoordinateWeight j j = M - 2 := by
      simp [binarySingleCoordinateWeight]
      ring
    rw [hshift] at h
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using h
  have hijb : IsWeightLE (binarySingleCoordinateWeight j) (M - 1)
      (directionalMixedDerivative i j Q) := by
    have h := hQ.hessian_entry j i
    have hshift :
        M - binarySingleCoordinateWeight j j - binarySingleCoordinateWeight j i = M - 1 := by
      simp [binarySingleCoordinateWeight, hij]
    rw [hshift] at h
    simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using h
  have hp := hii.mul hjj
  have hs0 := hijb.mul hijb
  have hs : IsWeightLE (binarySingleCoordinateWeight j) (M + (M - 2))
      (directionalMixedDerivative i j Q * directionalMixedDerivative i j Q) := by
    convert hs0 using 1 <;> ring
  have hsub := hp.sub hs
  have hdetij :
      binaryDirectionalHessianDet i j Q =
        directionalSecondDerivative i Q * directionalSecondDerivative j Q -
          directionalMixedDerivative i j Q * directionalMixedDerivative i j Q := by
    simp [binaryDirectionalHessianDet, pow_two]
  have h01 : binaryDirectionalHessianDet i j Q =
      binaryDirectionalHessianDet (0 : Fin 2) 1 Q := by
    fin_cases i <;> fin_cases j <;>
      simp_all [binaryDirectionalHessianDet, directionalSecondDerivative,
        directionalMixedDerivative, pderiv_comm_backport, pow_two] <;> ring
  rw [← h01, hdetij]
  convert hsub using 1 <;> ring

theorem coeff_sub_own_monomial
    (P : MvPolynomial (Fin 2) K) (d e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e
        (P - MvPolynomial.monomial d (MvPolynomial.coeff d P)) =
      if e = d then 0 else MvPolynomial.coeff e P := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial]
  by_cases h : e = d
  · subst e
    simp
  · have h' : d ≠ e := Ne.symm h
    simp [h, h']

/-- On a binary contact face the maximal exponent in the bumped coordinate is
represented by a unique monomial. -/
theorem singleCoordinate_initialForm_eq_monomial_of_contactFace
    (i j : Fin 2) (hij : i ≠ j)
    (scale bump D N : ℕ) (hscale : 0 < scale)
    (S : MvPolynomial (Fin 2) K)
    (hcontact : MvPolynomial.IsWeightedHomogeneous
      (binaryFirstContactWeight j scale bump) S (scale * D : ℕ))
    (dN : Fin 2 →₀ ℕ) (hdN : dN ∈ S.support)
    (hdNj : dN j = N)
    (hmaxN : ∀ d ∈ S.support, d j ≤ N) :
    initialForm (binarySingleCoordinateWeight j) N S =
      MvPolynomial.monomial dN (MvPolynomial.coeff dN S) := by
  ext e
  by_cases hed : e = dN
  · subst e
    rw [coeff_initialForm, MvPolynomial.coeff_monomial,
      weight_binarySingleCoordinateWeight, hdNj]
    simp
  · have hde : dN ≠ e := Ne.symm hed
    by_cases heN : Finsupp.weight (binarySingleCoordinateWeight j) e = (N : ℤ)
    · have hej : e j = N := by
        rw [weight_binarySingleCoordinateWeight] at heN
        exact_mod_cast heN
      have hec : MvPolynomial.coeff e S = 0 := by
        by_contra hne
        have hwE := hcontact hne
        have hwN := hcontact (MvPolynomial.mem_support_iff.mp hdN)
        rw [weight_binaryFirstContactWeight] at hwE hwN
        unfold binaryFirstContactExponentWeight at hwE hwN
        rw [hej] at hwE
        rw [hdNj] at hwN
        have hdeg : e.degree = dN.degree := by
          have hsZ : (0 : ℤ) < (scale : ℤ) := by exact_mod_cast hscale
          nlinarith
        exact hed (finTwo_exponent_eq_of_degree_eq_of_coord_eq_curved
          j e dN hdeg (by rw [hej, hdNj]))
      rw [coeff_initialForm, MvPolynomial.coeff_monomial]
      simp [heN, hec, hed, hde]
    · rw [coeff_initialForm, MvPolynomial.coeff_monomial]
      simp [heN, hed, hde]

private theorem binarySecondContact_level_lt_curved
    {M N : ℕ} (hMN : M < N) :
    2 * (M : ℤ) - 2 < (N : ℤ) + (M : ℤ) - 2 := by
  omega

set_option maxHeartbeats 2000000 in
/-- Finite first-contact rigidity: a singular-Hessian binary polynomial with
pure nonlinear top facet and zero transverse linear coefficient has no support
leaving that facet. -/
theorem binarySingularHessian_no_outsideSupport_of_pureTop
    (Q : MvPolynomial (Fin 2) K) (D : ℕ)
    (i j : Fin 2) (hij : i ≠ j)
    (hD : 2 ≤ D)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    (htopFacet : ∀ d ∈ Q.support, d.degree = D → d j = 0)
    (htopCoeff : MvPolynomial.coeff (Finsupp.single i D) Q ≠ 0)
    (hlinear : MvPolynomial.coeff (Finsupp.single j 1) Q = 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    ¬ (binaryOutsideSupport j Q).Nonempty := by
  intro hout
  rcases exists_minimal_binaryContactExponent (D := D) hout with
    ⟨d₀, hd₀, hmin⟩
  let scale := d₀ j
  let bump := D - d₀.degree
  have hlevel := selected_binaryContact_level hd₀ hmax htopFacet
  dsimp only at hlevel
  have hscale : 0 < scale := by simpa [scale] using hlevel.1
  have hd₀level :
      binaryFirstContactExponentWeight j scale bump d₀ =
        (scale * D : ℕ) := by simpa [scale, bump] using hlevel.2.2
  have hbound : IsWeightLE (binaryFirstContactWeight j scale bump)
      (scale * D : ℕ) Q := by
    simpa [scale, bump] using selected_binaryContact_isWeightLE hd₀ hmin hmax
  let S := initialForm (binaryFirstContactWeight j scale bump)
    (scale * D : ℕ) Q
  have hSdet : binaryDirectionalHessianDet (0 : Fin 2) 1 S = 0 := by
    dsimp [S]
    exact binaryDirectionalHessianDet_initialForm_eq_zero _ _ Q hbound hdet
  have hShom : MvPolynomial.IsWeightedHomogeneous
      (binaryFirstContactWeight j scale bump) S (scale * D : ℕ) := by
    dsimp [S]
    exact initialForm_isWeightedHomogeneous _ _ _
  have hd₀S : d₀ ∈ S.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [S]
    rw [coeff_initialForm, weight_binaryFirstContactWeight, hd₀level]
    simpa only [Nat.cast_mul, if_true] using
      (MvPolynomial.mem_support_iff.mp (mem_binaryOutsideSupport.mp hd₀).1)
  let dTop : Fin 2 →₀ ℕ := Finsupp.single i D
  have hdTopj : dTop j = 0 := by simp [dTop, Finsupp.single_apply, hij]
  have hdTopDegree : dTop.degree = D := by
    rw [finTwo_degree_eq_add_curved]
    fin_cases i <;> fin_cases j <;> simp_all [dTop, Finsupp.single_apply]
  have hdTopWeight :
      binaryFirstContactExponentWeight j scale bump dTop =
        (scale * D : ℕ) := by
    unfold binaryFirstContactExponentWeight
    rw [hdTopDegree, hdTopj]
    simp
  have hdTopS : dTop ∈ S.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [S]
    rw [coeff_initialForm, weight_binaryFirstContactWeight, hdTopWeight]
    simpa [dTop] using htopCoeff
  have hSne : S ≠ 0 := MvPolynomial.support_nonempty.mp ⟨dTop, hdTopS⟩

  rcases Finset.exists_max_image S.support (fun d => d j)
      (MvPolynomial.support_nonempty.mpr hSne) with ⟨dN, hdN, hNmax⟩
  let N := dN j
  have hNpos : 0 < N := by
    have hle := hNmax d₀ hd₀S
    dsimp [N]
    exact lt_of_lt_of_le (mem_binaryOutsideSupport.mp hd₀).2 hle
  have htransBound : IsWeightLE (binarySingleCoordinateWeight j) N S := by
    intro d hd
    rw [weight_binarySingleCoordinateWeight]
    exact_mod_cast hNmax d hd
  have hTmono := singleCoordinate_initialForm_eq_monomial_of_contactFace
    i j hij scale bump D N hscale S hShom dN hdN rfl hNmax
  let cN := MvPolynomial.coeff dN S
  have hcN : cN ≠ 0 := MvPolynomial.mem_support_iff.mp hdN
  have hTdet : binaryDirectionalHessianDet (0 : Fin 2) 1
      (initialForm (binarySingleCoordinateWeight j) N S) = 0 :=
    binaryDirectionalHessianDet_initialForm_eq_zero
      _ _ S htransBound hSdet
  have hmonoDet : binaryDirectionalHessianDet (0 : Fin 2) 1
      (MvPolynomial.monomial dN cN) = 0 := by
    rw [← hTmono]
    exact hTdet
  have hdNi : dN i = 0 := by
    by_cases hdeg : 2 ≤ dN.degree
    · exact binaryMonomial_zeroHessian_forces_otherExponent_zero
        hij hcN hNpos hdeg hmonoDet
    · have hle : dN.degree ≤ 1 := by omega
      have hjle : dN j ≤ dN.degree := finTwo_coord_le_degree_curved j dN
      have hjOne : dN j = 1 := by omega
      have hdegOne : dN.degree = 1 := by omega
      have hsingleDegree : (Finsupp.single j 1).degree = 1 := by
        rw [finTwo_degree_eq_add_curved]
        fin_cases j <;> simp
      have hsingleCoord : (Finsupp.single j 1) j = 1 := by simp
      have hdNsingle : dN = Finsupp.single j 1 :=
        finTwo_exponent_eq_of_degree_eq_of_coord_eq_curved j dN
          (Finsupp.single j 1)
          (hdegOne.trans hsingleDegree.symm)
          (by simpa [hsingleCoord] using hjOne)
      rw [hdNsingle]
      simp [Finsupp.single_apply, hij]
  have hdNdegree_eq : dN.degree = N := by
    dsimp [N]
    exact finTwo_degree_eq_coord_of_other_zero_curved i j hij dN hdNi
  have hNneOne : N ≠ 1 := by
    intro hN1
    have hdN_eq_single : dN = Finsupp.single j 1 := by
      apply finTwo_exponent_eq_of_degree_eq_of_coord_eq_curved j
      · rw [hdNdegree_eq, hN1]
        rw [finTwo_degree_eq_add_curved]
        fin_cases j <;> simp [Finsupp.single_apply]
      · dsimp [N] at hN1
        rw [hN1]
        simp [Finsupp.single_apply]
    have hdNQcoeff : MvPolynomial.coeff dN Q ≠ 0 := by
      have hdNSc := MvPolynomial.mem_support_iff.mp hdN
      dsimp [S] at hdNSc
      rw [coeff_initialForm] at hdNSc
      split at hdNSc
      · exact hdNSc
      · exact (hdNSc rfl).elim
    rw [hdN_eq_single, hlinear] at hdNQcoeff
    exact hdNQcoeff rfl
  have hNtwo : 2 ≤ N := by omega

  have hdTop_ne_dN : dTop ≠ dN := by
    intro hEq
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d j) hEq
    change dTop j = dN j at h
    rw [hdTopj] at h
    have hdNj_ne : dN j ≠ 0 := by simpa [N] using hNpos.ne'
    exact hdNj_ne h.symm
  have heraseNonempty : (S.support.erase dN).Nonempty :=
    ⟨dTop, Finset.mem_erase.mpr ⟨hdTop_ne_dN, hdTopS⟩⟩
  rcases Finset.exists_max_image (S.support.erase dN) (fun d => d j)
      heraseNonempty with ⟨dM, hdMerase, hMmax⟩
  have hdM : dM ∈ S.support := (Finset.mem_erase.mp hdMerase).2
  have hdMne : dM ≠ dN := (Finset.mem_erase.mp hdMerase).1
  let M := dM j
  have hMN : M < N := by
    have hle : M ≤ N := by
      dsimp [M, N]
      exact hNmax dM hdM
    apply lt_of_le_of_ne hle
    intro hEq
    have hcoord : dM j = dN j := by simpa [M, N] using hEq
    have hwM := hShom (MvPolynomial.mem_support_iff.mp hdM)
    have hwN := hShom (MvPolynomial.mem_support_iff.mp hdN)
    rw [weight_binaryFirstContactWeight] at hwM hwN
    unfold binaryFirstContactExponentWeight at hwM hwN
    rw [hcoord] at hwM
    have hdeg : dM.degree = dN.degree := by
      have hsZ : (0 : ℤ) < (scale : ℤ) := by exact_mod_cast hscale
      nlinarith
    have heq := finTwo_exponent_eq_of_degree_eq_of_coord_eq_curved
      j dM dN hdeg hcoord
    exact hdMne heq

  let P := MvPolynomial.monomial dN cN
  let R := S - P
  have hdecomp : S = P + R := by
    dsimp [R, P, cN]
    ring
  have hdMR : dM ∈ R.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [R, P, cN]
    rw [coeff_sub_own_monomial]
    simp [hdMne, MvPolynomial.mem_support_iff.mp hdM]
  have hRbound : IsWeightLE (binarySingleCoordinateWeight j) M R := by
    intro d hd
    rw [weight_binarySingleCoordinateWeight]
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    dsimp [R, P, cN] at hcoeff
    rw [coeff_sub_own_monomial] at hcoeff
    split at hcoeff
    · exact (hcoeff rfl).elim
    · rename_i hdn
      have hdS : d ∈ S.support := MvPolynomial.mem_support_iff.mpr hcoeff
      exact_mod_cast hMmax d (Finset.mem_erase.mpr ⟨hdn, hdS⟩)
  have hRhom : MvPolynomial.IsWeightedHomogeneous
      (binaryFirstContactWeight j scale bump) R (scale * D : ℕ) := by
    intro d hd
    have hcoeff := hd
    dsimp [R, P, cN] at hcoeff
    rw [coeff_sub_own_monomial] at hcoeff
    split at hcoeff
    · exact (hcoeff rfl).elim
    · exact hShom hcoeff
  have hTMmono := singleCoordinate_initialForm_eq_monomial_of_contactFace
    i j hij scale bump D M hscale R hRhom dM hdMR rfl
    (by
      intro d hd
      have h := hRbound hd
      rw [weight_binarySingleCoordinateWeight] at h
      exact_mod_cast h)
  let cM := MvPolynomial.coeff dM R
  have hcM : cM ≠ 0 := MvPolynomial.mem_support_iff.mp hdMR

  have hdMi_two : 2 ≤ dM i := by
    have hwM := hShom (MvPolynomial.mem_support_iff.mp hdM)
    have hwN := hShom (MvPolynomial.mem_support_iff.mp hdN)
    rw [weight_binaryFirstContactWeight] at hwM hwN
    unfold binaryFirstContactExponentWeight at hwM hwN
    have hdMdeg : dM.degree = dM i + M := by
      dsimp [M]
      exact finTwo_degree_eq_coord_add_other_curved i j hij dM
    rw [hdMdeg] at hwM
    rw [hdNdegree_eq] at hwN
    change
      (scale : ℤ) * ((dM i + M : ℕ) : ℤ) + (bump : ℤ) * (M : ℤ) =
        ((scale * D : ℕ) : ℤ) at hwM
    change
      (scale : ℤ) * (N : ℤ) + (bump : ℤ) * (N : ℤ) =
        ((scale * D : ℕ) : ℤ) at hwN
    have hEqZ :
        (scale : ℤ) * (dM i : ℤ) =
          ((scale + bump : ℕ) : ℤ) * ((N - M : ℕ) : ℤ) := by
      have hsub : ((N - M : ℕ) : ℤ) = (N : ℤ) - (M : ℤ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hMN)]
      rw [hsub]
      push_cast at hwM hwN ⊢
      linear_combination hwM - hwN
    by_contra hnot
    have hlt : dM i < 2 := Nat.lt_of_not_ge hnot
    have hle : dM i ≤ 1 := by
      exact Nat.le_of_lt_succ hlt
    have hleft : scale * dM i ≤ scale := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left scale hle
    have hgap : 1 ≤ N - M := Nat.sub_pos_of_lt hMN
    have hright : scale + bump ≤ (scale + bump) * (N - M) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (scale + bump) hgap
    have hEqNat : scale * dM i = (scale + bump) * (N - M) := by
      exact_mod_cast hEqZ
    have hbump : 0 < bump := by
      simpa [bump] using hlevel.2.1
    have hscale_lt : scale < scale + bump := Nat.lt_add_of_pos_right hbump
    have hcontra : scale + bump ≤ scale := by
      calc
        scale + bump ≤ (scale + bump) * (N - M) := hright
        _ = scale * dM i := hEqNat.symm
        _ ≤ scale := hleft
    exact (Nat.not_lt_of_ge hcontra) hscale_lt

  have hPi : directionalSecondDerivative i P = 0 := by
    dsimp [P]
    unfold directionalSecondDerivative
    simp [MvPolynomial.pderiv_monomial, hdNi]
  have hPij : directionalMixedDerivative i j P = 0 := by
    dsimp [P]
    unfold directionalMixedDerivative
    simp [MvPolynomial.pderiv_monomial, hdNi]
  have hcrossSimplify :
      binaryHessianDetCross P R =
        directionalSecondDerivative i R * directionalSecondDerivative j P := by
    rw [binaryHessianDetCross_eq_directional_of_ne i j hij P R, hPi, hPij]
    ring

  let w := binarySingleCoordinateWeight j
  have hPhom : MvPolynomial.IsWeightedHomogeneous w P N := by
    dsimp [P]
    exact MvPolynomial.isWeightedHomogeneous_monomial w dN cN (by
      change Finsupp.weight (binarySingleCoordinateWeight j) dN = (dN j : ℤ)
      exact weight_binarySingleCoordinateWeight j dN)
  have hcrossTop :
      initialForm w ((N : ℤ) + (M : ℤ) - 2) (binaryHessianDetCross P R) =
        directionalSecondDerivative i (initialForm w M R) *
          directionalSecondDerivative j P := by
    rw [hcrossSimplify]
    exact initialForm_singleCoordinate_cross_secondDerivative
      i j hij (N : ℤ) (M : ℤ) P R hPhom hRbound
  have hcrossTopNe :
      initialForm w ((N : ℤ) + (M : ℤ) - 2) (binaryHessianDetCross P R) ≠ 0 := by
    rw [hcrossTop, hTMmono]
    apply mul_ne_zero
    · exact directionalSecondDerivative_monomial_ne_zero_of_two_le i hcM hdMi_two
    · exact directionalSecondDerivative_monomial_ne_zero_of_two_le j hcN hNtwo

  have hRdetLE := binaryDirectionalHessianDet_isWeightLE_singleCoordinate
    i j hij (M : ℤ) R hRbound
  have hlevelgt : 2 * (M : ℤ) - 2 < (N : ℤ) + (M : ℤ) - 2 :=
    binarySecondContact_level_lt_curved hMN
  have hRdetTop :
      initialForm w ((N : ℤ) + (M : ℤ) - 2)
        (binaryDirectionalHessianDet (0 : Fin 2) 1 R) = 0 :=
    initialForm_eq_zero_of_isWeightLE hRdetLE hlevelgt
  have hPdet : binaryDirectionalHessianDet (0 : Fin 2) 1 P = 0 := by
    dsimp [P]
    exact hmonoDet
  have hsum :
      binaryHessianDetCross P R +
        binaryDirectionalHessianDet (0 : Fin 2) 1 R = 0 := by
    have hexpand := binaryDirectionalHessianDet_add_cross P R
    rw [← hdecomp] at hexpand
    rw [hSdet, hPdet] at hexpand
    simpa only [zero_add] using hexpand.symm
  have hcomponent := congrArg
    (fun T : MvPolynomial (Fin 2) K =>
      initialForm w ((N : ℤ) + (M : ℤ) - 2) T) hsum
  change
    initialForm w ((N : ℤ) + (M : ℤ) - 2)
        (binaryHessianDetCross P R + binaryDirectionalHessianDet (0 : Fin 2) 1 R) =
      initialForm w ((N : ℤ) + (M : ℤ) - 2) 0 at hcomponent
  rw [initialForm_add, hRdetTop, add_zero, initialForm_zero] at hcomponent
  exact hcrossTopNe hcomponent

/-! ## Determinant-one shear -/

def binarySourceShearVariable
    (t : K) (i : Fin 2) : MvPolynomial (Fin 2) K :=
  if i = 0 then MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1
  else MvPolynomial.X i

noncomputable def binarySourceShearHom
    (t : K) : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (binarySourceShearVariable t)

@[simp] theorem binarySourceShearHom_C (t a : K) :
    binarySourceShearHom t (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [binarySourceShearHom]

@[simp] theorem binarySourceShearHom_X (t : K) (i : Fin 2) :
    binarySourceShearHom t (MvPolynomial.X i) = binarySourceShearVariable t i := by
  simp [binarySourceShearHom]

theorem binarySourceShearHom_inverse
    (t : K) (P : MvPolynomial (Fin 2) K) :
    binarySourceShearHom (-t) (binarySourceShearHom t P) = P := by
  let φ : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
    (binarySourceShearHom (-t)).comp (binarySourceShearHom t)
  have hφ : φ = RingHom.id (MvPolynomial (Fin 2) K) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ, binarySourceShearHom]
    · intro i
      fin_cases i <;> simp [φ, binarySourceShearHom,
        binarySourceShearVariable] <;> ring
  change φ P = P
  rw [hφ]
  rfl

theorem binarySourceShearHom_injective (t : K) :
    Function.Injective (binarySourceShearHom t) := by
  intro P Q h
  have h' := congrArg (binarySourceShearHom (-t)) h
  simpa [binarySourceShearHom_inverse] using h'

theorem binarySourceShearVariable_isHomogeneous_one
    (t : K) (i : Fin 2) :
    (binarySourceShearVariable t i).IsHomogeneous 1 := by
  fin_cases i
  · simp [binarySourceShearVariable]
    exact (MvPolynomial.isHomogeneous_X K (0 : Fin 2)).add
      (MvPolynomial.isHomogeneous_C_mul_X t (1 : Fin 2))
  · simpa [binarySourceShearVariable] using
      (MvPolynomial.isHomogeneous_X K (1 : Fin 2))

theorem binarySourceShearHom_isHomogeneous
    (t : K) {D : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : P.IsHomogeneous D) :
    (binarySourceShearHom t P).IsHomogeneous D := by
  have h := hP.eval₂ MvPolynomial.C (binarySourceShearVariable t)
    (fun a => MvPolynomial.isHomogeneous_C (Fin 2) a)
    (fun i => binarySourceShearVariable_isHomogeneous_one t i)
  simpa [binarySourceShearHom] using h

theorem binaryOrdinary_isWeightedHomogeneous_of_isHomogeneous
    {P : MvPolynomial (Fin 2) K} {D : ℕ}
    (hP : P.IsHomogeneous D) :
    MvPolynomial.IsWeightedHomogeneous binaryOrdinaryIntegerWeight P D := by
  intro d hd
  rw [binaryOrdinaryIntegerWeight_eq_degree]
  have hone : Finsupp.weight (1 : Fin 2 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  have hdeg : Finsupp.weight (1 : Fin 2 → ℕ) d = D := hP hd
  rw [hone] at hdeg
  exact_mod_cast hdeg

theorem binarySourceShearHom_binaryOrdinaryDegreeComponent
    (t : K) (P : MvPolynomial (Fin 2) K) (D : ℕ) :
    binarySourceShearHom t (binaryOrdinaryDegreeComponent P D) =
      binaryOrdinaryDegreeComponent (binarySourceShearHom t P) D := by
  classical
  unfold binaryOrdinaryDegreeComponent
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, initialForm_add, hP, hQ]
  | monomial n a =>
      have hmono : (MvPolynomial.monomial n a).IsHomogeneous n.degree :=
        MvPolynomial.isHomogeneous_monomial a rfl
      have hsmono := binarySourceShearHom_isHomogeneous t hmono
      have hmonoW := binaryOrdinary_isWeightedHomogeneous_of_isHomogeneous hmono
      have hsmonoW := binaryOrdinary_isWeightedHomogeneous_of_isHomogeneous hsmono
      by_cases hdeg : n.degree = D
      · subst D
        rw [initialForm_eq_self_of_isWeightedHomogeneous hmonoW,
          initialForm_eq_self_of_isWeightedHomogeneous hsmonoW]
      · have hcast : (D : ℤ) ≠ (n.degree : ℤ) := by
          exact_mod_cast (Ne.symm hdeg)
        rw [initialForm_eq_zero_of_isWeightedHomogeneous hmonoW D hcast,
          map_zero]
        exact (initialForm_eq_zero_of_isWeightedHomogeneous hsmonoW D hcast).symm

theorem pderiv_zero_binarySourceShearHom
    (t : K) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv 0 (binarySourceShearHom t P) =
      binarySourceShearHom t (MvPolynomial.pderiv 0 P) := by
  apply MvPolynomial.induction_on P
  · intro a
    simp
  · intro P Q hP hQ
    simp [hP, hQ]
  · intro P n hP
    fin_cases n <;>
      simp only [map_mul, binarySourceShearHom_X,
        MvPolynomial.pderiv_mul, map_add, hP] <;>
      simp [binarySourceShearVariable] <;> ring

theorem pderiv_one_binarySourceShearHom
    (t : K) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv 1 (binarySourceShearHom t P) =
      binarySourceShearHom t (MvPolynomial.pderiv 1 P) +
        MvPolynomial.C t * binarySourceShearHom t (MvPolynomial.pderiv 0 P) := by
  apply MvPolynomial.induction_on P
  · intro a
    simp
  · intro P Q hP hQ
    simp [hP, hQ, mul_add, add_mul] <;> ring
  · intro P n hP
    fin_cases n <;>
      simp only [map_mul, binarySourceShearHom_X,
        MvPolynomial.pderiv_mul, map_add, hP] <;>
      simp [binarySourceShearVariable] <;> ring

theorem binaryDirectionalHessianDet_binarySourceShearHom
    (t : K) (P : MvPolynomial (Fin 2) K) :
    binaryDirectionalHessianDet (0 : Fin 2) 1 (binarySourceShearHom t P) =
      binarySourceShearHom t
        (binaryDirectionalHessianDet (0 : Fin 2) 1 P) := by
  have h00 :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (binarySourceShearHom t P)) =
        binarySourceShearHom t (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 P)) := by
    rw [pderiv_zero_binarySourceShearHom, pderiv_zero_binarySourceShearHom]
  have h01 :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (binarySourceShearHom t P)) =
        binarySourceShearHom t (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P)) +
          MvPolynomial.C t *
            binarySourceShearHom t (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 P)) := by
    rw [pderiv_one_binarySourceShearHom]
    rw [map_add, MvPolynomial.pderiv_C_mul]
    rw [pderiv_zero_binarySourceShearHom, pderiv_zero_binarySourceShearHom]
  have h11 :
      MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (binarySourceShearHom t P)) =
        binarySourceShearHom t (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 P)) +
          (MvPolynomial.C t + MvPolynomial.C t) *
            binarySourceShearHom t (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P)) +
          (MvPolynomial.C t * MvPolynomial.C t) *
            binarySourceShearHom t (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 P)) := by
    rw [pderiv_one_binarySourceShearHom]
    rw [map_add, MvPolynomial.pderiv_C_mul]
    rw [pderiv_one_binarySourceShearHom, pderiv_one_binarySourceShearHom]
    rw [pderiv_comm_backport 0 1 P]
    ring
  unfold binaryDirectionalHessianDet directionalSecondDerivative
    directionalMixedDerivative
  rw [h00, h11, h01]
  simp only [map_sub, map_mul, map_pow]
  ring

theorem binarySourceShearHom_gradientRatioLinearForm_axis
    (c : Fin 2 → K) (hc0 : c 0 ≠ 0) :
    binarySourceShearHom (-(c 1 / c 0)) (gradientRatioLinearForm c) =
      MvPolynomial.C (c 0) * MvPolynomial.X 0 := by
  classical
  unfold gradientRatioLinearForm
  simp only [map_sum, map_mul, binarySourceShearHom_C,
    binarySourceShearHom_X]
  rw [Fin.sum_univ_two]
  simp [binarySourceShearVariable, hc0]
  have hscalar : c 0 * (c 1 / c 0) = c 1 := by
    field_simp
  have hCscalar :
      (MvPolynomial.C (c 0) : MvPolynomial (Fin 2) K) *
          MvPolynomial.C (c 1 / c 0) = MvPolynomial.C (c 1) := by
    rw [← MvPolynomial.C_mul, hscalar]
  rw [mul_add, mul_neg, ← mul_assoc, hCscalar]
  ring

theorem binarySourceShearHom_transverseDeriv_axis
    (c : Fin 2 → K) (hc0 : c 0 ≠ 0)
    (P : MvPolynomial (Fin 2) K) :
    binarySourceShearHom (-(c 1 / c 0))
        (binaryLinearFormTransverseDeriv c P) =
      MvPolynomial.C (-c 0) *
        MvPolynomial.pderiv 1
          (binarySourceShearHom (-(c 1 / c 0)) P) := by
  let t : K := -(c 1 / c 0)
  have ht : c 0 * t = -c 1 := by
    dsimp [t]
    field_simp
  change binarySourceShearHom t (binaryLinearFormTransverseDeriv c P) =
    MvPolynomial.C (-c 0) * MvPolynomial.pderiv 1 (binarySourceShearHom t P)
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
  simp only [map_add, map_mul, map_neg, binarySourceShearHom_C]
  rw [pderiv_one_binarySourceShearHom]
  have hCt : (MvPolynomial.C (c 1) : MvPolynomial (Fin 2) K) =
      -(MvPolynomial.C (c 0) * MvPolynomial.C t) := by
    rw [← MvPolynomial.C_mul, ht]
    simp
  rw [hCt]
  ring

/-- Every ordinary component above a support degree ceiling is zero. -/
theorem binaryOrdinaryDegreeComponent_eq_zero_of_above_max
    (Q : MvPolynomial (Fin 2) K) (D n : ℕ)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    (hDn : D < n) :
    binaryOrdinaryDegreeComponent Q n = 0 := by
  ext d
  unfold binaryOrdinaryDegreeComponent
  rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree]
  split
  · rename_i hw
    have hdeg : d.degree = n := by exact_mod_cast hw
    have hcoeff : MvPolynomial.coeff d Q = 0 := by
      by_contra hne
      have hd : d ∈ Q.support := MvPolynomial.mem_support_iff.mpr hne
      have := hmax d hd
      omega
    exact hcoeff
  · rfl

theorem binarySourceShearHom_support_degree_le
    (t : K) (Q : MvPolynomial (Fin 2) K) (D : ℕ)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D) :
    ∀ d ∈ (binarySourceShearHom t Q).support, d.degree ≤ D := by
  intro d hd
  by_contra hnot
  have hDn : D < d.degree := by omega
  have hzero := binaryOrdinaryDegreeComponent_eq_zero_of_above_max
    Q D d.degree hmax hDn
  have hcomm := binarySourceShearHom_binaryOrdinaryDegreeComponent
    t Q d.degree
  rw [hzero, map_zero] at hcomm
  have hcomponent :
      binaryOrdinaryDegreeComponent (binarySourceShearHom t Q) d.degree = 0 :=
    hcomm.symm
  have hc0 : MvPolynomial.coeff d
      (binaryOrdinaryDegreeComponent (binarySourceShearHom t Q) d.degree) = 0 := by
    rw [hcomponent]
    simp
  rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved _ d d.degree rfl] at hc0
  exact (MvPolynomial.mem_support_iff.mp hd) hc0

/-- A zero binary linear jet is preserved by the linear shear. -/
theorem binarySourceShearHom_linearCoeff_zero
    (t : K) (Q : MvPolynomial (Fin 2) K)
    (hlinear : ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) Q = 0) :
    ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) (binarySourceShearHom t Q) = 0 := by
  have hQone : binaryOrdinaryDegreeComponent Q 1 = 0 := by
    ext d
    by_cases hdeg : d.degree = 1
    · have hsum : d 0 + d 1 = 1 := by
        rw [← finTwo_degree_eq_add_curved d]
        exact hdeg
      have hcases :
          (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
      rcases hcases with h | h
      · have hd : d = Finsupp.single 0 1 := by
          apply Finsupp.ext
          intro k
          fin_cases k <;> simp [h.1, h.2, Finsupp.single_apply]
        rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q d 1 hdeg,
          hd, hlinear 0]
        simp
      · have hd : d = Finsupp.single 1 1 := by
          apply Finsupp.ext
          intro k
          fin_cases k <;> simp [h.1, h.2, Finsupp.single_apply]
        rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q d 1 hdeg,
          hd, hlinear 1]
        simp
    · unfold binaryOrdinaryDegreeComponent
      rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree]
      have hcast : (d.degree : ℤ) ≠ (1 : ℤ) := by exact_mod_cast hdeg
      simp [hcast]
  have hSone : binaryOrdinaryDegreeComponent (binarySourceShearHom t Q) 1 = 0 := by
    rw [← binarySourceShearHom_binaryOrdinaryDegreeComponent, hQone]
    simp
  intro i
  have hdeg : (Finsupp.single i 1).degree = 1 := by
    rw [finTwo_degree_eq_add_curved]
    fin_cases i <;> simp [Finsupp.single_apply]
  have hc0 : MvPolynomial.coeff (Finsupp.single i 1)
      (binaryOrdinaryDegreeComponent (binarySourceShearHom t Q) 1) = 0 := by
    rw [hSone]
    simp
  rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved _ _ 1 hdeg] at hc0
  exact hc0

/-! ## Elimination of the curved constructor -/

theorem binarySingularHessian_nextLayerCurved_impossible
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ) (H : MvPolynomial (Fin 2) K)
    (hD : 2 ≤ D)
    (H_eq : H = binaryOrdinaryDegreeComponent Q D)
    (H_ne_zero : H ≠ 0)
    (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
    (a : K) (c : Fin 2 → K)
    (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (R : MvPolynomial (Fin 2) K)
    (R_eq : R = Q - H)
    (E : ℕ) (G : MvPolynomial (Fin 2) K)
    (E_lt_D : E < D)
    (G_eq : G = binaryOrdinaryDegreeComponent R E)
    (G_ne_zero : G ≠ 0)
    (transverse_first_ne_zero : binaryLinearFormTransverseDeriv c G ≠ 0)
    (hlinear : ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) Q = 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    False := by
  have ha : a ≠ 0 := by
    intro ha0
    apply H_ne_zero
    rw [normalForm, ha0]
    simp
  have hcNonzero : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    apply H_ne_zero
    rw [normalForm]
    have hL : gradientRatioLinearForm c = 0 := by
      classical
      unfold gradientRatioLinearForm
      rw [Fin.sum_univ_two]
      simp [hnot.1, hnot.2]
    rw [hL]
    have hD0 : D ≠ 0 := by omega
    simp [hD0]
  have hHwh : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D := by
    rw [H_eq]
    exact initialForm_isWeightedHomogeneous _ _ _
  have hHEzero : initialForm binaryOrdinaryIntegerWeight E H = 0 := by
    apply initialForm_eq_zero_of_isWeightedHomogeneous hHwh E
    exact_mod_cast (ne_of_lt E_lt_D)
  have hGQ : G = binaryOrdinaryDegreeComponent Q E := by
    rw [G_eq, R_eq]
    unfold binaryOrdinaryDegreeComponent
    simp only [map_sub]
    rw [hHEzero, sub_zero]

  by_cases hc0 : c 0 = 0
  · have hc1 : c 1 ≠ 0 := by
      rcases hcNonzero with h | h
      · exact (h hc0).elim
      · exact h
    have htransG : MvPolynomial.pderiv 0 G ≠ 0 := by
      intro hz
      apply transverse_first_ne_zero
      unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
      rw [hc0, hz]
      simp
    have houtside : (binaryOutsideSupport (0 : Fin 2) Q).Nonempty := by
      rcases MvPolynomial.support_nonempty.mpr htransG with ⟨m, hm⟩
      have hcoeff := coeff_pderiv_backport (K := K) (0 : Fin 2) G m
      have hmcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv 0 G) ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hm
      have hsource :
          MvPolynomial.coeff (m + Finsupp.single (0 : Fin 2) 1) G ≠ 0 := by
        intro hz
        rw [hz] at hcoeff
        simp at hcoeff
        exact hmcoeff hcoeff
      let d := m + Finsupp.single (0 : Fin 2) 1
      have hdj : 0 < d (0 : Fin 2) := by
        dsimp [d]
        simp [Finsupp.single_apply]
      have hdQ : d ∈ Q.support := by
        rw [hGQ] at hsource
        unfold binaryOrdinaryDegreeComponent at hsource
        rw [coeff_initialForm] at hsource
        split at hsource
        · exact MvPolynomial.mem_support_iff.mpr hsource
        · exact (hsource rfl).elim
      exact ⟨d, mem_binaryOutsideSupport.mpr ⟨hdQ, hdj⟩⟩
    have hL : gradientRatioLinearForm c =
        MvPolynomial.C (c 1) * MvPolynomial.X 1 := by
      classical
      unfold gradientRatioLinearForm
      rw [Fin.sum_univ_two]
      simp [hc0]
    have hHaxis : H =
        MvPolynomial.C (a * (c 1) ^ D) * (MvPolynomial.X 1) ^ D := by
      rw [normalForm, hL, mul_pow, ← MvPolynomial.C_pow, ← mul_assoc,
        ← MvPolynomial.C_mul]
    have htopCoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) D) Q ≠ 0 := by
      let dtop : Fin 2 →₀ ℕ := Finsupp.single (1 : Fin 2) D
      have hd : dtop.degree = D := by
        dsimp [dtop]
        rw [finTwo_degree_eq_add_curved]
        simp [Finsupp.single_apply]
      have hcH : MvPolynomial.coeff dtop H = MvPolynomial.coeff dtop Q := by
        rw [H_eq]
        exact coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q dtop D hd
      have hleft : MvPolynomial.coeff dtop H = a * c 1 ^ D := by
        rw [hHaxis]
        dsimp [dtop]
        rw [MvPolynomial.C_mul_X_pow_eq_monomial]
        simp
      have hscalar : a * c 1 ^ D ≠ 0 := mul_ne_zero ha (pow_ne_zero D hc1)
      intro hz
      apply hscalar
      rw [← hleft, hcH, hz]
    have htopFacet :
        ∀ d ∈ Q.support, d.degree = D → d (0 : Fin 2) = 0 := by
      intro d hd hddeg
      have hcoeff : MvPolynomial.coeff d H ≠ 0 := by
        rw [H_eq]
        unfold binaryOrdinaryDegreeComponent
        rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree, hddeg]
        simp [MvPolynomial.mem_support_iff.mp hd]
      rw [hHaxis] at hcoeff
      have hpderiv : MvPolynomial.pderiv (0 : Fin 2)
          (MvPolynomial.C (a * c 1 ^ D) * (MvPolynomial.X 1) ^ D) = 0 := by
        simp
      exact exponent_eq_zero_of_pderiv_eq_zero 0 _ hpderiv d hcoeff
    exact (binarySingularHessian_no_outsideSupport_of_pureTop
      Q D 1 0 (by decide) hD maximal htopFacet htopCoeff (hlinear 0) hdet)
      houtside

  · let t : K := -(c 1 / c 0)
    let Qs := binarySourceShearHom t Q
    let Gs := binarySourceShearHom t G
    have hdetS : binaryDirectionalHessianDet (0 : Fin 2) 1 Qs = 0 := by
      dsimp [Qs, t]
      rw [binaryDirectionalHessianDet_binarySourceShearHom, hdet]
      simp
    have hGsComp : Gs = binaryOrdinaryDegreeComponent Qs E := by
      dsimp [Gs, Qs, t]
      rw [hGQ, binarySourceShearHom_binaryOrdinaryDegreeComponent]
    have htransS : MvPolynomial.pderiv 1 Gs ≠ 0 := by
      intro hz
      apply transverse_first_ne_zero
      apply binarySourceShearHom_injective t
      have hcov := binarySourceShearHom_transverseDeriv_axis c hc0 G
      dsimp [t] at hcov ⊢
      rw [hcov, hz]
      simp
    have houtside : (binaryOutsideSupport (1 : Fin 2) Qs).Nonempty := by
      rcases MvPolynomial.support_nonempty.mpr htransS with ⟨m, hm⟩
      have hcoeff := coeff_pderiv_backport (K := K) (1 : Fin 2) Gs m
      have hmcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv 1 Gs) ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hm
      have hsource :
          MvPolynomial.coeff (m + Finsupp.single (1 : Fin 2) 1) Gs ≠ 0 := by
        intro hz
        rw [hz] at hcoeff
        simp at hcoeff
        exact hmcoeff hcoeff
      let d := m + Finsupp.single (1 : Fin 2) 1
      have hdj : 0 < d (1 : Fin 2) := by
        dsimp [d]
        simp [Finsupp.single_apply]
      have hdQ : d ∈ Qs.support := by
        rw [hGsComp] at hsource
        unfold binaryOrdinaryDegreeComponent at hsource
        rw [coeff_initialForm] at hsource
        split at hsource
        · exact MvPolynomial.mem_support_iff.mpr hsource
        · exact (hsource rfl).elim
      exact ⟨d, mem_binaryOutsideSupport.mpr ⟨hdQ, hdj⟩⟩
    have hHsComp :
        binaryOrdinaryDegreeComponent Qs D =
          MvPolynomial.C (a * (c 0) ^ D) * (MvPolynomial.X 0) ^ D := by
      have hmap := congrArg (binarySourceShearHom t) H_eq
      rw [binarySourceShearHom_binaryOrdinaryDegreeComponent] at hmap
      have haxis := binarySourceShearHom_gradientRatioLinearForm_axis c hc0
      dsimp [t] at hmap haxis
      rw [normalForm, map_mul, map_pow, binarySourceShearHom_C, haxis] at hmap
      rw [← hmap]
      rw [mul_pow, ← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]
    have htopCoeffS :
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) D) Qs ≠ 0 := by
      let dtop : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) D
      have hd : dtop.degree = D := by
        dsimp [dtop]
        rw [finTwo_degree_eq_add_curved]
        simp [Finsupp.single_apply]
      have hcComp : MvPolynomial.coeff dtop
          (binaryOrdinaryDegreeComponent Qs D) = MvPolynomial.coeff dtop Qs :=
        coeff_binaryOrdinaryDegreeComponent_of_degree_curved Qs dtop D hd
      have hright : MvPolynomial.coeff dtop
          (MvPolynomial.C (a * c 0 ^ D) * MvPolynomial.X 0 ^ D) =
          a * c 0 ^ D := by
        dsimp [dtop]
        rw [MvPolynomial.C_mul_X_pow_eq_monomial]
        simp
      have hscalar : a * c 0 ^ D ≠ 0 := mul_ne_zero ha (pow_ne_zero D hc0)
      intro hz
      apply hscalar
      rw [← hright, ← hHsComp, hcComp, hz]
    have htopFacetS :
        ∀ d ∈ Qs.support, d.degree = D → d (1 : Fin 2) = 0 := by
      intro d hd hddeg
      have hcoeff : MvPolynomial.coeff d
          (binaryOrdinaryDegreeComponent Qs D) ≠ 0 := by
        unfold binaryOrdinaryDegreeComponent
        rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree, hddeg]
        simp [MvPolynomial.mem_support_iff.mp hd]
      rw [hHsComp] at hcoeff
      have hpderiv : MvPolynomial.pderiv (1 : Fin 2)
          (MvPolynomial.C (a * c 0 ^ D) * (MvPolynomial.X 0) ^ D) = 0 := by
        simp
      exact exponent_eq_zero_of_pderiv_eq_zero 1 _ hpderiv d hcoeff
    have hmaxS : ∀ d ∈ Qs.support, d.degree ≤ D := by
      dsimp [Qs]
      exact binarySourceShearHom_support_degree_le t Q D maximal
    have hlinearS := binarySourceShearHom_linearCoeff_zero t Q hlinear
    exact (binarySingularHessian_no_outsideSupport_of_pureTop
      Qs D 0 1 (by decide) hD hmaxS htopFacetS htopCoeffS
        (hlinearS 1) hdetS) houtside

/-! ## Curved-free frontier -/

inductive BinarySingularHessianCurvedEliminatedFrontier
    (Q : MvPolynomial (Fin 2) K) : Type (u + 1)
  | lowDegree
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
  | nonlinearCollapsed
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K) (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (Q_eq_H : Q = H)
  | nonlinearNextAffine
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K) (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H) (R_ne_zero : R ≠ 0)
      (E : ℕ) (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D) (E_le_one : E ≤ 1)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero : binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
  | nonlinearNextLocked
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K) (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H) (R_ne_zero : R ≠ 0)
      (E : ℕ) (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D) (E_ge_two : 2 ≤ E)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero : binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
      (transverse_first_zero : binaryLinearFormTransverseDeriv c G = 0)

theorem binarySingularHessian_curvedEliminatedFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hlinear : ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) Q = 0) :
    Nonempty (BinarySingularHessianCurvedEliminatedFrontier Q) := by
  rcases binarySingularHessian_nextLayerCurvatureFrontier Q hQ hdet with ⟨F⟩
  cases F with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
        a c normalForm Q_eq_H⟩
  | nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero =>
      exact ⟨.nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
        R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero remainder_maximal
        G_homogeneous transverse_sq_zero⟩
  | nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero transverse_first_zero =>
      exact ⟨.nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
        R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
        G_homogeneous transverse_sq_zero transverse_first_zero⟩
  | nonlinearNextCurved D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero transverse_first_ne_zero next_det_ne_zero =>
      exact False.elim (binarySingularHessian_nextLayerCurved_impossible
        Q D H hD H_eq H_ne_zero maximal a c normalForm R R_eq E G E_lt_D
        G_eq G_ne_zero transverse_first_ne_zero hlinear hdet)

/-! ## HC4 carrier adapter -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The ambient zero linear jet descends through the injective binary
planarisation. -/
theorem DirectClosingCanonicalSquareBinaryStationaryCoreData.binaryFace_linear_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
    (i : Fin 2) :
    MvPolynomial.coeff (Finsupp.single i 1) D.binaryFace = 0 := by
  let emb := transverseBaseEmbedding D.D.index D.hindex
  have hder := congrArg (MvPolynomial.pderiv (emb i)) D.face_eq_rename
  have hcomm := pderiv_rename_transverseBaseEmbedding
    D.D.index D.hindex i D.binaryFace
  rw [hcomm] at hder
  have hc0 := congrArg
    (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff 0 P) hder
  change MvPolynomial.coeff 0
      (MvPolynomial.rename emb (MvPolynomial.pderiv i D.binaryFace)) =
    MvPolynomial.coeff 0 (MvPolynomial.pderiv (emb i) D.face) at hc0
  have hrename :
      MvPolynomial.coeff 0
          (MvPolynomial.rename emb (MvPolynomial.pderiv i D.binaryFace)) =
        MvPolynomial.coeff 0 (MvPolynomial.pderiv i D.binaryFace) := by
    simpa only [MvPolynomial.constantCoeff_eq] using
      (MvPolynomial.constantCoeff_rename emb
        (MvPolynomial.pderiv i D.binaryFace))
  rw [hrename] at hc0
  rw [coeff_pderiv_backport, coeff_pderiv_backport] at hc0
  simp only [zero_add, Nat.cast_one, one_mul] at hc0
  have hamb := D.face_linear_zero (emb i)
  rw [hamb] at hc0
  simpa using hc0

/-- Assembly-facing curved-free frontier for the actual transverse stationary
binary core. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.curvedEliminatedFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianCurvedEliminatedFrontier
      D.binaryData.binaryFace) := by
  exact binarySingularHessian_curvedEliminatedFrontier
    D.binaryData.binaryFace
    D.binaryData.binaryFace_ne_zero
    D.binaryData.binary_det_zero
    D.binaryData.binaryFace_linear_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end
end HC4.Valuation
