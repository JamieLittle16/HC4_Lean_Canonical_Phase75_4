module

public import HC4.Polynomial.WeightedExtremalAffinePlane
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# A full-source split row gives planar injectivity

No clock hypothesis is needed here. A Hessian row supported at a
single off-diagonal coordinate splits off a hyperbolic pair. The
determinant-one identity makes that entry a nonzero constant.
Fix the recovered base coordinate, then apply planar JC2 to the
remaining two gradient components. The last coordinate is affine.

In particular a weight equal to the positive cap, with a unique
zero-weight coordinate, is already terminal even at positive clock.
-/

@[expose] public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A vanishing partial gives invariance of evaluation when just
that coordinate is changed. -/
theorem extremal_eval_eq_of_pderiv_zero
    (f : MvPolynomial (Fin 4) K) (k : Fin 4) (hf : pderiv k f = 0)
    (x y : Fin 4 → K) (hxy : ∀ i, i ≠ k → x i = y i) :
    MvPolynomial.eval x f = MvPolynomial.eval y f := by
  classical
  calc
    MvPolynomial.eval x f = ∑ u ∈ f.support, MvPolynomial.eval x (monomial u (coeff u f)) := by
      rw [← map_sum, ← f.as_sum]
    _ = ∑ u ∈ f.support, MvPolynomial.eval y (monomial u (coeff u f)) := ?_
    _ = MvPolynomial.eval y f := by rw [← map_sum, ← f.as_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  congr 1
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i ≠ k := by
    intro he
    subst i
    exact (Finsupp.mem_support_iff.mp hi)
      (exponent_eq_zero_of_pderiv_eq_zero k f hf u (MvPolynomial.mem_support_iff.mp hu))
  change x i ^ u i = y i ^ u i
  rw [hxy i hne]

/-- Specialize the original polynomial at a fixed base value and
zero in the split partner. -/
def splitRowSlice (c : K) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval ![MvPolynomial.C c, X 0, X 1, 0]

theorem splitRowSlice_eval (c : K) (f : MvPolynomial (Fin 4) K) (p : Fin 2 → K) :
    MvPolynomial.eval p (splitRowSlice c f) =
      MvPolynomial.eval ![c, p 0, p 1, 0] f := by
  let E : MvPolynomial (Fin 2) K →ₐ[K] K := MvPolynomial.aeval p
  have h : E.comp (splitRowSlice c) = MvPolynomial.aeval ![c,p 0,p 1,0] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [E, splitRowSlice]
  exact AlgHom.congr_fun h f

theorem splitRowSlice_pderiv_zero (c : K) (f : MvPolynomial (Fin 4) K) :
    pderiv 0 (splitRowSlice c f) = splitRowSlice c (pderiv 1 f) := by
  unfold splitRowSlice
  rw [RankThreeCubic.derivation_aeval, Fin.sum_univ_four]
  simp [pderiv_X_of_ne]

theorem splitRowSlice_pderiv_one (c : K) (f : MvPolynomial (Fin 4) K) :
    pderiv 1 (splitRowSlice c f) = splitRowSlice c (pderiv 2 f) := by
  unfold splitRowSlice
  rw [RankThreeCubic.derivation_aeval, Fin.sum_univ_four]
  simp [pderiv_X_of_ne]

set_option maxHeartbeats 4000000 in
/-- Exact planar reduction of a full Hessian split row in standard
coordinates. The split row need not be part of a leading form. -/
theorem gradient_injective_of_splitRow_standard
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : MvPolynomial (Fin 4) K) (hdet : hessianDeterminant P = 1)
    (hrow : ∀ i : Fin 4, i ≠ 0 → hessian P 3 i = 0) :
    Function.Injective (mvGradientMap P) := by
  classical
  let H := hessian P
  have hs (i j : Fin 4) : H i j = H j i := pderiv_comm_backport j i P
  have hr1 : H 3 1 = 0 := hrow 1 (by decide)
  have hr2 : H 3 2 = 0 := hrow 2 (by decide)
  have hr3 : H 3 3 = 0 := hrow 3 (by decide)
  have hc1 : H 1 3 = 0 := (hs 1 3).trans hr1
  have hc2 : H 2 3 = 0 := (hs 2 3).trans hr2
  have hmul : H 3 0 * H.adjugate 0 3 = 1 := by
    have he := congrArg (fun A : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) => A 3 3)
      (Matrix.mul_adjugate H)
    change (∑ i : Fin 4, H 3 i * H.adjugate i 3) =
      (H.det • (1 : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K))) 3 3 at he
    rw [show H.det = 1 from hdet, one_smul, Matrix.one_apply_eq,
      Fin.sum_univ_four, hr1, hr2, hr3] at he
    simpa using he
  have hu : IsUnit (H 3 0) := isUnit_iff_dvd_one.mpr ⟨H.adjugate 0 3, hmul.symm⟩
  obtain ⟨a,ha,hA⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have ha0 : a ≠ 0 := ha.ne_zero
  have h03 : H 0 3 = MvPolynomial.C a := (hs 0 3).trans hA
  have hmatrix : H = !![H 0 0, H 0 1, H 0 2, MvPolynomial.C a;
      H 1 0, H 1 1, H 1 2, 0;
      H 2 0, H 2 1, H 2 2, 0;
      MvPolynomial.C a, 0, 0, 0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h03,hA,hr1,hr2,hr3,hc1,hc2]
  have hD : H.det = -(MvPolynomial.C a)^2 * (H 1 1 * H 2 2 - H 1 2 * H 2 1) := by
    calc
      H.det = (!![H 0 0, H 0 1, H 0 2, MvPolynomial.C a;
        H 1 0, H 1 1, H 1 2, 0;
        H 2 0, H 2 1, H 2 2, 0;
        MvPolynomial.C a, 0, 0, 0]).det := congrArg Matrix.det hmatrix
      _ = _ := by
        rw [Matrix.det_succ_row_zero]
        simp only [Fin.sum_univ_four]
        simp [Matrix.det_fin_three, Fin.succAbove]
        ring
  have hcross : H 1 1 * H 2 2 - H 1 2 * H 2 1 = MvPolynomial.C (-(a^2)⁻¹) := by
    have hne : (-(MvPolynomial.C a)^2 : MvPolynomial (Fin 4) K) ≠ 0 := by
      exact neg_ne_zero.mpr (pow_ne_zero _ (MvPolynomial.C_ne_zero.mpr ha0))
    apply mul_left_cancel₀ hne
    rw [← hD, show H.det = 1 from hdet]
    have he : -(a^2) * (-(a^2)⁻¹) = 1 := by
      field_simp [ha0]
    symm
    calc
      -(MvPolynomial.C a)^2 * MvPolynomial.C (-(a^2)⁻¹) =
          MvPolynomial.C (-(a^2) * (-(a^2)⁻¹)) := by simp only [map_mul, map_neg, map_pow]
      _ = 1 := by rw [he, map_one]
  have hlin (j k : Fin 4) (h : ∀ i, hessian P j i = if i = k then MvPolynomial.C a else 0) :
      ∃ b : K, pderiv j P = MvPolynomial.C a * X k + MvPolynomial.C b := by
    let r := pderiv j P - MvPolynomial.C a * X k
    have hr (i : Fin 4) : pderiv i r = 0 := by
      change pderiv i (pderiv j P - MvPolynomial.C a * X k) = 0
      rw [map_sub, MvPolynomial.pderiv_C_mul, ← hessian_apply, h i]
      by_cases hi : i = k
      · subst i
        simp
      · rw [if_neg hi, pderiv_X_of_ne (Ne.symm hi), mul_zero, sub_zero]
    have he := extremal_eq_C_of_all_pderiv_zero r hr
    refine ⟨coeff 0 r, ?_⟩
    change pderiv j P - MvPolynomial.C a * X k = _ at he
    linear_combination he
  obtain ⟨b,hb⟩ := hlin 3 0 (by
    intro i
    by_cases hi : i = 0
    · subst i
      rw [if_pos rfl]
      exact hA
    · rw [if_neg hi]
      exact hrow i hi)
  intro x y hxy
  have hbase : x 0 = y 0 := by
    have he := congrFun hxy 3
    change MvPolynomial.eval x (pderiv 3 P) = MvPolynomial.eval y (pderiv 3 P) at he
    rw [hb] at he
    simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at he
    exact mul_left_cancel₀ ha0 (add_right_cancel he)
  let E := splitRowSlice (x 0)
  let G : HC4.PlanarPolynomialMap K := ![E (pderiv 1 P), E (pderiv 2 P)]
  have hG : HC4.HasNonzeroConstantPlanarJacobian G := by
    refine ⟨-(a^2)⁻¹, by exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ ha0)), ?_⟩
    unfold HC4.planarJacobianDetPolynomial
    change pderiv 0 (E (pderiv 1 P)) * pderiv 1 (E (pderiv 2 P)) -
      pderiv 1 (E (pderiv 1 P)) * pderiv 0 (E (pderiv 2 P)) = _
    dsimp only [E]
    rw [splitRowSlice_pderiv_zero, splitRowSlice_pderiv_one,
      splitRowSlice_pderiv_one, splitRowSlice_pderiv_zero]
    change E (H 1 1) * E (H 2 2) - E (H 1 2) * E (H 2 1) = _
    rw [← map_mul, ← map_mul, ← map_sub, hcross]
    exact E.commutes _
  let px : Fin 2 → K := ![x 1,x 2]
  let py : Fin 2 → K := ![y 1,y 2]
  have heval (z : Fin 4 → K) (hz : z 0 = x 0) (i : Fin 4)
      (hi : pderiv 3 (pderiv i P) = 0) :
      MvPolynomial.eval (![z 1,z 2] : Fin 2 → K) (E (pderiv i P)) =
        MvPolynomial.eval z (pderiv i P) := by
    change MvPolynomial.eval _ (splitRowSlice (x 0) (pderiv i P)) = _
    rw [splitRowSlice_eval]
    apply extremal_eval_eq_of_pderiv_zero _ 3 hi
    intro j hj
    fin_cases j
    · change x 0 = z 0
      exact hz.symm
    · rfl
    · rfl
    · exact (hj rfl).elim
  have hpair : px = py := by
    apply hJC2 G hG
    funext i
    fin_cases i
    · change MvPolynomial.eval px (E (pderiv 1 P)) =
        MvPolynomial.eval py (E (pderiv 1 P))
      rw [heval x rfl 1 hc1, heval y hbase.symm 1 hc1]
      exact congrFun hxy 1
    · change MvPolynomial.eval px (E (pderiv 2 P)) =
        MvPolynomial.eval py (E (pderiv 2 P))
      rw [heval x rfl 2 hc2, heval y hbase.symm 2 hc2]
      exact congrFun hxy 2
  have hx1 : x 1 = y 1 := congrFun hpair 0
  have hx2 : x 2 = y 2 := congrFun hpair 1
  let R := pderiv 0 P - MvPolynomial.C a * X 3
  have hR : pderiv 3 R = 0 := by
    change pderiv 3 (pderiv 0 P - MvPolynomial.C a * X 3) = 0
    rw [map_sub, MvPolynomial.pderiv_C_mul, pderiv_X_self, mul_one]
    change H 0 3 - MvPolynomial.C a = 0
    rw [h03, sub_self]
  have hReq := extremal_eval_eq_of_pderiv_zero R 3 hR x y (by
    intro i hi
    fin_cases i
    · exact hbase
    · exact hx1
    · exact hx2
    · exact (hi rfl).elim)
  have he := congrFun hxy 0
  change MvPolynomial.eval x (pderiv 0 P) = MvPolynomial.eval y (pderiv 0 P) at he
  change MvPolynomial.eval x (pderiv 0 P - MvPolynomial.C a * X 3) =
    MvPolynomial.eval y (pderiv 0 P - MvPolynomial.C a * X 3) at hReq
  simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at hReq
  rw [he] at hReq
  have hprod : a * x 3 = a * y 3 := by linear_combination -hReq
  have hx3 : x 3 = y 3 := mul_left_cancel₀ ha0 hprod
  funext i
  fin_cases i <;> assumption

/-- The actual weight cap forces the split row, without needing
zero determinant clock. Standard coordinate placement. -/
theorem gradient_injective_of_oneZero_capCoordinate_standard
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (w : Fin 4 → ℤ) (hw : ∀ i, 0 ≤ w i)
    (m : ℤ) (h3 : w 3 = m) (hpos : ∀ i, i ≠ 0 → 0 < w i)
    (P : MvPolynomial (Fin 4) K) (hcap : IsWeightLE w m P)
    (hdet : hessianDeterminant P = 1) :
    Function.Injective (mvGradientMap P) := by
  apply gradient_injective_of_splitRow_standard hJC2 P hdet
  intro i hi
  exact eq_zero_of_nonnegativeWeight_negative_cap w hw _
    (by rw [h3]; have h := hpos i hi; omega) _ (hcap.hessian_entry 3 i)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_injective_of_splitRow_standard
#print axioms HC4.Polynomial.gradient_injective_of_oneZero_capCoordinate_standard
