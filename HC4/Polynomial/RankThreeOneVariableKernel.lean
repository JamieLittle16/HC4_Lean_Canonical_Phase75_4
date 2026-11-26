import HC4.Polynomial.RankThreeExtremalReduction
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# One-variable normalized kernel rigidity

In the remaining rank-three chart the kernel lies in a fixed
coordinate hyperplane. Suppose its normalized direction depends
only on the omitted coordinate. Third-derivative symmetry then
puts its derivative in the complementary Hessian kernel. A
regular two-by-two pivot and the constant normalization force
that derivative to vanish.

This eliminates genuinely one-variable kernel drift when the
complementary Hessian has rank two. Dependence on that one
coordinate is a hypothesis of this lemma, not asserted in general.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton RankThreeCubic
open nonZeroDivisors
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 4) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)

/-- Actual rational partials in the four-variable fraction field. -/
def rankThreePartial (i : Fin 4) : Derivation K (E K) (E K) :=
  localizationDerivation (nonZeroDivisors (B K)) (pderiv i)

theorem rankThreePartial_map (i : Fin 4) (q : B K) :
    rankThreePartial i (algebraMap (B K) (E K) q) =
      algebraMap (B K) (E K) (pderiv i q) :=
  localizationDerivation_algebraMap (nonZeroDivisors (B K)) _ _

set_option maxHeartbeats 3000000 in
/-- For a kernel direction whose non-distinguished partials vanish,
the distinguished derivative is annihilated by every other Hessian
row. This is a full-source third-derivative identity. -/
theorem rankThree_oneVariableKernel_derivative_rows
    (L : B K) (k : Fin 4) (V : Fin 4 → E K)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hconst : ∀ i, i ≠ k → ∀ j, rankThreePartial i (V j) = 0)
    (i : Fin 4) (hi : i ≠ k) :
    ∑ j : Fin 4, algebraMap (B K) (E K) (hessian L i j) *
      rankThreePartial k (V j) = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  have hrow (a : Fin 4) : (∑ j : Fin 4, H a j * V j) = 0 :=
    congrFun hV a
  have hmap (a : Fin 4) (q : B K) : rankThreePartial a (f q) = f (pderiv a q) :=
    rankThreePartial_map a q
  have hthird (j : Fin 4) : rankThreePartial k (H i j) =
      rankThreePartial i (H k j) := by
    change rankThreePartial k (f (pderiv j (pderiv i L))) =
      rankThreePartial i (f (pderiv j (pderiv k L)))
    rw [hmap,hmap,pderiv_comm_backport k j,pderiv_comm_backport i j,
      pderiv_comm_backport k i]
  have hdiff (a b : Fin 4) :
      (∑ j : Fin 4, H a j * rankThreePartial b (V j)) +
      (∑ j : Fin 4, V j * rankThreePartial b (H a j)) = 0 := by
    have h := congrArg (rankThreePartial (K := K) b) (hrow a)
    simpa only [map_sum,map_zero,Derivation.leibniz,smul_eq_mul,
      Finset.sum_add_distrib] using h
  have hz := hdiff k i
  simp only [hconst i hi,mul_zero,Finset.sum_const_zero,zero_add] at hz
  have he := hdiff i k
  simp only [hthird,hz,add_zero] at he
  exact he

set_option maxHeartbeats 3000000 in
/-- A normalized one-variable complementary kernel with regular
two-coordinate pivot is constant over the original ground field. -/
theorem rankThree_oneVariableKernel_constant
    (L : B K) (k l u v : Fin 4)
    (huk : u ≠ k) (hvk : v ≠ k) (huv : u ≠ v)
    (hcover : ∀ j : Fin 4, j = k ∨ j = l ∨ j = u ∨ j = v)
    (hreg : rankTwoPrincipalPivot (hessian L) u v ≠ 0)
    (V : Fin 4 → E K) (hVk : V k = 0) (hVl : V l = 1)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hconst : ∀ i, i ≠ k → ∀ j, rankThreePartial i (V j) = 0) :
    ∃ d : Fin 4 → K, d ≠ 0 ∧
      hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  let W : Fin 4 → E K := fun j => rankThreePartial k (V j)
  have hWk : W k = 0 := by change rankThreePartial k (V k) = 0; rw [hVk,map_zero]
  have hWl : W l = 0 := by
    change rankThreePartial k (V l) = 0
    rw [hVl,Derivation.map_one_eq_zero]
  have hWoff (j : Fin 4) (hju : j ≠ u) (hjv : j ≠ v) : W j = 0 := by
    rcases hcover j with h | h | h | h
    · rw [h,hWk]
    · rw [h,hWl]
    · exact (hju h).elim
    · exact (hjv h).elim
  have hrepr : W = (Pi.single u (W u) : Fin 4 → E K) + Pi.single v (W v) := by
    funext j
    by_cases hj : j = u
    · subst j
      simp [huv]
    · by_cases h' : j = v
      · subst j
        simp [hj]
      · simp [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne h',hWoff j hj h']
  have he (i : Fin 4) (hi : i ≠ k) : H i u * W u + H i v * W v = 0 := by
    have h := rankThree_oneVariableKernel_derivative_rows L k V hV hconst i hi
    change (H *ᵥ W) i = 0 at h
    have hw := congrArg (fun z : Fin 4 → E K => H *ᵥ z) hrepr
    change H *ᵥ W = H *ᵥ ((Pi.single u (W u) : Fin 4 → E K) + Pi.single v (W v)) at hw
    rw [Matrix.mulVec_add,Matrix.mulVec_single,Matrix.mulVec_single] at hw
    have hj := congrFun hw i
    change (H *ᵥ W) i = H i u * W u + H i v * W v at hj
    exact hj.symm.trans h
  have hΔ : rankTwoPrincipalPivot H u v ≠ 0 := by
    rw [← rankTwoPrincipalPivot_map]
    intro h
    apply hreg
    apply IsFractionRing.injective (B K) (E K)
    simpa only [map_zero] using h
  have hu : rankTwoPrincipalPivot H u v * W u = 0 := by
    unfold rankTwoPrincipalPivot
    linear_combination H v v * he u huk - H u v * he v hvk
  have hv : rankTwoPrincipalPivot H u v * W v = 0 := by
    unfold rankTwoPrincipalPivot
    linear_combination H u u * he v hvk - H v u * he u huk
  have hWu := (mul_eq_zero.mp hu).resolve_left hΔ
  have hWv := (mul_eq_zero.mp hv).resolve_left hΔ
  have hW : W = 0 := by rw [hrepr,hWu,hWv]; simp
  have hc (j : Fin 4) : ∃ d : K, V j = algebraMap K (E K) d := by
    apply rankOnePartial_constants
    intro i
    change rankThreePartial i (V j) = 0
    by_cases hi : i = k
    · subst i
      exact congrFun hW j
    · exact hconst i hi j
  choose d hd using hc
  refine ⟨d,?_,?_⟩
  · intro hz
    have hl := hd l
    rw [hVl,hz] at hl
    have hbad : (1 : E K) = 0 := by simpa using hl
    exact one_ne_zero hbad
  · funext i
    apply IsFractionRing.injective (B K) (E K)
    change f (∑ j : Fin 4, hessian L i j * MvPolynomial.C (d j)) = f 0
    simp only [map_sum,map_mul,map_zero]
    have hC (a : K) : f (MvPolynomial.C a) = algebraMap K (E K) a :=
      (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    simp only [hC,← hd]
    exact congrFun hV i

set_option maxHeartbeats 3000000 in
/-- The actual cofactor chart supplies a normalized rational kernel.
No complementary two-minor or one-variable hypothesis is needed. -/
theorem rankThree_normalizedKernel_exists
    (L : B K) (k l : Fin 4)
    (hdet : (hessian L).det = 0)
    (hcol : ∀ i, (hessian L).adjugate i k = 0)
    (hreg : (hessian L).adjugate l l ≠ 0) :
    ∃ V : Fin 4 → E K, V k = 0 ∧ V l = 1 ∧
      (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0 := by
  classical
  let A := hessian L
  let f := algebraMap (B K) (E K)
  let c := f (A.adjugate l l)
  have hc : c ≠ 0 := by
    intro hz
    apply hreg
    apply IsFractionRing.injective (B K) (E K)
    simpa only [map_zero] using hz
  have hs : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact pderiv_comm_backport _ _ _
  have hsa : A.adjugate.IsSymm := by
    change A.adjugate.transpose = A.adjugate
    rw [Matrix.adjugate_transpose, hs]
  let V : Fin 4 → E K := fun i => c⁻¹ * f (A.adjugate i l)
  refine ⟨V, ?_, ?_, ?_⟩
  · have hz : A.adjugate k l = 0 := (hsa.apply l k).trans (hcol l)
    change c⁻¹ * f (A.adjugate k l) = 0
    rw [hz, map_zero, mul_zero]
  · change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc
  · have hA : A * A.adjugate = 0 := by
      rw [Matrix.mul_adjugate, show A.det = 0 from hdet, zero_smul]
    funext i
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) (B K) => M i l) hA
    change (∑ j : Fin 4, A i j * A.adjugate j l) = 0 at hi
    have he := congrArg f hi
    simp only [map_sum, map_mul, map_zero] at he
    change (∑ j : Fin 4, f (A i j) * (c⁻¹ * f (A.adjugate j l))) = 0
    calc
      _ = c⁻¹ * (∑ j : Fin 4, f (A i j) * f (A.adjugate j l)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [he, mul_zero]

set_option maxHeartbeats 3000000 in
/-- All mixed kernel differentials obey Hessian reciprocity, without
any restriction on the variables of the normalized direction. -/
theorem rankThree_kernel_mixedDifferential
    (L : B K) (V : Fin 4 → E K)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (i k : Fin 4) :
    (∑ j : Fin 4, algebraMap (B K) (E K) (hessian L i j) *
      rankThreePartial k (V j)) =
    (∑ j : Fin 4, algebraMap (B K) (E K) (hessian L k j) *
      rankThreePartial i (V j)) := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  have hrow (a : Fin 4) : (∑ j : Fin 4, H a j * V j) = 0 :=
    congrFun hV a
  have hmap (a : Fin 4) (q : B K) : rankThreePartial a (f q) = f (pderiv a q) :=
    rankThreePartial_map a q
  have hthird (j : Fin 4) : rankThreePartial k (H i j) =
      rankThreePartial i (H k j) := by
    change rankThreePartial k (f (pderiv j (pderiv i L))) =
      rankThreePartial i (f (pderiv j (pderiv k L)))
    rw [hmap,hmap,pderiv_comm_backport k j,pderiv_comm_backport i j,
      pderiv_comm_backport k i]
  have hdiff (a b : Fin 4) :
      (∑ j : Fin 4, H a j * rankThreePartial b (V j)) +
      (∑ j : Fin 4, V j * rankThreePartial b (H a j)) = 0 := by
    have h := congrArg (rankThreePartial (K := K) b) (hrow a)
    simpa only [map_sum,map_zero,Derivation.leibniz,smul_eq_mul,
      Finset.sum_add_distrib] using h
  have hi := hdiff i k
  have hk := hdiff k i
  simp only [hthird] at hi
  exact add_right_cancel (hi.trans hk.symm)

set_option maxHeartbeats 3000000 in
/-- A normalized corank-one direction is straight, using the actual
surviving full principal cofactor to kill the acceleration. -/
theorem rankThree_normalizedKernel_lineGradient
    (L : B K) (l : Fin 4)
    (hreg : (hessian L).adjugate l l ≠ 0)
    (V : Fin 4 → E K) (hVl : V l = 1)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    ∀ i, lineEval (fun j => algebraMap (B K) (E K) (X j)) V (pderiv i L) =
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i L)) := by
  classical
  let f := algebraMap (B K) (E K)
  let z : Fin 4 → E K := fun i => f (X i)
  let H := (hessian L).map f
  let d : Fin 4 → Derivation K (E K) (E K) := fun i => rankThreePartial i
  have hd (i : Fin 4) (q : B K) : d i (f q) = f (pderiv i q) :=
    rankThreePartial_map i q
  have hregH : H.adjugate l l ≠ 0 := by
    intro hz
    apply hreg
    apply IsFractionRing.injective (B K) (E K)
    change (f.mapMatrix (hessian L)).adjugate l l = 0 at hz
    rw [← f.map_adjugate] at hz
    simpa only [map_zero] using hz
  have hker' (i : Fin 4) : ∑ j, H i j * V j = 0 := congrFun hV i
  have hs (i j : Fin 4) : H i j = H j i := by
    change f (pderiv j (pderiv i L)) = f (pderiv i (pderiv j L))
    rw [pderiv_comm_backport]
  have ht (i j a : Fin 4) : d a (H i j) = d i (H a j) := by
    change d a (f (pderiv j (pderiv i L))) = d i (f (pderiv j (pderiv a L)))
    rw [hd,hd,pderiv_comm_backport a j,pderiv_comm_backport i j,
      pderiv_comm_backport a i]
  let D : Derivation K (E K) (E K) := ∑ i, V i • d i
  have hD (x : E K) : D x = ∑ i, V i * d i x := by
    change Derivation.coeFnAddMonoidHom D x = _
    simp only [D,map_sum,Finset.sum_apply,Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply,smul_eq_mul]
  let W : Fin 4 → E K := fun i => D (V i)
  have hacc : H *ᵥ W = 0 := by
    funext i
    simp only [W,Matrix.mulVec,dotProduct,hD,Pi.zero_apply]
    exact hessianKernel_acceleration d H V hs ht hker' i
  have hWl : W l = 0 := by
    change D (V l) = 0
    rw [hVl, Derivation.map_one_eq_zero]
  have hW : W = 0 := by
    by_contra hn
    exact hregH (adjugate_entry_zero_of_nonzero_kernel_coordinate_zero H W hacc hn l l hWl)
  have hD0 (i : Fin 4) : D (V i) = 0 := congrFun hW i
  have hz (i : Fin 4) : D (z i) = V i := by
    simp only [z,hD,hd,pderiv_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hg (q : B K) : MvPolynomial.aeval z q = f q := by
    let g := IsScalarTower.toAlgHom K (B K) (E K)
    have he : MvPolynomial.aeval z = g := by
      apply MvPolynomial.algHom_ext
      intro i
      exact MvPolynomial.aeval_X _ i
    exact AlgHom.congr_fun he q
  intro i
  have hp : D (MvPolynomial.aeval z (pderiv i L)) = 0 := by
    rw [hg,hD]
    simp_rw [hd,mul_comm (V _)]
    exact hker' i
  simpa only [hg] using lineEval_eq_C_of_derivation_eq_zero D z V hz hD0 (pderiv i L) hp


/-- Jacobian of the actual normalized direction on the complement
of its unit coordinate. The base is still the four-variable field. -/
def rankThreeComplementJacobian (l : Fin 4) (V : Fin 4 → E K) :
    Matrix (Fin 3) (Fin 3) (E K) :=
  fun i j => rankThreePartial (l.succAbove j) (V (l.succAbove i))

set_option maxHeartbeats 4000000 in
/-- Differentiate the verified full-source affine gradient fibre
in the three complementary coordinates. -/
theorem rankThree_complement_transport
    (L : B K) (l : Fin 4) (V : Fin 4 → E K)
    (hVl : V l = 1)
    (hgrad : ∀ i, lineEval (fun j => algebraMap (B K) (E K) (X j)) V (pderiv i L) =
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i L))) :
    let H := (hessian L).submatrix l.succAbove l.succAbove
    let T := (lineEval (fun j => algebraMap (B K) (E K) (X j)) V).toRingHom.mapMatrix H
    let M := (algebraMap (B K) (E K)).mapMatrix H
    T * (1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rankThreeComplementJacobian l V).map _root_.Polynomial.C) =
        M.map _root_.Polynomial.C := by
  classical
  dsimp
  let f := algebraMap (B K) (E K)
  let z : Fin 4 → E K := fun i => f (X i)
  let d (j : Fin 3) : Derivation K (E K) (E K) := rankThreePartial (l.succAbove j)
  let w : Fin 4 → _root_.Polynomial (E K) := fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (V i) * _root_.Polynomial.X
  let J : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rankThreeComplementJacobian l V).map _root_.Polynomial.C
  have hE : (lineEval (K := K) z V : B K →ₐ[K] _root_.Polynomial (E K)) =
      MvPolynomial.aeval w := rfl
  have hz (j : Fin 3) (i : Fin 4) : d j (z i) = if i = l.succAbove j then 1 else 0 := by
    change rankThreePartial (l.succAbove j) (f (X i)) = _
    rw [rankThreePartial_map]
    by_cases h : i = l.succAbove j
    · subst i
      simp
    · simp [h, pderiv_X_of_ne h]
  have hc (j : Fin 3) : coeffDeriv (d j) (w l) = 0 := by
    simp [w, hz, hVl, Fin.succAbove_ne]
  have ht (j i : Fin 3) : coeffDeriv (d j) (w (l.succAbove i)) = J i j := by
    change coeffDeriv (d j)
      (_root_.Polynomial.C (z (l.succAbove i)) +
        _root_.Polynomial.C (V (l.succAbove i)) * _root_.Polynomial.X) = _
    simp only [map_add, coeffDeriv_C, Derivation.leibniz, smul_eq_mul, coeffDeriv_X,
      mul_zero, zero_add, hz, J, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, apply_ite _root_.Polynomial.C, map_one, map_zero,
      Fin.succAbove_right_injective.eq_iff]
    rfl
  have hsum (g : Fin 4 → _root_.Polynomial (E K)) (hg : g l = 0) :
      (∑ i : Fin 4, g i) = ∑ i : Fin 3, g (l.succAbove i) := by
    rw [Fin.sum_univ_succAbove g l, hg, zero_add]
  apply Matrix.ext
  intro i j
  have e := congrArg (coeffDeriv (d j)) (hgrad (l.succAbove i))
  change coeffDeriv (d j) (lineEval z V (pderiv (l.succAbove i) L)) =
    coeffDeriv (d j) (_root_.Polynomial.C (f (pderiv (l.succAbove i) L))) at e
  rw [coeffDeriv_C, show d j (f (pderiv (l.succAbove i) L)) =
    f (pderiv (l.succAbove j) (pderiv (l.succAbove i) L)) from rankThreePartial_map _ _,
    hE, derivation_aeval] at e
  have hsplit :
      (∑ a : Fin 4, MvPolynomial.aeval w (pderiv a (pderiv (l.succAbove i) L)) *
        coeffDeriv (d j) (w a)) =
      ∑ a : Fin 3, MvPolynomial.aeval w (pderiv (l.succAbove a) (pderiv (l.succAbove i) L)) *
        coeffDeriv (d j) (w (l.succAbove a)) := by
    exact hsum (fun a : Fin 4 => MvPolynomial.aeval w (pderiv a (pderiv (l.succAbove i) L)) *
      coeffDeriv (d j) (w a)) (by
        change MvPolynomial.aeval w (pderiv l (pderiv (l.succAbove i) L)) *
          coeffDeriv (d j) (w l) = 0
        rw [hc j, mul_zero])
  rw [hsplit] at e
  simp only [ht] at e
  simpa only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.submatrix_apply, hessian_apply, hE, J] using e

set_option maxHeartbeats 4000000 in
/-- The actual complement pencil has determinant one. Its
constant coefficient is the identity and its product with the
transported Hessian has nonzero constant determinant. -/
theorem rankThree_complement_det_one
    (L : B K) (l : Fin 4) (V : Fin 4 → E K)
    (hVl : V l = 1) (hreg : (hessian L).adjugate l l ≠ 0)
    (hgrad : ∀ i, lineEval (fun j => algebraMap (B K) (E K) (X j)) V (pderiv i L) =
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i L))) :
    (1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rankThreeComplementJacobian l V).map _root_.Polynomial.C).det = 1 := by
  classical
  let f := algebraMap (B K) (E K)
  let J : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rankThreeComplementJacobian l V).map _root_.Polynomial.C
  let H := (hessian L).submatrix l.succAbove l.succAbove
  let T := (lineEval (fun j => f (X j)) V).toRingHom.mapMatrix H
  let M := f.mapMatrix H
  have hH : H.det ≠ 0 := by
    intro hz
    apply hreg
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, show
      ((hessian L).submatrix l.succAbove l.succAbove).det = 0 from hz, mul_zero]
  have hM : f H.det ≠ 0 := by
    intro hz
    apply hH
    apply IsFractionRing.injective (B K) (E K)
    simpa only [map_zero] using hz
  have h := rankThree_complement_transport L l V hVl hgrad
  change T * J = M.map _root_.Polynomial.C at h
  have hh : T.det * J.det = _root_.Polynomial.C (f H.det) := by
    rw [← Matrix.det_mul, h]
    exact (_root_.Polynomial.C.map_det M).symm.trans
      (congrArg _root_.Polynomial.C (f.map_det H).symm)
  have hz : J.det.coeff 0 = 1 := by
    let e := _root_.Polynomial.constantCoeff (R := E K)
    have he : e.mapMatrix J = 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [e, J, Matrix.one_apply, hij, Matrix.smul_apply, RingHom.mapMatrix_apply]
    change e J.det = 1
    rw [e.map_det, he, Matrix.det_one]
  exact polynomial_factor_eq_one hM hh hz

/-- Nilpotence of the full complementary differential is a
consequence of actual polynomial transport, not an imposed
hypothesis on the rational direction. -/
theorem rankThree_complement_cube_zero
    (L : B K) (l : Fin 4) (V : Fin 4 → E K)
    (hVl : V l = 1) (hreg : (hessian L).adjugate l l ≠ 0)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    rankThreeComplementJacobian l V ^ 3 = 0 := by
  simpa using matrix_pow_card_eq_zero_of_det_linear_eq_one
    (rankThreeComplementJacobian l V)
    (rankThree_complement_det_one L l V hVl hreg
      (rankThree_normalizedKernel_lineGradient L l hreg V hVl hV))


/-- The fixed zero component gives an actual zero row in the
complementary velocity differential. -/
theorem rankThree_complement_zeroRow
    (l : Fin 4) (V : Fin 4 → E K) (a : Fin 3)
    (ha : V (l.succAbove a) = 0) :
    ∀ j, rankThreeComplementJacobian l V a j = 0 := by
  intro j
  change rankThreePartial (l.succAbove j) (V (l.succAbove a)) = 0
  rw [ha, map_zero]

/-- The complementary Hessian is an exact symmetrizer of the
velocity differential. Removing the normalized coordinate in
the mixed differential identity contributes zero. -/
theorem rankThree_complement_selfAdjoint
    (L : B K) (l : Fin 4) (V : Fin 4 → E K)
    (hVl : V l = 1)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    let B₀ := ((hessian L).submatrix l.succAbove l.succAbove).map
      (algebraMap (B K) (E K))
    let J := rankThreeComplementJacobian l V
    B₀ * J = J.transpose * B₀ := by
  classical
  dsimp
  apply Matrix.ext
  intro i j
  have h := rankThree_kernel_mixedDifferential L V hV
    (l.succAbove i) (l.succAbove j)
  have hz (a : Fin 4) : rankThreePartial a (V l) = 0 := by
    rw [hVl, Derivation.map_one_eq_zero]
  rw [Fin.sum_univ_succAbove _ l, Fin.sum_univ_succAbove _ l,
    hz, hz, mul_zero, mul_zero, zero_add, zero_add] at h
  change (∑ a : Fin 3, algebraMap (B K) (E K) (hessian L (l.succAbove i) (l.succAbove a)) *
      rankThreePartial (l.succAbove j) (V (l.succAbove a))) =
    ∑ a : Fin 3, rankThreePartial (l.succAbove i) (V (l.succAbove a)) *
      algebraMap (B K) (E K) (hessian L (l.succAbove a) (l.succAbove j))
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]
  have hs : hessian L (l.succAbove j) (l.succAbove a) =
      hessian L (l.succAbove a) (l.succAbove j) :=
    pderiv_comm_backport _ _ _
  rw [hs]


set_option maxHeartbeats 3000000 in
/-- The normalized kernel's derivative along itself vanishes in
the original four-variable fraction field. -/
theorem rankThree_normalizedKernel_acceleration_zero
    (L : B K) (l : Fin 4)
    (hreg : (hessian L).adjugate l l ≠ 0)
    (V : Fin 4 → E K) (hVl : V l = 1)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    ∀ i, (∑ j : Fin 4, V j * rankThreePartial j (V i)) = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let z : Fin 4 → E K := fun i => f (X i)
  let H := (hessian L).map f
  let d : Fin 4 → Derivation K (E K) (E K) := fun i => rankThreePartial i
  have hd (i : Fin 4) (q : B K) : d i (f q) = f (pderiv i q) :=
    rankThreePartial_map i q
  have hregH : H.adjugate l l ≠ 0 := by
    intro hz
    apply hreg
    apply IsFractionRing.injective (B K) (E K)
    change (f.mapMatrix (hessian L)).adjugate l l = 0 at hz
    rw [← f.map_adjugate] at hz
    simpa only [map_zero] using hz
  have hker' (i : Fin 4) : ∑ j, H i j * V j = 0 := congrFun hV i
  have hs (i j : Fin 4) : H i j = H j i := by
    change f (pderiv j (pderiv i L)) = f (pderiv i (pderiv j L))
    rw [pderiv_comm_backport]
  have ht (i j a : Fin 4) : d a (H i j) = d i (H a j) := by
    change d a (f (pderiv j (pderiv i L))) = d i (f (pderiv j (pderiv a L)))
    rw [hd,hd,pderiv_comm_backport a j,pderiv_comm_backport i j,
      pderiv_comm_backport a i]
  let D : Derivation K (E K) (E K) := ∑ i, V i • d i
  have hD (x : E K) : D x = ∑ i, V i * d i x := by
    change Derivation.coeFnAddMonoidHom D x = _
    simp only [D,map_sum,Finset.sum_apply,Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply,smul_eq_mul]
  let W : Fin 4 → E K := fun i => D (V i)
  have hacc : H *ᵥ W = 0 := by
    funext i
    simp only [W,Matrix.mulVec,dotProduct,hD,Pi.zero_apply]
    exact hessianKernel_acceleration d H V hs ht hker' i
  have hWl : W l = 0 := by
    change D (V l) = 0
    rw [hVl, Derivation.map_one_eq_zero]
  have hW : W = 0 := by
    by_contra hn
    exact hregH (adjugate_entry_zero_of_nonzero_kernel_coordinate_zero H W hacc hn l l hWl)
  have hD0 (i : Fin 4) : D (V i) = 0 := congrFun hW i
  intro i
  exact (hD (V i)).symm.trans (hD0 i)

set_option maxHeartbeats 3000000 in
/-- Zero complementary differential closes the actual extremal
chart, without assuming a separate regular two-minor. -/
theorem globalWeightOptimum_rankThree_complementJacobian_ne_zero
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (l : Fin 4) (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (V : Fin 4 → E K) (hVl : V l = 1)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    rankThreeComplementJacobian l V ≠ 0 := by
  classical
  intro hJ
  let L := initialForm w m P
  have hother (i j : Fin 4) (hi : i ≠ l) : rankThreePartial i (V j) = 0 := by
    by_cases hj : j = l
    · rw [hj, hVl, Derivation.map_one_eq_zero]
    · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hi
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hj
      have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) (E K) => M b a) hJ
      change rankThreePartial (l.succAbove a) (V (l.succAbove b)) = 0 at he
      rwa [ha, hb] at he
  have hall (i j : Fin 4) : rankThreePartial i (V j) = 0 := by
    by_cases hi : i = l
    · subst i
      have he := rankThree_normalizedKernel_acceleration_zero L l hreg V hVl hV j
      rw [Finset.sum_eq_single l] at he
      · rwa [hVl, one_mul] at he
      · intro a _ ha
        rw [hother a j ha, mul_zero]
      · simp
    · exact hother i j hi
  have hc (j : Fin 4) : ∃ d : K, V j = algebraMap K (E K) d := by
    apply rankOnePartial_constants
    intro i
    exact hall i j
  choose d hd using hc
  have hd0 : d ≠ 0 := by
    intro hz
    have hl := hd l
    rw [hVl, hz] at hl
    have hbad : (1 : E K) = 0 := by simpa using hl
    exact one_ne_zero hbad
  have hpoly : hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
    funext i
    let f := algebraMap (B K) (E K)
    apply IsFractionRing.injective (B K) (E K)
    change f (∑ j : Fin 4, hessian L i j * MvPolynomial.C (d j)) = f 0
    simp only [map_sum, map_mul, map_zero]
    have hC (a : K) : f (MvPolynomial.C a) = algebraMap K (E K) a :=
      (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    simp only [hC, ← hd]
    exact congrFun hV i
  exact hd0 (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap
    hclock hopt hdet d hpoly)

section Matrix
variable {F : Type*} [Field F]

set_option maxHeartbeats 3000000 in
/-- A regular symmetrizer of a rank-two nilpotent with a fixed zero
row has zero principal cofactor at that row. In particular the
actual active two-coordinate Hessian is singular. -/
theorem rankThree_zeroRow_rankTwo_principalCofactor_zero
    (H N : Matrix (Fin 3) (Fin 3) F) (a : Fin 3)
    (hreg : H.det ≠ 0) (hself : N.transpose * H = H * N)
    (h3 : N ^ 3 = 0) (ha : ∀ j, N a j = 0)
    (hm : ∃ i j p q : Fin 3, N i p * N j q ≠ N i q * N j p) :
    H.adjugate a a = 0 := by
  classical
  obtain ⟨hr, hs, _, hl, _⟩ := rankTwo_square_frontier N h3 hm
  have he : ∃ i j : Fin 3, (N * N) i j ≠ 0 := by
    by_contra hn
    apply hs
    apply Matrix.ext
    intro i j
    by_contra hz
    exact hn ⟨i,j,hz⟩
  obtain ⟨i,j,hij⟩ := he
  let v : Fin 3 → F := fun b => (N * N) b j
  have hv : v ≠ 0 := by
    intro hz
    exact hij (congrFun hz i)
  have hNv : N *ᵥ v = 0 := by
    funext b
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M b j) hl
  have hva : v a = 0 := by
    change (∑ b : Fin 3, N a b * N b j) = 0
    simp [ha]
  let e : Fin 3 → F := Pi.single a 1
  have heN : e ᵥ* N = 0 := by
    funext b
    change (∑ k : Fin 3, (Pi.single a (1 : F) : Fin 3 → F) k * N k b) = 0
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  let z := H *ᵥ v
  obtain ⟨hz, hzN⟩ := rankTwo_hessian_leftNormal H N hreg hself v hv hNv
  have hp (b : Fin 3) : z b = z a * e b := by
    have hh := rankTwo_leftKernel_minors_zero N hr z e hzN heN b a
    have hea : e a = 1 := by simp [e]
    rw [hea, mul_one] at hh
    exact hh
  have hza : z a ≠ 0 := by
    intro h
    apply hz
    funext b
    change z b = 0
    rw [hp b, h, zero_mul]
  have hrepr : z = (Pi.single a (z a) : Fin 3 → F) := by
    funext b
    rw [hp b]
    by_cases hb : b = a
    · subst b
      simp [e]
    · simp [e, Pi.single_eq_of_ne hb]
  have hh : H.adjugate *ᵥ z = H.det • v := by
    change H.adjugate *ᵥ (H *ᵥ v) = H.det • v
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [hrepr, Matrix.mulVec_single] at hh
  have ha' := congrFun hh a
  change H.adjugate a a * z a = H.det * v a at ha'
  rw [hva, mul_zero] at ha'
  exact (mul_eq_zero.mp ha').resolve_right hza

end Matrix


section ActiveBlock

variable {F : Type*} [Field F]

/-- A singular symmetric active block together with the actual
normalized kernel makes all three non-omitted Hessian rows
proportional after restricting to the non-omitted columns.

This is a partial Hessian assertion, not a claim that the full
four-variable Hessian has rank at most one. -/
theorem rankThree_activeMinor_zero_all_restrictedMinors
    (H : Matrix (Fin 4) (Fin 4) F) (hs : ∀ i j, H i j = H j i)
    (k l u v : Fin 4) (hkl : k ≠ l)
    (hcover : ∀ i, i = k ∨ i = l ∨ i = u ∨ i = v)
    (V : Fin 4 → F) (hVk : V k = 0) (hVl : V l = 1)
    (hV : H *ᵥ V = 0)
    (hku : k ≠ u) (hkv : k ≠ v) (hlu : l ≠ u) (hlv : l ≠ v) (huv : u ≠ v)
    (hminor : rankTwoPrincipalPivot H u v = 0) :
    ∀ i j p q : Fin 4, i ≠ k → j ≠ k → p ≠ k → q ≠ k →
      H i p * H j q = H i q * H j p := by
  classical
  have hrepr : V = (Pi.single l (1 : F) : Fin 4 → F) +
      Pi.single u (V u) + Pi.single v (V v) := by
    funext i
    rcases hcover i with h | h | h | h
    · subst i
      simp [hVk, hkl, hku, hkv]
    · subst i
      simp [hVl, hlu, hlv]
    · subst i
      simp [Ne.symm hlu, huv]
    · subst i
      simp [Ne.symm hlv, Ne.symm huv]
  have hcol (i : Fin 4) : H i l = -(H i u * V u + H i v * V v) := by
    have he := congrArg (fun x : Fin 4 → F => H *ᵥ x) hrepr
    change H *ᵥ V = H *ᵥ ((Pi.single l (1 : F) : Fin 4 → F) +
      Pi.single u (V u) + Pi.single v (V v)) at he
    rw [hV, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_single,
      Matrix.mulVec_single, Matrix.mulVec_single] at he
    have hh := congrFun he i
    change 0 = H i l * 1 + H i u * V u + H i v * V v at hh
    linear_combination -hh
  have hrow (i : Fin 4) : H l i = -(H u i * V u + H v i * V v) := by
    rw [hs l i, hcol i, hs i u, hs i v]
  have hbase (i j : Fin 4) (hi : i ≠ k) (hj : j ≠ k) :
      H i u * H j v = H i v * H j u := by
    rcases hcover i with he | he | he | he
    · exact (hi he).elim
    · subst i
      rcases hcover j with he | he | he | he
      · exact (hj he).elim
      · subst j
        ring
      · subst j
        rw [hrow u, hrow v]
        unfold rankTwoPrincipalPivot at hminor
        linear_combination V v * hminor
      · subst j
        rw [hrow u, hrow v]
        unfold rankTwoPrincipalPivot at hminor
        linear_combination -V u * hminor
    · subst i
      rcases hcover j with he | he | he | he
      · exact (hj he).elim
      · subst j
        rw [hrow u, hrow v]
        unfold rankTwoPrincipalPivot at hminor
        linear_combination -V v * hminor
      · subst j
        ring
      · subst j
        exact sub_eq_zero.mp hminor
    · subst i
      rcases hcover j with he | he | he | he
      · exact (hj he).elim
      · subst j
        rw [hrow u, hrow v]
        unfold rankTwoPrincipalPivot at hminor
        linear_combination V u * hminor
      · subst j
        unfold rankTwoPrincipalPivot at hminor
        linear_combination -hminor
      · subst j
        ring
  intro i j p q hi hj hp hq
  have h := hbase i j hi hj
  rcases hcover p with he | he | he | he
  · exact (hp he).elim
  · subst p
    rcases hcover q with he | he | he | he
    · exact (hq he).elim
    · subst q
      ring
    · subst q
      rw [hcol i, hcol j]
      linear_combination V v * h
    · subst q
      rw [hcol i, hcol j]
      linear_combination -V u * h
  · subst p
    rcases hcover q with he | he | he | he
    · exact (hq he).elim
    · subst q
      rw [hcol i, hcol j]
      linear_combination -V v * h
    · subst q
      ring
    · subst q
      exact h
  · subst p
    rcases hcover q with he | he | he | he
    · exact (hq he).elim
    · subst q
      rw [hcol i, hcol j]
      linear_combination V u * h
    · subst q
      linear_combination -h
    · subst q
      ring

end ActiveBlock

set_option maxHeartbeats 4000000 in
/-- Rank-two velocity drift implies that the actual polynomial
Hessian restricted to the three non-omitted variables has every
two-by-two minor zero. The conclusion descends to the polynomial
ring, without adjoining parameters or changing the source. -/
theorem rankThree_rankTwoVelocity_restrictedMinors_zero
    (L : B K) (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian L).adjugate l l ≠ 0)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hm : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p) :
    ∀ i j p q : Fin 4, i ≠ l.succAbove a → j ≠ l.succAbove a →
      p ≠ l.succAbove a → q ≠ l.succAbove a →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  let B₀ := H.submatrix l.succAbove l.succAbove
  let J := rankThreeComplementJacobian l V
  let k := l.succAbove a
  let u := l.succAbove (a.succAbove 0)
  let v := l.succAbove (a.succAbove 1)
  have hB : B₀.det ≠ 0 := by
    intro hz
    apply hreg
    have he : f ((hessian L).submatrix l.succAbove l.succAbove).det = 0 := by
      rw [RingHom.map_det]
      exact hz
    have hd : ((hessian L).submatrix l.succAbove l.succAbove).det = 0 :=
      IsFractionRing.injective (B K) (E K) (he.trans (map_zero f).symm)
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hd, mul_zero]
  have hself : J.transpose * B₀ = B₀ * J :=
    (rankThree_complement_selfAdjoint L l V hVl hV).symm
  have h3 : J ^ 3 = 0 := rankThree_complement_cube_zero L l V hVl hreg hV
  have ha : ∀ j, J a j = 0 := rankThree_complement_zeroRow l V a hVk
  have hc := rankThree_zeroRow_rankTwo_principalCofactor_zero B₀ J a hB hself h3 ha hm
  have hminor : rankTwoPrincipalPivot H u v = 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hc
    have hz : (B₀.submatrix a.succAbove a.succAbove).det = 0 :=
      (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    rw [Matrix.det_fin_two] at hz
    exact hz
  have hs (i j : Fin 4) : H i j = H j i :=
    congrArg f (pderiv_comm_backport j i L)
  have hkl : k ≠ l := Fin.succAbove_ne l a
  have hku : k ≠ u := by
    intro he
    exact (Fin.succAbove_ne a 0) (Fin.succAbove_right_injective he).symm
  have hkv : k ≠ v := by
    intro he
    exact (Fin.succAbove_ne a 1) (Fin.succAbove_right_injective he).symm
  have hlu : l ≠ u := Ne.symm (Fin.succAbove_ne l _)
  have hlv : l ≠ v := Ne.symm (Fin.succAbove_ne l _)
  have huv : u ≠ v := by
    intro he
    have hz : (0 : Fin 2) = 1 :=
      Fin.succAbove_right_injective (Fin.succAbove_right_injective he)
    exact (by decide : (0 : Fin 2) ≠ 1) hz
  have hcover (i : Fin 4) : i = k ∨ i = l ∨ i = u ∨ i = v := by
    by_cases hi : i = l
    · exact Or.inr (Or.inl hi)
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hi
    by_cases hba : b = a
    · left
      rw [← hb,hba]
    obtain ⟨c,hc⟩ := Fin.exists_succAbove_eq hba
    have he : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    rcases he with he | he
    · right; right; left
      rw [← hb,← hc,he]
    · right; right; right
      rw [← hb,← hc,he]
  intro i j p q hi hj hp hq
  have he := rankThree_activeMinor_zero_all_restrictedMinors H hs k l u v hkl
    hcover V hVk hVl hV hku hkv hlu hlv huv hminor i j p q hi hj hp hq
  apply IsFractionRing.injective (B K) (E K)
  change f (hessian L i p * hessian L j q) = f (hessian L i q * hessian L j p)
  simp only [map_mul]
  exact he


set_option maxHeartbeats 4000000 in
/-- In the actual rank-two velocity branch, each surviving
restricted Hessian ratio has reduced numerator and denominator
depending only on the omitted coordinate. This conclusion is
in the original polynomial ring. -/
theorem rankThree_rankTwoVelocity_ratio_num_den_independent
    (L : B K) (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian L).adjugate l l ≠ 0)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hm : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p)
    (p i : Fin 4) (hp : p ≠ l.succAbove a) (hi : i ≠ l.succAbove a)
    (hip : i ≠ p) (hdiag : hessian L p p ≠ 0) :
    let f := algebraMap (B K) (E K)
    let r := f (hessian L i p) / f (hessian L p p)
    ∀ j : Fin 4, j ≠ l.succAbove a →
      pderiv j (IsFractionRing.num (B K) r) = 0 ∧
      pderiv j (IsFractionRing.den (B K) r : B K) = 0 := by
  classical
  dsimp
  have hmin := rankThree_rankTwoVelocity_restrictedMinors_zero L l a V hVl hVk hreg hV hm
  have hrow (j : Fin 4) (hj : j ≠ l.succAbove a) :
      hessian L p p * hessian L i j = hessian L i p * hessian L p j :=
    (hmin p i p j hp hi hp hj).trans (mul_comm _ _)
  exact rankOnePartial_num_den_independent _ (l.succAbove a)
    (rankOneHessian_twoRows_partialRatios_constant L (l.succAbove a) p i
      hip hp hi hdiag hrow)


set_option maxHeartbeats 4000000 in
/-- Exact weighted classification of nonzero restricted ratios in
the rank-two velocity branch. If the omitted coordinate has zero
weight, the two active coordinate weights coincide. Otherwise the
entry ratio is a Laurent monomial in the omitted coordinate. -/
theorem rankThree_rankTwoVelocity_weightedRatio
    (L : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ j, 0 ≤ w j)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian L).adjugate l l ≠ 0)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hm : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p)
    (p i : Fin 4) (hp : p ≠ l.succAbove a) (hi : i ≠ l.succAbove a)
    (hip : i ≠ p) (hdiag : hessian L p p ≠ 0) (hmix : hessian L i p ≠ 0) :
    (w (l.succAbove a) = 0 ∧ w i = w p) ∨
      (0 < w (l.succAbove a) ∧
        ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧ e ≠ 0 ∧
          w p - w i = ((t : ℤ) - (n : ℤ)) * w (l.succAbove a) ∧
          hessian L i p * MvPolynomial.monomial (Finsupp.single (l.succAbove a) n) c =
            hessian L p p * MvPolynomial.monomial (Finsupp.single (l.succAbove a) t) e) := by
  classical
  let s := l.succAbove a
  let f := algebraMap (B K) (E K)
  let A := hessian L p p
  let C₀ := hessian L i p
  let r := f C₀ / f A
  let P := IsFractionRing.num (B K) r
  let Q : B K := IsFractionRing.den (B K) r
  have hQ0 : Q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) r)
  have hAf : f A ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hdiag
  have hQf : f Q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hQ0
  have hrepr : f P / f Q = f C₀ / f A :=
    IsFractionRing.mk'_num_den' (B K) r
  have hcross : C₀ * Q = A * P := by
    apply IsFractionRing.injective (B K) (E K)
    change f (C₀*Q) = f (A*P)
    simp only [map_mul]
    rw [mul_comm (f A)]
    exact ((div_eq_div_iff hQf hAf).mp hrepr).symm
  have hder (j : Fin 4) (hj : j ≠ s) : pderiv j P = 0 ∧ pderiv j Q = 0 :=
    rankThree_rankTwoVelocity_ratio_num_den_independent L l a V hVl hVk hreg hV hm
      p i hp hi hip hdiag j hj
  have hA : MvPolynomial.IsWeightedHomogeneous w A (m-w p-w p) :=
    pderiv_isWeightedHomogeneous (pderiv_isWeightedHomogeneous hL p) p
  have hC : MvPolynomial.IsWeightedHomogeneous w C₀ (m-w i-w p) :=
    pderiv_isWeightedHomogeneous (pderiv_isWeightedHomogeneous hL i) p
  by_cases hz : w s = 0
  · have he := rankOne_weighted_relativeRatio_zeroWeight w s hz _ _ A C₀
      hmix hA hC P Q hQ0 hcross
      (fun j hj => (hder j hj).1) (fun j hj => (hder j hj).2)
    exact Or.inl ⟨hz, by omega⟩
  · have hpos : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm hz)
    obtain ⟨n,t,c,e,hc,he,hwt,hpow⟩ :=
      rankOne_weighted_relativeRatio_cross_power w s hpos _ _ A C₀
        hdiag hmix hA hC P Q hQ0 hcross
        (fun j hj => (hder j hj).1) (fun j hj => (hder j hj).2)
    refine Or.inr ⟨hpos,n,t,c,e,hc,he,?_,hpow⟩
    change w p - w i = ((t : ℤ) - (n : ℤ)) * w s
    rw [sub_mul]
    omega


set_option maxHeartbeats 5000000 in
/-- Transfer a supported second derivative coefficient to the
pivot row. The monomial factors involve only the omitted coordinate,
so the transfer preserves every new weight with zero omitted weight
and increases the pivot exponent by one in the original potential. -/
theorem rankThree_support_transfer_to_pivot
    (L : B K) (s p i j : Fin 4) (hps : p ≠ s) (hip : i ≠ p)
    (v : Fin 4 → ℤ) (hvs : v s = 0)
    (u : Fin 4 →₀ ℕ) (hu : coeff u L ≠ 0) (hui : u i ≠ 0)
    (huj : (u - Finsupp.single i 1 : Fin 4 →₀ ℕ) j ≠ 0)
    (n t : ℕ) (c e : K) (hc : c ≠ 0)
    (hcross : hessian L i j * MvPolynomial.monomial (Finsupp.single s n) c =
      hessian L p j * MvPolynomial.monomial (Finsupp.single s t) e) :
    ∃ z : Fin 4 →₀ ℕ, coeff z L ≠ 0 ∧ z p = u p + 1 ∧
      Finsupp.weight v z = Finsupp.weight v u - v i + v p := by
  classical
  let a : Fin 4 →₀ ℕ := u - Finsupp.single i 1
  let b : Fin 4 →₀ ℕ := a - Finsupp.single j 1
  have ha : coeff a (pderiv i L) ≠ 0 :=
    extremal_pderiv_coeff_nonzero L u hu i hui
  have hb : coeff b (hessian L i j) ≠ 0 :=
    extremal_pderiv_coeff_nonzero (pderiv i L) a ha j huj
  let q : Fin 4 →₀ ℕ := b + Finsupp.single s n
  have hq : coeff q (hessian L p j * MvPolynomial.monomial (Finsupp.single s t) e) ≠ 0 := by
    rw [← hcross]
    change coeff (b + Finsupp.single s n)
      (hessian L i j * MvPolynomial.monomial (Finsupp.single s n) c) ≠ 0
    rw [MvPolynomial.coeff_mul_monomial]
    exact mul_ne_zero hb hc
  rw [MvPolynomial.coeff_mul_monomial'] at hq
  have hle : Finsupp.single s t ≤ q := by
    by_contra hn
    rw [if_neg hn] at hq
    exact hq rfl
  rw [if_pos hle] at hq
  let b' : Fin 4 →₀ ℕ := q - Finsupp.single s t
  have hb' : coeff b' (hessian L p j) ≠ 0 := (mul_ne_zero_iff.mp hq).1
  let a' : Fin 4 →₀ ℕ := b' + Finsupp.single j 1
  let z : Fin 4 →₀ ℕ := a' + Finsupp.single p 1
  have ha' : coeff a' (pderiv p L) ≠ 0 := by
    change coeff b' (pderiv j (pderiv p L)) ≠ 0 at hb'
    rw [coeff_pderiv_backport] at hb'
    exact (mul_ne_zero_iff.mp hb').1
  have hz : coeff z L ≠ 0 := by
    rw [coeff_pderiv_backport] at ha'
    exact (mul_ne_zero_iff.mp ha').1
  have hau : a + Finsupp.single i 1 = u :=
    Finsupp.sub_add_single_one_cancel hui
  have hba : b + Finsupp.single j 1 = a :=
    Finsupp.sub_add_single_one_cancel huj
  have hbb : b' + Finsupp.single s t = b + Finsupp.single s n :=
    tsub_add_cancel_of_le hle
  have hpa : a p = u p := by
    have he := congrArg (fun x : Fin 4 →₀ ℕ => x p) hau
    change (a + Finsupp.single i 1 : Fin 4 →₀ ℕ) p = u p at he
    simpa only [Finsupp.add_apply, Finsupp.single_apply, if_neg hip, add_zero] using he
  have hpb : b p + (Finsupp.single j (1 : ℕ)) p = a p := by
    have he := congrArg (fun x : Fin 4 →₀ ℕ => x p) hba
    change (b + Finsupp.single j 1 : Fin 4 →₀ ℕ) p = a p at he
    simpa only [Finsupp.add_apply] using he
  have hpc : b' p = b p := by
    have he := congrArg (fun x : Fin 4 →₀ ℕ => x p) hbb
    change (b' + Finsupp.single s t : Fin 4 →₀ ℕ) p =
      (b + Finsupp.single s n : Fin 4 →₀ ℕ) p at he
    simpa only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hps), add_zero] using he
  have hwp := congrArg (Finsupp.weight v) hau
  have hwq := congrArg (Finsupp.weight v) hba
  have hwr := congrArg (Finsupp.weight v) hbb
  simp only [map_add, Finsupp.weight_single, one_smul, hvs,
    smul_zero, add_zero] at hwp hwq hwr
  refine ⟨z,hz,?_,?_⟩
  · change (b' + Finsupp.single j 1 + Finsupp.single p 1 : Fin 4 →₀ ℕ) p = u p + 1
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, hpc, hpb, hpa]
  · change Finsupp.weight v (b' + Finsupp.single j 1 + Finsupp.single p 1) = _
    simp only [map_add, Finsupp.weight_single, one_smul]
    omega

set_option maxHeartbeats 5000000 in
/-- A restricted rank-one chart admits a new cap after collapsing
the omitted weight to zero and assigning the active coordinates the
pivot weight. This is a coefficient argument on the actual leading
polynomial, not a nonlinear change of the source. -/
theorem rankThree_support_cap_of_monomial_rows
    (L : B K) (w v : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ j, 0 ≤ w j) (hL : IsWeightLE w m L)
    (s p : Fin 4) (hps : p ≠ s) (hvs : v s = 0)
    (hvp : v p = w p) (hv : ∀ i, v i ≤ m)
    (hrows : ∀ i j : Fin 4, i ≠ s → i ≠ p → j ≠ s →
      hessian L i j ≠ 0 →
      v i ≤ v p ∧ ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧
        hessian L i j * MvPolynomial.monomial (Finsupp.single s n) c =
          hessian L p j * MvPolynomial.monomial (Finsupp.single s t) e) :
    IsWeightLE v m L := by
  classical
  intro u hu
  by_contra hn
  let T := L.support.filter (fun x => m < Finsupp.weight v x)
  have hT : T.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hu, lt_of_not_ge hn⟩⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image T (fun x : Fin 4 →₀ ℕ => x p) hT
  have hbL : b ∈ L.support := (Finset.mem_filter.mp hb).1
  have hbv : m < Finsupp.weight v b := (Finset.mem_filter.mp hb).2
  have hbc := MvPolynomial.mem_support_iff.mp hbL
  have hex : ∃ i : Fin 4, i ≠ s ∧ i ≠ p ∧ b i ≠ 0 := by
    by_contra he
    push_neg at he
    have hle : Finsupp.weight v b ≤ Finsupp.weight w b := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply]
      apply Finset.sum_le_sum
      intro i hi
      change b i • v i ≤ b i • w i
      by_cases his : i = s
      · subst i
        rw [hvs, smul_zero]
        exact nsmul_nonneg (hw s) _
      · by_cases hip : i = p
        · subst i
          rw [hvp]
        · rw [he i his hip, zero_smul, zero_smul]
    exact (not_lt_of_ge (hle.trans (hL hbL))) hbv
  obtain ⟨i,his,hip,hbi⟩ := hex
  let a : Fin 4 →₀ ℕ := b - Finsupp.single i 1
  have ha : a + Finsupp.single i 1 = b :=
    Finsupp.sub_add_single_one_cancel hbi
  have hexj : ∃ j : Fin 4, j ≠ s ∧ a j ≠ 0 := by
    by_contra he
    push_neg at he
    have hza : a = Finsupp.single s (a s) := by
      ext j
      by_cases hj : j = s
      · subst j
        simp
      · rw [he j hj, Finsupp.single_eq_of_ne hj]
    have hz : Finsupp.weight v a = 0 := by
      rw [hza, Finsupp.weight_single, hvs, smul_zero]
    have ht := congrArg (Finsupp.weight v) ha
    rw [map_add, Finsupp.weight_single, one_smul, hz, zero_add] at ht
    exact (not_lt_of_ge ((le_of_eq ht.symm).trans (hv i))) hbv
  obtain ⟨j,hjs,haj⟩ := hexj
  have hH : hessian L i j ≠ 0 := by
    have h1 : coeff a (pderiv i L) ≠ 0 :=
      extremal_pderiv_coeff_nonzero L b hbc i hbi
    have h2 := extremal_pderiv_coeff_nonzero (pderiv i L) a h1 j haj
    intro hz
    change pderiv j (pderiv i L) = 0 at hz
    exact h2 (by rw [hz, coeff_zero])
  obtain ⟨hvi,n,t,c,e,hc,hcross⟩ := hrows i j his hip hjs hH
  obtain ⟨z,hz,hzp,hzw⟩ := rankThree_support_transfer_to_pivot L s p i j hps hip
    v hvs b hbc hbi haj n t c e hc hcross
  have hzT : z ∈ T := Finset.mem_filter.mpr
    ⟨MvPolynomial.mem_support_iff.mpr hz, by rw [hzw]; omega⟩
  have hbad := hmax z hzT
  omega


set_option maxHeartbeats 5000000 in
/-- The monomial transfer cap gives an actual extremal
contradiction when the two other active coordinates have
strictly smaller weight than the nonzero pivot. -/
theorem globalWeightOptimum_rankThree_no_unique_active_max
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hminor : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p)
    (hpos : 0 < w (l.succAbove a))
    (p : Fin 4) (hps : p ≠ l.succAbove a)
    (hp : hessian (initialForm w m P) p p ≠ 0)
    (hsmall : ∀ i, i ≠ l.succAbove a → i ≠ p →
      hessian (initialForm w m P) i i ≠ 0 ∧ w i < w p) :
    False := by
  classical
  let L := initialForm w m P
  let s := l.succAbove a
  let H := hessian L
  let v : Fin 4 → ℤ := fun i => if i = s then 0 else w p
  change p ≠ s at hps
  have hs (i j : Fin 4) : H i j = H j i := pderiv_comm_backport _ _ _
  have hmin := rankThree_rankTwoVelocity_restrictedMinors_zero L l a V hVl hVk
    hreg hV hminor
  have hL : MvPolynomial.IsWeightedHomogeneous w L m :=
    initialForm_isWeightedHomogeneous w m P
  have hmix (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) : H i p ≠ 0 := by
    intro hz
    have he := hmin p i p i hps his hps his
    change H p p * H i i = H p i * H i p at he
    rw [hz,mul_zero] at he
    exact (mul_ne_zero hp (hsmall i his hip).1) he
  have hratio (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) :
      ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧ e ≠ 0 ∧
        w p - w i = ((t : ℤ)-(n : ℤ))*w s ∧
        H i p * MvPolynomial.monomial (Finsupp.single s n) c =
          H p p * MvPolynomial.monomial (Finsupp.single s t) e := by
    have he := rankThree_rankTwoVelocity_weightedRatio L w m hw hL l a V
      hVl hVk hreg hV hminor p i hps his hip hp (hmix i his hip)
    rcases he with ⟨hz,_⟩ | ⟨_,hn⟩
    · exact (ne_of_gt hpos hz).elim
    · exact hn
  have hgap (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) :
      w s ≤ w p - w i := by
    obtain ⟨n,t,c,e,hc,he,hd,_⟩ := hratio i his hip
    have hlt := (hsmall i his hip).2
    have hspos : 0 < w s := hpos
    have hprod : 0 < ((t : ℤ)-(n : ℤ))*w s := by rw [← hd]; omega
    have hdiff : 1 ≤ (t : ℤ)-(n : ℤ) := by
      by_contra hn
      have hnon : (t : ℤ)-(n : ℤ) ≤ 0 := by omega
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hnon (le_of_lt hspos))) hprod
    rw [hd]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff (le_of_lt hspos)
  have hvs : v s = 0 := by simp [v]
  have hvp : v p = w p := by simp [v,hps]
  have hvnon (i : Fin 4) : 0 ≤ v i := by
    by_cases hi : i = s <;> simp [v,hi,hw p]
  have hvle (i : Fin 4) : v i ≤ m := by
    have hpw := weightCap_coordinate_le P w m hw hcap hdet p
    by_cases hi : i = s <;> simp [v,hi,le_of_lt hm,hpw]
  have hrows (i j : Fin 4) (his : i ≠ s) (hip : i ≠ p) (hjs : j ≠ s)
      (hij : H i j ≠ 0) :
      v i ≤ v p ∧ ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧
        H i j * MvPolynomial.monomial (Finsupp.single s n) c =
          H p j * MvPolynomial.monomial (Finsupp.single s t) e := by
    obtain ⟨n,t,c,e,hc,he,hd,hcross⟩ := hratio i his hip
    refine ⟨by rw [hvp]; change (if i = s then 0 else w p) ≤ w p; rw [if_neg his],n,t,c,e,hc,?_⟩
    have hrow := hmin p i p j hps his hps hjs
    change H p p * H i j = H p j * H i p at hrow
    apply mul_left_cancel₀ hp
    calc
      H p p * (H i j * MvPolynomial.monomial (Finsupp.single s n) c) =
          H p j * (H i p * MvPolynomial.monomial (Finsupp.single s n) c) := by
        rw [← mul_assoc, hrow, mul_assoc]
      _ = H p j * (H p p * MvPolynomial.monomial (Finsupp.single s t) e) := by rw [hcross]
      _ = H p p * (H p j * MvPolynomial.monomial (Finsupp.single s t) e) := by ring
  have hcapv : IsWeightLE v m L :=
    rankThree_support_cap_of_monomial_rows L w v m hw
      (isWeightLE_of_isWeightedHomogeneous hL) s p hps hvs hvp hvle hrows
  let d : Fin 4 → ℤ := fun i => v i - w i
  have hds : d s = -w s := by change v s - w s = _; rw [hvs,zero_sub]
  have hdp : d p = 0 := by change v p - w p = _; rw [hvp,sub_self]
  have hdge (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) : w s ≤ d i := by
    change w s ≤ v i - w i
    rw [show v i = w p by simp [v,his]]
    exact hgap i his hip
  obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hps
  have hsum : 0 < ∑ i : Fin 4, d i := by
    rw [Fin.sum_univ_succAbove d s, hds]
    rw [Fin.sum_univ_succAbove (fun i : Fin 3 => d (s.succAbove i)) b]
    change 0 < -w s + (d (s.succAbove b) +
      ∑ i : Fin 2, d (s.succAbove (b.succAbove i)))
    rw [hb,hdp,zero_add,Fin.sum_univ_two]
    have he (i : Fin 2) : w s ≤ d (s.succAbove (b.succAbove i)) := by
      apply hdge
      · exact Fin.succAbove_ne _ _
      · intro h
        have hh : s.succAbove (b.succAbove i) = s.succAbove b := h.trans hb.symm
        exact (Fin.succAbove_ne b i) (Fin.succAbove_right_injective hh)
    have hh0 := he 0
    have hh1 := he 1
    have hsp : 0 < w s := hpos
    omega
  obtain ⟨u,hu,hbad⟩ := globalWeightOptimum_no_improvingSlope P w d m
    hw hm hcap hclock hopt (by intro i hi; change 0 ≤ v i-w i; rw [hi,sub_zero]; exact hvnon i)
    hsum
  have hweight : Finsupp.weight w u = m :=
    ((mem_support_initialForm_iff w m P u).mp hu).2
  have hfun : d = (fun i => (1 : ℤ)*v i + (-1)*w i) := by
    funext i
    simp [d,sub_eq_add_neg]
  rw [hfun,firstWall_weight_scaled_add,one_mul,neg_one_mul,hweight] at hbad
  have he := hcapv hu
  omega


set_option maxHeartbeats 4000000 in
/-- Weighted ratio rigidity for any restricted rank-one polynomial
Hessian, independently of the velocity chart that produced it. -/
theorem rankThree_restricted_weightedRatio
    (L : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ j, 0 ≤ w j)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (s : Fin 4)
    (hmin : ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (p i : Fin 4) (hp : p ≠ s) (hi : i ≠ s)
    (hip : i ≠ p) (hdiag : hessian L p p ≠ 0) (hmix : hessian L i p ≠ 0) :
    (w s = 0 ∧ w i = w p) ∨
      (0 < w s ∧
        ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧ e ≠ 0 ∧
          w p - w i = ((t : ℤ) - (n : ℤ)) * w s ∧
          hessian L i p * MvPolynomial.monomial (Finsupp.single s n) c =
            hessian L p p * MvPolynomial.monomial (Finsupp.single s t) e) := by
  classical
  let f := algebraMap (B K) (E K)
  let A := hessian L p p
  let C₀ := hessian L i p
  let r := f C₀ / f A
  let P := IsFractionRing.num (B K) r
  let Q : B K := IsFractionRing.den (B K) r
  have hQ0 : Q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) r)
  have hAf : f A ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hdiag
  have hQf : f Q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hQ0
  have hrepr : f P / f Q = f C₀ / f A :=
    IsFractionRing.mk'_num_den' (B K) r
  have hcross : C₀ * Q = A * P := by
    apply IsFractionRing.injective (B K) (E K)
    change f (C₀*Q) = f (A*P)
    simp only [map_mul]
    rw [mul_comm (f A)]
    exact ((div_eq_div_iff hQf hAf).mp hrepr).symm
  have hder (j : Fin 4) (hj : j ≠ s) : pderiv j P = 0 ∧ pderiv j Q = 0 :=
    rankOnePartial_num_den_independent r s
      (rankOneHessian_twoRows_partialRatios_constant L s p i hip hp hi hdiag
        (fun j hj => (hmin p i p j hp hi hp hj).trans (mul_comm _ _))) j hj
  have hA : MvPolynomial.IsWeightedHomogeneous w A (m-w p-w p) :=
    pderiv_isWeightedHomogeneous (pderiv_isWeightedHomogeneous hL p) p
  have hC : MvPolynomial.IsWeightedHomogeneous w C₀ (m-w i-w p) :=
    pderiv_isWeightedHomogeneous (pderiv_isWeightedHomogeneous hL i) p
  by_cases hz : w s = 0
  · have he := rankOne_weighted_relativeRatio_zeroWeight w s hz _ _ A C₀
      hmix hA hC P Q hQ0 hcross
      (fun j hj => (hder j hj).1) (fun j hj => (hder j hj).2)
    exact Or.inl ⟨hz, by omega⟩
  · have hpos : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm hz)
    obtain ⟨n,t,c,e,hc,he,hwt,hpow⟩ :=
      rankOne_weighted_relativeRatio_cross_power w s hpos _ _ A C₀
        hdiag hmix hA hC P Q hQ0 hcross
        (fun j hj => (hder j hj).1) (fun j hj => (hder j hj).2)
    refine Or.inr ⟨hpos,n,t,c,e,hc,he,?_,hpow⟩
    change w p - w i = ((t : ℤ) - (n : ℤ)) * w s
    rw [sub_mul]
    omega


set_option maxHeartbeats 5000000 in
/-- A zero restricted diagonal forces its whole restricted row
to vanish. This does not imply a full zero Hessian row. -/
theorem rankThree_restricted_row_zero
    (L : B K) (s i : Fin 4) (hi : i ≠ s)
    (hmin : ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (hii : hessian L i i = 0) :
    ∀ j, j ≠ s → hessian L i j = 0 := by
  intro j hj
  have he := hmin i j i j hi hj hi hj
  rw [hii,zero_mul,show hessian L j i = hessian L i j from pderiv_comm_backport i j L] at he
  exact (mul_eq_zero.mp he.symm).elim id id

/-- The global optimum forbids two distinct zero restricted
diagonals, since they give a jointly affine principal plane. -/
theorem globalWeightOptimum_rankThree_restricted_atMostOne_zero
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m)
    (s i j : Fin 4) (hi : i ≠ s) (hj : j ≠ s)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (hii : hessian (initialForm w m P) i i = 0)
    (hjj : hessian (initialForm w m P) j j = 0) :
    i = j := by
  classical
  by_contra hij
  let L := initialForm w m P
  have hz := rankThree_restricted_row_zero L s i hi hmin hii j hj
  obtain ⟨u,hu,hgt⟩ := globalWeightOptimum_no_jointlyAffine_support P w m
    hw hm hcap hclock hopt i j
  have hle := extremal_jointlyAffine_support_of_hessian_zero L i j hij hii hjj hz u hu
  omega

/-- Collapse the omitted weight, raising affine-only coordinates to the cap. -/
noncomputable def rankThreeCollapsedWeight (L : B K) (w : Fin 4 → ℤ)
    (m : ℤ) (s p : Fin 4) : Fin 4 → ℤ := by
  classical
  exact fun i => if i = s then 0 else if hessian L i i = 0 then m else w p

set_option maxHeartbeats 5000000 in
/-- A generalized signed-slope contradiction: zero restricted rows
are given the full cap, and all other restricted variables the
weight of a nonzero pivot. Only the strict total gain is required. -/
theorem globalWeightOptimum_rankThree_restricted_no_gain
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s p : Fin 4) (hps : p ≠ s) (hpos : 0 < w s)
    (hp : hessian (initialForm w m P) p p ≠ 0)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    (∑ i, rankThreeCollapsedWeight (initialForm w m P) w m s p i) ≤ ∑ i, w i := by
  classical
  let L := initialForm w m P
  let H := hessian L
  let v : Fin 4 → ℤ := fun i => if i = s then 0 else
    if H i i = 0 then m else w p
  change (∑ i, v i) ≤ ∑ i, w i
  by_contra hn
  have hL : MvPolynomial.IsWeightedHomogeneous w L m :=
    initialForm_isWeightedHomogeneous w m P
  have hpw := weightCap_coordinate_le P w m hw hcap hdet p
  have hvs : v s = 0 := by simp [v]
  have hvp : v p = w p := by simp [v,hps,show H p p ≠ 0 from hp]
  have hvnon (i : Fin 4) : 0 ≤ v i := by
    by_cases hi : i = s
    · simp [v,hi]
    · by_cases hz : H i i = 0 <;> simp [v,hi,hz,le_of_lt hm,hw p]
  have hvle (i : Fin 4) : v i ≤ m := by
    by_cases hi : i = s
    · simp [v,hi,le_of_lt hm]
    · by_cases hz : H i i = 0 <;> simp [v,hi,hz,hpw]
  have hrows (i j : Fin 4) (his : i ≠ s) (hip : i ≠ p) (hjs : j ≠ s)
      (hij : H i j ≠ 0) :
      v i ≤ v p ∧ ∃ n t : ℕ, ∃ c e : K, c ≠ 0 ∧
        H i j * MvPolynomial.monomial (Finsupp.single s n) c =
          H p j * MvPolynomial.monomial (Finsupp.single s t) e := by
    have hii : H i i ≠ 0 := by
      intro hz
      exact hij (rankThree_restricted_row_zero L s i his hmin hz j hjs)
    have hmix : H i p ≠ 0 := by
      intro hz
      have he := hmin p i p i hps his hps his
      change H p p * H i i = H p i * H i p at he
      rw [hz,mul_zero] at he
      exact (mul_ne_zero hp hii) he
    have hr := rankThree_restricted_weightedRatio L w m hw hL s hmin p i
      hps his hip hp hmix
    rcases hr with ⟨hz,_⟩ | ⟨_,n,t,c,e,hc,he,hd,hcross⟩
    · exact (ne_of_gt hpos hz).elim
    refine ⟨by rw [hvp]; simp [v,his,hii],n,t,c,e,hc,?_⟩
    have hrow := hmin p i p j hps his hps hjs
    change H p p * H i j = H p j * H i p at hrow
    apply mul_left_cancel₀ hp
    calc
      H p p * (H i j * MvPolynomial.monomial (Finsupp.single s n) c) =
          H p j * (H i p * MvPolynomial.monomial (Finsupp.single s n) c) := by
        rw [← mul_assoc, hrow, mul_assoc]
      _ = H p j * (H p p * MvPolynomial.monomial (Finsupp.single s t) e) := by rw [hcross]
      _ = H p p * (H p j * MvPolynomial.monomial (Finsupp.single s t) e) := by ring
  have hcapv : IsWeightLE v m L :=
    rankThree_support_cap_of_monomial_rows L w v m hw
      (isWeightLE_of_isWeightedHomogeneous hL) s p hps hvs hvp hvle hrows
  let d : Fin 4 → ℤ := fun i => v i - w i
  have hsum : 0 < ∑ i : Fin 4, d i := by
    change 0 < ∑ i : Fin 4, (v i - w i)
    rw [Finset.sum_sub_distrib]
    omega
  obtain ⟨u,hu,hbad⟩ := globalWeightOptimum_no_improvingSlope P w d m
    hw hm hcap hclock hopt (by intro i hi; change 0 ≤ v i-w i; rw [hi,sub_zero]; exact hvnon i)
    hsum
  have hweight : Finsupp.weight w u = m :=
    ((mem_support_initialForm_iff w m P u).mp hu).2
  have hfun : d = (fun i => (1 : ℤ)*v i + (-1)*w i) := by
    funext i
    simp [d,sub_eq_add_neg]
  rw [hfun,firstWall_weight_scaled_add,one_mul,neg_one_mul,hweight] at hbad
  have he := hcapv hu
  omega


set_option maxHeartbeats 5000000 in
/-- An affine-only restricted coordinate must have a nonzero
mixed entry with the omitted coordinate. Its weight is therefore
at least one omitted weight below the cap. -/
theorem globalWeightOptimum_rankThree_zeroRow_weight_gap
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s i : Fin 4) (his : i ≠ s)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (hii : hessian (initialForm w m P) i i = 0) :
    w i + w s ≤ m := by
  let L := initialForm w m P
  by_contra hn
  have hL : IsWeightLE w m L :=
    isWeightLE_of_isWeightedHomogeneous (initialForm_isWeightedHomogeneous w m P)
  have hzero : hessian L i s = 0 :=
    eq_zero_of_nonnegativeWeight_negative_cap w hw _ (by omega) _ (hL.hessian_entry i s)
  have hrow (j : Fin 4) : pderiv j (pderiv i L) = 0 := by
    change hessian L i j = 0
    by_cases hj : j = s
    · rw [hj]
      exact hzero
    · exact rankThree_restricted_row_zero L s i his hmin hii j hj
  exact globalWeightOptimum_no_constant_partial P w m hw hm hcap hclock hopt hdet i _
    (extremal_eq_C_of_all_pderiv_zero (pderiv i L) hrow)

set_option maxHeartbeats 5000000 in
/-- If one restricted row vanishes and the remaining two
nonzero diagonal weights differ, the positive omitted weight
case is impossible at the actual optimum. -/
theorem globalWeightOptimum_rankThree_no_one_zero_distinct_weights
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s p i j : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hjs : j ≠ s)
    (hip : i ≠ p) (hjp : j ≠ p) (hji : j ≠ i)
    (hcover : ∀ a : Fin 4, a = s ∨ a = p ∨ a = i ∨ a = j)
    (hpos : 0 < w s)
    (hp : hessian (initialForm w m P) p p ≠ 0)
    (hi : hessian (initialForm w m P) i i ≠ 0)
    (hj : hessian (initialForm w m P) j j = 0)
    (hlt : w i < w p)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    False := by
  classical
  let L := initialForm w m P
  let H := hessian L
  let v := rankThreeCollapsedWeight L w m s p
  have hmix : H i p ≠ 0 := by
    intro hz
    have he := hmin p i p i hps his hps his
    change H p p * H i i = H p i * H i p at he
    rw [hz,mul_zero] at he
    exact (mul_ne_zero hp hi) he
  have hr := rankThree_restricted_weightedRatio L w m hw
    (initialForm_isWeightedHomogeneous w m P) s hmin p i hps his hip hp hmix
  rcases hr with ⟨hz,_⟩ | ⟨_,n,t,c,e,hc,he,hd,hcross⟩
  · exact (ne_of_gt hpos hz).elim
  have hgap : w s ≤ w p - w i := by
    have hprod : 0 < ((t : ℤ)-(n : ℤ))*w s := by rw [← hd]; omega
    have hdiff : 1 ≤ (t : ℤ)-(n : ℤ) := by
      by_contra hn
      have hnon : (t : ℤ)-(n : ℤ) ≤ 0 := by omega
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hnon (le_of_lt hpos))) hprod
    rw [hd]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff (le_of_lt hpos)
  have hgapj := globalWeightOptimum_rankThree_zeroRow_weight_gap P w m hw hm hcap
    hclock hopt hdet s j hjs hmin hj
  have hvs : v s = 0 := by simp [v,rankThreeCollapsedWeight]
  have hvp : v p = w p := by
    change (if p = s then 0 else if hessian L p p = 0 then m else w p) = w p
    rw [if_neg hps, if_neg (show hessian L p p ≠ 0 from hp)]
  have hvi : v i = w p := by
    change (if i = s then 0 else if hessian L i i = 0 then m else w p) = w p
    rw [if_neg his, if_neg (show hessian L i i ≠ 0 from hi)]
  have hvj : v j = m := by
    change (if j = s then 0 else if hessian L j j = 0 then m else w p) = m
    rw [if_neg hjs, if_pos (show hessian L j j = 0 from hj)]
  have hopt' : (∑ a : Fin 4, v a) ≤ ∑ a : Fin 4, w a :=
    globalWeightOptimum_rankThree_restricted_no_gain P w m hw hm hcap hclock hopt hdet
      s p hps hpos hp hmin
  have hsum (f : Fin 4 → ℤ) : ∑ a : Fin 4, f a = f s + f p + f i + f j := by
    have hset : (Finset.univ : Finset (Fin 4)) = {s,p,i,j} := by
      ext a
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
      exact hcover a
    rw [hset]
    simp [Ne.symm hps,Ne.symm his,Ne.symm hjs,Ne.symm hip,Ne.symm hjp,Ne.symm hji]
    ring
  rw [hsum v,hsum w,hvs,hvp,hvi,hvj] at hopt'
  omega


set_option maxHeartbeats 5000000 in
/-- Equal positive-omitted-weight rows have a ground-field ratio. -/
theorem rankThree_restricted_equalWeight_rows
    (L : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ j, 0 ≤ w j) (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (s p i : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hip : i ≠ p)
    (hpos : 0 < w s) (hwi : w i = w p)
    (hp : hessian L p p ≠ 0) (hi : hessian L i i ≠ 0)
    (hmin : ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    ∃ c : K, ∀ j, j ≠ s → hessian L i j = MvPolynomial.C c * hessian L p j := by
  classical
  have hmix : hessian L i p ≠ 0 := by
    intro hz
    have he := hmin p i p i hps his hps his
    rw [hz,mul_zero] at he
    exact (mul_ne_zero hp hi) he
  have hr := rankThree_restricted_weightedRatio L w m hw hL s hmin p i
    hps his hip hp hmix
  rcases hr with ⟨hz,_⟩ | ⟨_,n,t,c,e,hc,he,hd,hcross⟩
  · exact (ne_of_gt hpos hz).elim
  have hnt : t = n := by
    rw [← hwi,sub_self] at hd
    have hh := (mul_eq_zero.mp hd.symm).resolve_right (ne_of_gt hpos)
    omega
  subst t
  let M : B K := MvPolynomial.monomial (Finsupp.single s n) (1 : K)
  have hM : M ≠ 0 := by
    exact MvPolynomial.monomial_eq_zero.not.mpr one_ne_zero
  have hm (b : K) : MvPolynomial.monomial (Finsupp.single s n) b =
      MvPolynomial.C b * M := by
    change _ = MvPolynomial.C b * MvPolynomial.monomial (Finsupp.single s n) 1
    rw [MvPolynomial.C_mul_monomial,mul_one]
  rw [hm c,hm e,← mul_assoc,← mul_assoc] at hcross
  have heq := mul_right_cancel₀ hM hcross
  have hc' : (MvPolynomial.C c : B K) ≠ 0 := MvPolynomial.C_ne_zero.mpr hc
  have hratio : hessian L i p = MvPolynomial.C (e / c) * hessian L p p := by
    apply mul_right_cancel₀ hc'
    calc
      hessian L i p * MvPolynomial.C c = hessian L p p * MvPolynomial.C e := heq
      _ = (MvPolynomial.C (e/c) * hessian L p p) * MvPolynomial.C c := by
        rw [show MvPolynomial.C e = MvPolynomial.C (e/c) * MvPolynomial.C c by
          rw [← map_mul,div_mul_cancel₀ _ hc]]
        ring
  refine ⟨e/c,?_⟩
  intro j hj
  apply mul_left_cancel₀ hp
  rw [hmin p i p j hps his hps hj,hratio]
  ring

set_option maxHeartbeats 5000000 in
/-- Kill a proportional restricted row by a constant column shear.
The surviving entries are simply the substituted original entries.
In particular every restricted minor stays zero. -/
theorem rankThree_restricted_shear_zero_row
    (L : B K) (w : Fin 4 → ℤ)
    (s p i : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hip : i ≠ p)
    (hwi : w i = w p) (c : K)
    (hrow : ∀ j, j ≠ s → hessian L i j = MvPolynomial.C c * hessian L p j)
    (hmin : ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    ∃ N : Matrix (Fin 4) (Fin 4) K, N.det = 1 ∧
      (∀ a b, w a ≠ w b → N a b = 0) ∧
      let Q := weightedLinearSubstitution N L
      (∀ j, j ≠ s → hessian Q i j = 0) ∧
      (∀ a b, a ≠ i → b ≠ i →
        hessian Q a b = weightedLinearSubstitution N (hessian L a b)) ∧
      (∀ a b d e : Fin 4, a ≠ s → b ≠ s → d ≠ s → e ≠ s →
        hessian Q a d * hessian Q b e = hessian Q a e * hessian Q b d) := by
  classical
  let d : Fin 4 → K := Pi.single i 1 - Pi.single p c
  have hdi : d i = 1 := by simp [d,hip]
  let N := extremalKernelShear d i
  let f := weightedLinearSubstitution N
  let Q := f L
  have hN : N.det = 1 := extremalKernelShear_det d i
  have hNb : ∀ a b, w a ≠ w b → N a b = 0 := by
    apply extremalKernelShear_respects_weight w d i
    intro a ha
    have hai : a ≠ i := fun h => ha (congrArg w h)
    have hap : a ≠ p := by
      intro h
      apply ha
      rw [h, hwi]
    simp [d,Pi.single_eq_of_ne hai,Pi.single_eq_of_ne hap]
  have hNi (a : Fin 4) : N a i = d a := by
    change extremalKernelShear d i a i = d a
    rw [extremalKernelShear_column d i (by rw [hdi]; exact one_ne_zero),hdi,div_one]
  have hNfix (b : Fin 4) (hb : b ≠ i) (a : Fin 4) :
      N a b = (1 : Matrix (Fin 4) (Fin 4) K) a b :=
    extremalKernelShear_other_column d i a b hb
  have hC (b : K) : f (MvPolynomial.C b) = MvPolynomial.C b := f.commutes b
  let R := pderiv i L - MvPolynomial.C c * pderiv p L
  have hpartial : pderiv i Q = f R := by
    change pderiv i (weightedLinearSubstitution N L) = f R
    rw [weightedLinearSubstitution_partial]
    change (∑ a : Fin 4, f (pderiv a L) * MvPolynomial.C (N a i)) = f R
    simp only [hNi,d,Pi.sub_apply,map_sub,mul_sub,Finset.sum_sub_distrib]
    have hsum (b : Fin 4) (e : K) :
        (∑ a : Fin 4, f (pderiv a L) * MvPolynomial.C ((Pi.single b e : Fin 4 → K) a)) =
          f (pderiv b L) * MvPolynomial.C e := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ ha
        simp [Pi.single_eq_of_ne ha]
      · simp
    rw [hsum i 1,hsum p c,map_one,mul_one]
    change _ = f (pderiv i L - MvPolynomial.C c * pderiv p L)
    rw [map_sub,map_mul,hC,mul_comm (MvPolynomial.C c)]
  have hR (a : Fin 4) (ha : a ≠ s) : pderiv a R = 0 := by
    change pderiv a (pderiv i L - MvPolynomial.C c * pderiv p L) = 0
    rw [map_sub,MvPolynomial.pderiv_C_mul,← hessian_apply,← hessian_apply,hrow a ha,sub_self]
  have hzero (j : Fin 4) (hj : j ≠ s) : hessian Q i j = 0 := by
    change pderiv j (pderiv i Q) = 0
    rw [hpartial]
    change pderiv j (weightedLinearSubstitution N R) = 0
    rw [weightedLinearSubstitution_partial]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = s
    · subst a
      have hz : N s j = 0 := by
        by_cases hji : j = i
        · subst j
          rw [hNi]
          simp [d,Pi.single_eq_of_ne (Ne.symm his),Pi.single_eq_of_ne (Ne.symm hps)]
        · rw [hNfix j hji s]
          simp [Matrix.one_apply,Ne.symm hj]
      rw [hz,map_zero,mul_zero]
    · rw [hR a ha,map_zero,zero_mul]
  have hfixed (a b : Fin 4) (ha : a ≠ i) (hb : b ≠ i) :
      hessian Q a b = f (hessian L a b) := by
    change pderiv b (pderiv a (weightedLinearSubstitution N L)) =
      weightedLinearSubstitution N (pderiv b (pderiv a L))
    rw [rankTwo_partial_fixedColumn L N a (hNfix a ha),
      rankTwo_partial_fixedColumn _ N b (hNfix b hb)]
  have hsym (a b : Fin 4) : hessian Q a b = hessian Q b a :=
    pderiv_comm_backport _ _ _
  refine ⟨N,hN,hNb,hzero,hfixed,?_⟩
  intro a b d e ha hb hd he
  by_cases hai : a = i
  · subst a
    rw [hzero d hd,hzero e he,zero_mul,zero_mul]
  by_cases hbi : b = i
  · subst b
    rw [hzero d hd,hzero e he,mul_zero,mul_zero]
  by_cases hdi : d = i
  · subst d
    rw [hsym a i,hsym b i,hzero a ha,hzero b hb,zero_mul,mul_zero]
  by_cases hei : e = i
  · subst e
    rw [hsym a i,hsym b i,hzero a ha,hzero b hb,mul_zero,zero_mul]
  rw [hfixed a d hai hdi,hfixed b e hbi hei,hfixed a e hai hei,hfixed b d hbi hdi,
    ← map_mul,← map_mul,hmin a b d e ha hb hd he]


set_option maxHeartbeats 5000000 in
/-- All one-zero restricted diagonal configurations are impossible
at positive omitted weight. The equal-weight case is reduced to
two zero restricted rows by an actual determinant-one shear. -/
theorem globalWeightOptimum_rankThree_no_one_zero
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s p i j : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hjs : j ≠ s)
    (hip : i ≠ p) (hjp : j ≠ p) (hji : j ≠ i)
    (hcover : ∀ a : Fin 4, a = s ∨ a = p ∨ a = i ∨ a = j)
    (hpos : 0 < w s)
    (hp : hessian (initialForm w m P) p p ≠ 0)
    (hi : hessian (initialForm w m P) i i ≠ 0)
    (hj : hessian (initialForm w m P) j j = 0)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    False := by
  classical
  rcases lt_trichotomy (w i) (w p) with hlt | heq | hgt
  · exact globalWeightOptimum_rankThree_no_one_zero_distinct_weights P w m hw hm
      hcap hclock hopt hdet s p i j hps his hjs hip hjp hji hcover hpos hp hi hj hlt hmin
  · let L := initialForm w m P
    obtain ⟨c,hrow⟩ := rankThree_restricted_equalWeight_rows L w m hw
      (initialForm_isWeightedHomogeneous w m P) s p i hps his hip hpos heq hp hi hmin
    obtain ⟨N,hN,hNb,hzero,hfix,hmin'⟩ :=
      rankThree_restricted_shear_zero_row L w s p i hps his hip heq c hrow hmin
    let Q := weightedLinearSubstitution N P
    have hcapQ := weightedLinearSubstitution_isWeightLE w N hNb m P hcap
    have hoptQ := hopt.substitution N hN
    have hlead : initialForm w m Q = weightedLinearSubstitution N L := by
      change initialForm w m (weightedLinearSubstitution N P) = _
      exact weightedLinearSubstitution_initialForm w N hNb m P
    have hii : hessian (initialForm w m Q) i i = 0 := by
      rw [hlead]
      exact hzero i his
    have hjj : hessian (initialForm w m Q) j j = 0 := by
      rw [hlead,hfix j j hji hji,show hessian L j j = 0 from hj,map_zero]
    have hminQ : ∀ a b d e : Fin 4, a ≠ s → b ≠ s → d ≠ s → e ≠ s →
        hessian (initialForm w m Q) a d * hessian (initialForm w m Q) b e =
          hessian (initialForm w m Q) a e * hessian (initialForm w m Q) b d := by
      rw [hlead]
      exact hmin'
    exact (Ne.symm hji) (globalWeightOptimum_rankThree_restricted_atMostOne_zero Q w m
      hw hm hcapQ hclock hoptQ s i j his hjs hminQ hii hjj)
  · have hcover' (a : Fin 4) : a = s ∨ a = i ∨ a = p ∨ a = j := by
      rcases hcover a with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    exact globalWeightOptimum_rankThree_no_one_zero_distinct_weights P w m hw hm
      hcap hclock hopt hdet s i p j his hps hjs (Ne.symm hip) hji hjp
      hcover' hpos hi hp hj hgt hmin

set_option maxHeartbeats 5000000 in
/-- In the three-nonzero restricted branch, any repeated weight
creates an affine-only row, which has just been excluded. -/
theorem globalWeightOptimum_rankThree_no_repeated_nonzero_weights
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s p i j : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hjs : j ≠ s)
    (hip : i ≠ p) (hjp : j ≠ p) (hji : j ≠ i)
    (hcover : ∀ a : Fin 4, a = s ∨ a = p ∨ a = i ∨ a = j)
    (hpos : 0 < w s) (heq : w i = w p)
    (hp : hessian (initialForm w m P) p p ≠ 0)
    (hi : hessian (initialForm w m P) i i ≠ 0)
    (hj : hessian (initialForm w m P) j j ≠ 0)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    False := by
  classical
  let L := initialForm w m P
  obtain ⟨c,hrow⟩ := rankThree_restricted_equalWeight_rows L w m hw
    (initialForm_isWeightedHomogeneous w m P) s p i hps his hip hpos heq hp hi hmin
  obtain ⟨N,hN,hNb,hzero,hfix,hmin'⟩ :=
    rankThree_restricted_shear_zero_row L w s p i hps his hip heq c hrow hmin
  let Q := weightedLinearSubstitution N P
  have hcapQ := weightedLinearSubstitution_isWeightLE w N hNb m P hcap
  have hoptQ := hopt.substitution N hN
  have hdetQ : hessianDeterminant Q = 1 := by
    change hessianDeterminant (weightedLinearSubstitution N P) = 1
    rw [weightedLinearSubstitution_det N hN,hdet,map_one]
  have hlead : initialForm w m Q = weightedLinearSubstitution N L := by
    change initialForm w m (weightedLinearSubstitution N P) = _
    exact weightedLinearSubstitution_initialForm w N hNb m P
  have hii : hessian (initialForm w m Q) i i = 0 := by
    rw [hlead]
    exact hzero i his
  have hnon (a : Fin 4) (ha : a ≠ i) (h : hessian L a a ≠ 0) :
      hessian (initialForm w m Q) a a ≠ 0 := by
    rw [hlead,hfix a a ha ha]
    intro hz
    exact h (rankOne_substitution_injective N hN
      (hz.trans (map_zero (weightedLinearSubstitution N)).symm))
  have hminQ : ∀ a b d e : Fin 4, a ≠ s → b ≠ s → d ≠ s → e ≠ s →
      hessian (initialForm w m Q) a d * hessian (initialForm w m Q) b e =
        hessian (initialForm w m Q) a e * hessian (initialForm w m Q) b d := by
    rw [hlead]
    exact hmin'
  have hcover' (a : Fin 4) : a = s ∨ a = p ∨ a = j ∨ a = i := by
    rcases hcover a with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  exact globalWeightOptimum_rankThree_no_one_zero Q w m hw hm hcapQ hclock hoptQ hdetQ
    s p j i hps hjs his hjp hip (Ne.symm hji) hcover' hpos
    (hnon p (Ne.symm hip) hp) (hnon j hji hj) hii hminQ


/-- Enumerate the two remaining coordinates without finite-case
enumeration of a dependent matrix expression. -/
theorem rankThree_remaining_two_coordinates (s j : Fin 4) (hjs : j ≠ s) :
    ∃ p i : Fin 4, p ≠ s ∧ i ≠ s ∧ i ≠ p ∧ j ≠ p ∧ j ≠ i ∧
      ∀ a : Fin 4, a = s ∨ a = p ∨ a = i ∨ a = j := by
  obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hjs
  let p := s.succAbove (b.succAbove 0)
  let i := s.succAbove (b.succAbove 1)
  have hp : p ≠ s := Fin.succAbove_ne _ _
  have hi : i ≠ s := Fin.succAbove_ne _ _
  have hip : i ≠ p := by
    intro h
    have he : (1 : Fin 2) = 0 :=
      Fin.succAbove_right_injective (Fin.succAbove_right_injective h)
    exact (by decide : (1 : Fin 2) ≠ 0) he
  have hjp : j ≠ p := by
    intro h
    have he : b = b.succAbove 0 := Fin.succAbove_right_injective (hb.trans h)
    exact (Fin.succAbove_ne b 0) he.symm
  have hji : j ≠ i := by
    intro h
    have he : b = b.succAbove 1 := Fin.succAbove_right_injective (hb.trans h)
    exact (Fin.succAbove_ne b 1) he.symm
  refine ⟨p,i,hp,hi,hip,hjp,hji,?_⟩
  intro a
  by_cases ha : a = s
  · exact Or.inl ha
  obtain ⟨c,hc⟩ := Fin.exists_succAbove_eq ha
  by_cases hcb : c = b
  · right; right; right
    rw [← hc,hcb,hb]
  obtain ⟨d,hd⟩ := Fin.exists_succAbove_eq hcb
  have he : d = 0 ∨ d = 1 := by fin_cases d <;> simp
  rcases he with he | he
  · right; left
    rw [← hc,← hd,he]
  · right; right; left
    rw [← hc,← hd,he]

set_option maxHeartbeats 6000000 in
/-- Full positive omitted weight exclusion in the actual rank-two
velocity branch. All diagonal-zero and repeated-weight branches
are handled in genuine linear charts of the same extremal source. -/
theorem globalWeightOptimum_rankThree_no_rankTwoVelocity_positiveWeight
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hminor : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p)
    (hpos : 0 < w (l.succAbove a)) :
    False := by
  classical
  let s := l.succAbove a
  let L := initialForm w m P
  have hmin := rankThree_rankTwoVelocity_restrictedMinors_zero L l a V hVl hVk
    hreg hV hminor
  have hnon (j : Fin 4) (hjs : j ≠ s) : hessian L j j ≠ 0 := by
    intro hj
    obtain ⟨p,i,hps,his,hip,hjp,hji,hcover⟩ :=
      rankThree_remaining_two_coordinates s j hjs
    have hp : hessian L p p ≠ 0 := by
      intro hz
      exact hjp (globalWeightOptimum_rankThree_restricted_atMostOne_zero P w m
        hw hm hcap hclock hopt s j p hjs hps hmin hj hz)
    have hi : hessian L i i ≠ 0 := by
      intro hz
      exact hji (globalWeightOptimum_rankThree_restricted_atMostOne_zero P w m
        hw hm hcap hclock hopt s j i hjs his hmin hj hz)
    exact globalWeightOptimum_rankThree_no_one_zero P w m hw hm hcap hclock hopt hdet
      s p i j hps his hjs hip hjp hji hcover hpos hp hi hj hmin
  have hdistinct (p i : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hip : i ≠ p) :
      w i ≠ w p := by
    intro heq
    obtain ⟨q,j,hqs,hjs,hjq,hiq,hij,hcover⟩ :=
      rankThree_remaining_two_coordinates s i his
    have hpcover : p = q ∨ p = j := by
      rcases hcover p with h | h | h | h
      · exact (hps h).elim
      · exact Or.inl h
      · exact Or.inr h
      · exact (hip h.symm).elim
    rcases hpcover with h | h
    · subst q
      have hcover' (b : Fin 4) : b = s ∨ b = p ∨ b = i ∨ b = j := by
        rcases hcover b with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
      exact globalWeightOptimum_rankThree_no_repeated_nonzero_weights P w m hw hm
        hcap hclock hopt hdet s p i j hps his hjs hip hjq (Ne.symm hij)
        hcover' hpos heq (hnon p hps) (hnon i his) (hnon j hjs) hmin
    · subst j
      have hcover' (b : Fin 4) : b = s ∨ b = p ∨ b = i ∨ b = q := by
        rcases hcover b with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      exact globalWeightOptimum_rankThree_no_repeated_nonzero_weights P w m hw hm
        hcap hclock hopt hdet s p i q hps his hqs hip (Ne.symm hjq) (Ne.symm hiq)
        hcover' hpos heq (hnon p hps) (hnon i his) (hnon q hqs) hmin
  let T := Finset.univ.filter (fun i : Fin 4 => i ≠ s)
  have hT : T.Nonempty :=
    ⟨s.succAbove 0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Fin.succAbove_ne _ _⟩⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image T w hT
  have hps : p ≠ s := (Finset.mem_filter.mp hp).2
  apply globalWeightOptimum_rankThree_no_unique_active_max P w m hw hm
    hcap hclock hopt hdet l a V hVl hVk hreg hV hminor hpos p hps (hnon p hps)
  intro i his hip
  refine ⟨hnon i his,?_⟩
  exact lt_of_le_of_ne (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,his⟩))
    (hdistinct p i hps his hip)


set_option maxHeartbeats 5000000 in
/-- A zero restricted row at zero omitted weight is a full-source
split row. Its leading partial has only zero-weight monomials,
forcing the coordinate weight to be exactly the cap. -/
theorem globalWeightOptimum_rankThree_zeroWeight_zeroRow_terminal
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s i : Fin 4) (his : i ≠ s) (hws : w s = 0)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (hii : hessian (initialForm w m P) i i = 0) :
    Function.Injective (mvGradientMap P) := by
  classical
  let L := initialForm w m P
  let G := pderiv i L
  have hG (j : Fin 4) (hj : j ≠ s) : pderiv j G = 0 :=
    rankThree_restricted_row_zero L s i his hmin hii j hj
  have hG0 : G ≠ 0 := by
    intro hz
    apply globalWeightOptimum_no_constant_partial P w m hw hm hcap hclock hopt hdet i 0
    simpa only [map_zero] using hz
  have hex : ∃ u : Fin 4 →₀ ℕ, coeff u G ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hG0
    ext u
    rw [hn u,coeff_zero]
  obtain ⟨u,hu⟩ := hex
  have hu' := rankOne_single_support_of_partialConstants G s hG u hu
  have hwt : Finsupp.weight w u = m - w i :=
    pderiv_isWeightedHomogeneous (initialForm_isWeightedHomogeneous w m P) i hu
  rw [hu',Finsupp.weight_single,hws,smul_zero] at hwt
  have hshift : m - w i = 0 := hwt.symm
  have hrem := sub_initialForm_isWeightLT (hcap.pderiv i)
  rw [← pderiv_initialForm,hshift] at hrem
  have hneg : IsWeightLE w (-1) (pderiv i P - G) := by
    intro u hu
    have hh := hrem hu
    omega
  have hfull : pderiv i P = G := sub_eq_zero.mp
    (eq_zero_of_nonnegativeWeight_negative_cap w hw (-1) (by decide) _ hneg)
  apply gradient_injective_of_splitRow hJC2 P hdet i s his
  intro j hj
  change pderiv j (pderiv i P) = 0
  rw [hfull]
  exact hG j hj

set_option maxHeartbeats 5000000 in
/-- Integer nonnegative weights admit the standard natural Euler
identity. Keeping the integer cap explicit avoids assumptions on
divisibility of the common restricted weight. -/
theorem rankThree_weightedEuler
    (L : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 ≤ m)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m) :
    (∑ i : Fin 4, (w i).toNat • (X i * pderiv i L)) = m.toNat • L := by
  let v : Fin 4 → ℕ := fun i => (w i).toNat
  have hv (u : Fin 4 →₀ ℕ) :
      ((Finsupp.weight v u : ℕ) : ℤ) = Finsupp.weight w u := by
    simp only [Finsupp.weight_apply,Finsupp.sum,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change ((u i • (w i).toNat : ℕ) : ℤ) = u i • w i
    simp [nsmul_eq_mul,Int.toNat_of_nonneg (hw i)]
  have hnat : MvPolynomial.IsWeightedHomogeneous v L m.toNat := by
    intro u hu
    have he : ((Finsupp.weight v u : ℕ) : ℤ) = (m.toNat : ℤ) := by
      rw [hv,hL hu,Int.toNat_of_nonneg hm]
    exact_mod_cast he
  exact hnat.sum_weight_X_mul_pderiv

set_option maxHeartbeats 5000000 in
/-- Differentiating a relative rational constant in its permitted
coordinate preserves relative constancy. This is proved by
differentiating its reduced numerator-denominator identity, not
by assuming commutation of arbitrary derivations. -/
theorem rankThree_relative_derivative_constant
    (r : E K) (s : Fin 4)
    (hr : ∀ j, j ≠ s → rankThreePartial j r = 0)
    (j : Fin 4) (hj : j ≠ s) :
    rankThreePartial j (rankThreePartial s r) = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let P := IsFractionRing.num (B K) r
  let Q : B K := IsFractionRing.den (B K) r
  have hQ0 : Q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) r)
  have hQf : f Q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hQ0
  have hder : pderiv j P = 0 ∧ pderiv j Q = 0 :=
    rankOnePartial_num_den_independent r s hr j hj
  have hrepr : f P / f Q = r := IsFractionRing.mk'_num_den' (B K) r
  have hmul : r * f Q = f P := by rw [← hrepr,div_mul_cancel₀ _ hQf]
  have hmap (a : Fin 4) (T : B K) : rankThreePartial a (f T) = f (pderiv a T) :=
    rankThreePartial_map a T
  have h1 := congrArg (rankThreePartial (K := K) s) hmul
  change rankThreePartial s (r * f Q) = rankThreePartial s (f P) at h1
  simp only [Derivation.leibniz,smul_eq_mul,hmap] at h1
  have h2 := congrArg (rankThreePartial (K := K) j) h1
  change rankThreePartial j (r * f (pderiv s Q) + f Q * rankThreePartial s r) =
    rankThreePartial j (f (pderiv s P)) at h2
  simp only [map_add,Derivation.leibniz,smul_eq_mul,hmap,hr j hj,
    hder.1,hder.2,map_zero,mul_zero,zero_mul,add_zero,zero_add,
    pderiv_comm_backport j s] at h2
  exact (mul_eq_zero.mp h2).resolve_left hQf


set_option maxHeartbeats 6000000 in
/-- With zero omitted weight and three nonzero restricted diagonals,
the Hessian row ratios also give the actual gradient ratios.
The positive Euler degree permits cancellation of the affine
integration constant. -/
theorem rankThree_zeroWeight_gradient_ratios
    (L : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ j, 0 ≤ w j) (hm : 0 < m)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (s p : Fin 4) (hps : p ≠ s) (hws : w s = 0)
    (hnon : ∀ i, i ≠ s → hessian L i i ≠ 0)
    (hmin : ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p) :
    let f := algebraMap (B K) (E K)
    ∃ r : Fin 4 → E K,
      r s = 0 ∧ r p = 1 ∧
      (∀ i j, i ≠ s → j ≠ s →
        f (hessian L i j) = r i * f (hessian L p j)) ∧
      (∀ i, i ≠ s → f (pderiv i L) = r i * f (pderiv p L)) ∧
      (∀ j, j ≠ s → ∀ i, rankThreePartial j (r i) = 0) := by
  classical
  let f := algebraMap (B K) (E K)
  let A := f (hessian L p p)
  let r : Fin 4 → E K := fun i => if i = s then 0 else f (hessian L i p) / A
  have hp := hnon p hps
  have hA : A ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hp
  have hrs : r s = 0 := by simp [r]
  have hrp : r p = 1 := by
    change (if p = s then 0 else A/A) = 1
    rw [if_neg hps,div_self hA]
  have hmix (i : Fin 4) (his : i ≠ s) : hessian L i p ≠ 0 := by
    intro hz
    have he := hmin p i p i hps his hps his
    rw [hz,mul_zero] at he
    exact (mul_ne_zero hp (hnon i his)) he
  have hwi (i : Fin 4) (his : i ≠ s) : w i = w p := by
    by_cases hip : i = p
    · rw [hip]
    · have he := rankThree_restricted_weightedRatio L w m hw hL s hmin p i
        hps his hip hp (hmix i his)
      rcases he with ⟨_,he⟩ | ⟨he,_⟩
      · exact he
      · omega
  have hrow (i j : Fin 4) (his : i ≠ s) (hjs : j ≠ s) :
      f (hessian L i j) = r i * f (hessian L p j) := by
    have he := congrArg f (hmin p i p j hps his hps hjs)
    simp only [map_mul] at he
    have hr : A * r i = f (hessian L i p) := by
      change A * (if i = s then 0 else f (hessian L i p)/A) = _
      rw [if_neg his,mul_comm,div_mul_cancel₀ _ hA]
    apply mul_left_cancel₀ hA
    change A * f (hessian L i j) = A * (r i * f (hessian L p j))
    rw [← mul_assoc,hr]
    exact he.trans (mul_comm _ _)
  have hconst (j : Fin 4) (hjs : j ≠ s) (i : Fin 4) :
      rankThreePartial j (r i) = 0 := by
    by_cases his : i = s
    · rw [his,hrs,map_zero]
    · by_cases hip : i = p
      · rw [hip,hrp,Derivation.map_one_eq_zero]
      · change rankThreePartial j (if i = s then 0 else f (hessian L i p)/A) = 0
        rw [if_neg his]
        exact rankOneHessian_twoRows_partialRatios_constant L s p i hip hps his hp
          (fun b hb => (hmin p i p b hps his hps hb).trans (mul_comm _ _)) j hjs
  have hbound : 2*w p ≤ m := by
    by_contra hn
    exact hp (eq_zero_of_nonnegativeWeight_negative_cap w hw _ (by omega) _
      (isWeightLE_of_isWeightedHomogeneous (hessian_entry_isWeightedHomogeneous hL p p)))
  let d := m - w p
  have hd : 0 < d := by dsimp [d]; omega
  have hd0 : (d.toNat : E K) ≠ 0 := by
    have hn : d.toNat ≠ 0 := by omega
    exact_mod_cast hn
  have hEuler (i : Fin 4) (his : i ≠ s) :
      (∑ j : Fin 4, ((w j).toNat : E K) *
        (f (X j) * f (hessian L i j))) = (d.toNat : E K) * f (pderiv i L) := by
    have hh : MvPolynomial.IsWeightedHomogeneous w (pderiv i L) d := by
      change MvPolynomial.IsWeightedHomogeneous w (pderiv i L) (m-w p)
      rw [← hwi i his]
      exact pderiv_isWeightedHomogeneous hL i
    have he := congrArg f (rankThree_weightedEuler (pderiv i L) w d hw (le_of_lt hd) hh)
    change f (∑ j : Fin 4, (w j).toNat • (X j * pderiv j (pderiv i L))) =
      f (d.toNat • pderiv i L) at he
    simp only [nsmul_eq_mul,map_sum,map_mul,map_natCast] at he
    exact he
  have hgrad (i : Fin 4) (his : i ≠ s) :
      f (pderiv i L) = r i * f (pderiv p L) := by
    apply mul_left_cancel₀ hd0
    calc
      (d.toNat : E K) * f (pderiv i L) =
          ∑ j : Fin 4, ((w j).toNat : E K) *
            (f (X j) * f (hessian L i j)) := (hEuler i his).symm
      _ = r i * ∑ j : Fin 4, ((w j).toNat : E K) *
            (f (X j) * f (hessian L p j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hjs : j = s
        · subst j
          simp [hws]
        · rw [hrow i j his hjs]
          ring
      _ = (d.toNat : E K) * (r i * f (pderiv p L)) := by
        rw [hEuler p hps]
        ring
  exact ⟨r,hrs,hrp,hrow,hgrad,hconst⟩

set_option maxHeartbeats 6000000 in
/-- The normalized corank-one kernel is independent of every
non-omitted variable once the restricted gradient ratios are
relative constants. Both the restricted Hessian row and the
omitted mixed row are controlled by the ratio and its derivative. -/
theorem rankThree_kernel_relative_of_gradient_ratios
    (L : B K) (s p l : Fin 4) (hps : p ≠ s)
    (hp : hessian L p p ≠ 0) (hreg : (hessian L).adjugate l l ≠ 0)
    (V : Fin 4 → E K) (hVs : V s = 0) (hVl : V l = 1)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (r : Fin 4 → E K) (hrs : r s = 0)
    (hrows : ∀ i j, i ≠ s → j ≠ s →
      algebraMap (B K) (E K) (hessian L i j) =
        r i * algebraMap (B K) (E K) (hessian L p j))
    (hgrad : ∀ i, i ≠ s → algebraMap (B K) (E K) (pderiv i L) =
      r i * algebraMap (B K) (E K) (pderiv p L))
    (hconst : ∀ j, j ≠ s → ∀ i, rankThreePartial j (r i) = 0) :
    ∀ j, j ≠ s → ∀ i, rankThreePartial j (V i) = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  let G := f (pderiv p L)
  let R : Fin 4 → E K := fun i => rankThreePartial s (r i)
  have hA : H p p ≠ 0 := by
    change f (hessian L p p) ≠ 0
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hp
  have hG : G ≠ 0 := by
    intro hz
    have he := IsFractionRing.injective (B K) (E K) (show f (pderiv p L) = f 0 by simpa only [map_zero] using hz)
    apply hp
    change pderiv p (pderiv p L) = 0
    rw [he,map_zero]
  have hs (i j : Fin 4) : H i j = H j i := by
    change f (hessian L i j) = f (hessian L j i)
    rw [show hessian L i j = hessian L j i from pderiv_comm_backport _ _ _]
  have hrow (i j : Fin 4) (his : i ≠ s) (hjs : j ≠ s) :
      H i j = r j * H i p := by
    rw [hs i j]
    change f (hessian L j i) = r j * H i p
    rw [hrows j i hjs his,hs i p]
    rfl
  have hmix (i : Fin 4) (his : i ≠ s) :
      H s i = r i * H s p + G * R i := by
    have he := congrArg (rankThreePartial (K := K) s) (hgrad i his)
    change rankThreePartial s (f (pderiv i L)) =
      rankThreePartial s (r i * f (pderiv p L)) at he
    have hmap (T : B K) : rankThreePartial s (f T) = f (pderiv s T) :=
      rankThreePartial_map s T
    simp only [Derivation.leibniz,smul_eq_mul,hmap] at he
    change H i s = r i * H p s + G * R i at he
    rw [hs i s,hs p s] at he
    exact he
  have hnormal (W : Fin 4 → E K) (hWs : W s = 0) (i : Fin 4) (his : i ≠ s) :
      (∑ j : Fin 4, H i j * W j) = H i p * ∑ j : Fin 4, r j * W j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjs : j = s
    · rw [hjs,hWs,mul_zero,mul_zero,mul_zero]
    · rw [hrow i j his hjs]
      ring
  have hmixed (W : Fin 4 → E K) (hWs : W s = 0) :
      (∑ j : Fin 4, H s j * W j) =
        H s p * (∑ j : Fin 4, r j * W j) + G * (∑ j : Fin 4, R j * W j) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjs : j = s
    · subst j
      simp [hWs]
    · rw [hmix j hjs]
      ring
  have hrv : ∑ j : Fin 4, r j * V j = 0 := by
    have he : ∑ j : Fin 4, H p j * V j = 0 := congrFun hV p
    rw [hnormal V hVs p hps] at he
    exact (mul_eq_zero.mp he).resolve_left hA
  have hRv : ∑ j : Fin 4, R j * V j = 0 := by
    have he : ∑ j : Fin 4, H s j * V j = 0 := congrFun hV s
    rw [hmixed V hVs,hrv,mul_zero,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hG
  have hRconst (j : Fin 4) (hj : j ≠ s) (i : Fin 4) :
      rankThreePartial j (R i) = 0 :=
    rankThree_relative_derivative_constant (r i) s (fun a ha => hconst a ha i) j hj
  have hregH : H.adjugate l l ≠ 0 := by
    intro hz
    apply hreg
    apply IsFractionRing.injective (B K) (E K)
    change (f.mapMatrix (hessian L)).adjugate l l = 0 at hz
    rw [← f.map_adjugate] at hz
    simpa only [map_zero] using hz
  intro j hj
  let W : Fin 4 → E K := fun i => rankThreePartial j (V i)
  have hWs : W s = 0 := by change rankThreePartial j (V s) = 0; rw [hVs,map_zero]
  have hWl : W l = 0 := by change rankThreePartial j (V l) = 0; rw [hVl,Derivation.map_one_eq_zero]
  have hrW : ∑ i : Fin 4, r i * W i = 0 := by
    have he := congrArg (rankThreePartial (K := K) j) hrv
    change rankThreePartial j (∑ i : Fin 4, r i * V i) = rankThreePartial j 0 at he
    simpa only [map_sum,map_zero,Derivation.leibniz,smul_eq_mul,hconst j hj,mul_zero,add_zero] using he
  have hRW : ∑ i : Fin 4, R i * W i = 0 := by
    have he := congrArg (rankThreePartial (K := K) j) hRv
    change rankThreePartial j (∑ i : Fin 4, R i * V i) = rankThreePartial j 0 at he
    simpa only [map_sum,map_zero,Derivation.leibniz,smul_eq_mul,hRconst j hj,mul_zero,add_zero] using he
  have hHW : H *ᵥ W = 0 := by
    funext i
    change (∑ a : Fin 4, H i a * W a) = 0
    by_cases his : i = s
    · rw [his,hmixed W hWs,hrW,hRW,mul_zero,mul_zero,add_zero]
    · rw [hnormal W hWs i his,hrW,mul_zero]
  have hW0 : W = 0 := by
    by_contra hn
    exact hregH (adjugate_entry_zero_of_nonzero_kernel_coordinate_zero H W hHW hn l l hWl)
  intro i
  exact congrFun hW0 i


set_option maxHeartbeats 6000000 in
/-- At zero omitted weight, a vanishing restricted diagonal gives
a full-source split row; otherwise Euler ratios force the normalized
velocity to depend on at most the omitted coordinate. -/
theorem counterexample_rankThree_no_rankTwoVelocity_zeroWeight
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hminor : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p)
    (hws : w (l.succAbove a) = 0) :
    False := by
  classical
  let s := l.succAbove a
  let L := initialForm w m P
  have hmin := rankThree_rankTwoVelocity_restrictedMinors_zero L l a V hVl hVk
    hreg hV hminor
  have hnon (i : Fin 4) (his : i ≠ s) : hessian L i i ≠ 0 := by
    intro hz
    exact hnoninj (globalWeightOptimum_rankThree_zeroWeight_zeroRow_terminal hJC2
      P w m hw hm hcap hclock hopt hdet s i his hws hmin hz)
  let p := s.succAbove 0
  have hps : p ≠ s := Fin.succAbove_ne _ _
  obtain ⟨r,hrs,hrp,hrows,hgrad,hconst⟩ :=
    rankThree_zeroWeight_gradient_ratios L w m hw hm
      (initialForm_isWeightedHomogeneous w m P) s p hps hws hnon hmin
  have hrel := rankThree_kernel_relative_of_gradient_ratios L s p l hps
    (hnon p hps) hreg V hVk hVl hV r hrs hrows hgrad hconst
  let J := rankThreeComplementJacobian l V
  have hcol (b c : Fin 3) (hc : c ≠ a) : J b c = 0 := by
    have hcs : l.succAbove c ≠ s := by
      intro he
      exact hc (Fin.succAbove_right_injective he)
    exact hrel (l.succAbove c) hcs (l.succAbove b)
  obtain ⟨i,j,b,c,hbad⟩ := hminor
  apply hbad
  change J i b * J j c = J i c * J j b
  by_cases hb : b = a
  · by_cases hc : c = a
    · rw [hb,hc]
    · rw [hcol j c hc,hcol i c hc,mul_zero,zero_mul]
  · rw [hcol i b hb,hcol j b hb,zero_mul,mul_zero]

/-- Rank-two velocity is excluded for every nonnegative omitted
weight in a genuine extremal counterexample. -/
theorem counterexample_rankThree_no_rankTwoVelocity
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hminor : let J := rankThreeComplementJacobian l V
      ∃ i j p q : Fin 3, J i p * J j q ≠ J i q * J j p) :
    False := by
  by_cases hz : w (l.succAbove a) = 0
  · exact counterexample_rankThree_no_rankTwoVelocity_zeroWeight hJC2 P w m hw hm
      hcap hclock hopt hdet hnoninj l a V hVl hVk hreg hV hminor hz
  · exact globalWeightOptimum_rankThree_no_rankTwoVelocity_positiveWeight P w m hw hm
      hcap hclock hopt hdet l a V hVl hVk hreg hV hminor
      (lt_of_le_of_ne (hw _) (Ne.symm hz))


section RankOneFrontier

/-- A nonzero complementary differential with all two-minors zero
is an exact rank-one factorization. Cube-zero then implies square-zero. -/
theorem rankThree_rankOne_factor_square_zero
    (J : Matrix (Fin 3) (Fin 3) (E K))
    (hJ : J ≠ 0) (h3 : J ^ 3 = 0)
    (hm : ∀ i j p q : Fin 3, J i p * J j q = J i q * J j p) :
    ∃ u v : Fin 3 → E K, u ≠ 0 ∧ v ≠ 0 ∧
      (∀ i j, J i j = u i * v j) ∧ v ⬝ᵥ u = 0 ∧ J * J = 0 := by
  classical
  have hex : ∃ i j, J i j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hJ
    ext i j
    exact hn i j
  obtain ⟨a,b,hab⟩ := hex
  let u : Fin 3 → E K := fun i => J i b
  let v : Fin 3 → E K := fun j => J a j / J a b
  have huv (i j : Fin 3) : J i j = u i * v j := by
    change J i j = J i b * (J a j / J a b)
    rw [← mul_div_assoc]
    exact (eq_div_iff hab).mpr (hm i a j b)
  have hu : u ≠ 0 := fun hz => hab (congrFun hz a)
  have hvb : v b = 1 := div_self hab
  have hv : v ≠ 0 := by
    intro hz
    rw [hz] at hvb
    exact zero_ne_one hvb
  have hdot := rankOne_dot_zero_of_cube_zero J u v huv h3 b (by rw [hvb]; exact one_ne_zero)
  exact ⟨u,v,hu,hv,huv,hdot,by rw [rankOne_mul_self_eq_smul J u v huv,hdot,zero_smul]⟩

/-- The actual remaining chart has a nonzero square-zero rank-one
velocity differential; its Hessian symmetrizer is the actual
complementary Hessian, not an auxiliary matrix. -/
theorem counterexample_rankThree_rankOne_frontier
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    let J := rankThreeComplementJacobian l V
    let H := ((hessian (initialForm w m P)).submatrix l.succAbove l.succAbove).map
      (algebraMap (B K) (E K))
    J ≠ 0 ∧ H * J = J.transpose * H ∧
      ∃ u v : Fin 3 → E K, u ≠ 0 ∧ v ≠ 0 ∧ u a = 0 ∧
        (∀ i j, J i j = u i * v j) ∧ v ⬝ᵥ u = 0 ∧ J * J = 0 := by
  classical
  let L := initialForm w m P
  let J := rankThreeComplementJacobian l V
  let H := ((hessian L).submatrix l.succAbove l.succAbove).map (algebraMap (B K) (E K))
  have hJ : J ≠ 0 :=
    globalWeightOptimum_rankThree_complementJacobian_ne_zero P w m hw hm hcap
      hclock hopt hdet l hreg V hVl hV
  have h3 : J ^ 3 = 0 := rankThree_complement_cube_zero L l V hVl hreg hV
  have hmin (i j p q : Fin 3) : J i p * J j q = J i q * J j p := by
    by_contra hn
    exact counterexample_rankThree_no_rankTwoVelocity hJC2 P w m hw hm hcap
      hclock hopt hdet hnoninj l a V hVl hVk hreg hV ⟨i,j,p,q,hn⟩
  obtain ⟨u,v,hu,hv,hfac,hdot,hsq⟩ :=
    rankThree_rankOne_factor_square_zero J hJ h3 hmin
  have hua : u a = 0 := by
    by_contra hn
    apply hv
    funext j
    have he := rankThree_complement_zeroRow l V a hVk j
    change J a j = 0 at he
    rw [hfac] at he
    exact (mul_eq_zero.mp he).resolve_left hn
  exact ⟨hJ,rankThree_complement_selfAdjoint L l V hVl hV,
    u,v,hu,hv,hua,hfac,hdot,hsq⟩

/-- Every image direction of a square-zero self-adjoint differential
is isotropic. This applies over the original fraction field. -/
theorem rankThree_velocity_column_isotropic
    (H J : Matrix (Fin 3) (Fin 3) (E K))
    (hs : H * J = J.transpose * H) (h2 : J * J = 0)
    (j : Fin 3) :
    ∑ a : Fin 3, ∑ b : Fin 3, J a j * H a b * J b j = 0 := by
  have he : J.transpose * H * J = 0 := by
    rw [← hs,Matrix.mul_assoc,h2,Matrix.mul_zero]
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) (E K) => M j j) he
  change (∑ b : Fin 3, (∑ a : Fin 3, J a j * H a b) * J b j) = 0 at h
  simp only [Finset.sum_mul] at h
  rw [Finset.sum_comm]
  exact h

end RankOneFrontier


set_option maxHeartbeats 6000000 in
/-- A normalized kernel taking values in a fixed affine line
cannot occur at a genuine global optimum. Its direction is
isotropic by square-zero transport; adjoining the affine offset
produces a constant isotropic plane of the leading Hessian. -/
theorem globalWeightOptimum_rankThree_no_affineKernelLine
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (l : Fin 4) (V : Fin 4 → E K)
    (hVl : V l = 1)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hsq : let J := rankThreeComplementJacobian l V; J * J = 0)
    (d e : Fin 4 → K) (hdl : d l = 1) (hel : e l = 0) (he0 : e ≠ 0)
    (t : E K) (hline : ∀ i, V i = algebraMap K (E K) (d i) +
      t * algebraMap K (E K) (e i)) :
    False := by
  classical
  let L := initialForm w m P
  let f := algebraMap (B K) (E K)
  let g := algebraMap K (E K)
  let H := ((hessian L).submatrix l.succAbove l.succAbove).map f
  let J := rankThreeComplementJacobian l V
  have hJ : J ≠ 0 :=
    globalWeightOptimum_rankThree_complementJacobian_ne_zero P w m hw hm hcap
      hclock hopt hdet l hreg V hVl hV
  have hfac (a b : Fin 3) :
      J a b = rankThreePartial (l.succAbove b) t * g (e (l.succAbove a)) := by
    change rankThreePartial (l.succAbove b) (V (l.succAbove a)) = _
    rw [hline]
    change rankThreePartial (l.succAbove b)
      (algebraMap K (E K) (d (l.succAbove a)) + t * algebraMap K (E K) (e (l.succAbove a))) =
      rankThreePartial (l.succAbove b) t * algebraMap K (E K) (e (l.succAbove a))
    simp only [map_add,Derivation.leibniz,smul_eq_mul,Derivation.map_algebraMap,mul_zero,add_zero,zero_add]
    exact mul_comm _ _
  have hsome : ∃ b : Fin 3, rankThreePartial (l.succAbove b) t ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hJ
    ext a b
    rw [hfac,hn b,zero_mul]
    rfl
  obtain ⟨b,hb⟩ := hsome
  let z := rankThreePartial (l.succAbove b) t
  have hz : z ≠ 0 := hb
  have hiso := rankThree_velocity_column_isotropic H J
    (rankThree_complement_selfAdjoint L l V hVl hV) hsq b
  have hC (c : K) : f (MvPolynomial.C c) = g c :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes c
  have hee : extremalHessianPair L e e = 0 := by
    apply IsFractionRing.injective (B K) (E K)
    unfold extremalHessianPair
    change f (∑ i : Fin 4, ∑ j : Fin 4,
      MvPolynomial.C (e i) * hessian L i j * MvPolynomial.C (e j)) = f 0
    simp only [map_sum,map_mul,hC,map_zero]
    rw [Fin.sum_univ_succAbove _ l]
    simp only [hel,map_zero,zero_mul,Finset.sum_const_zero,zero_add]
    have hinner (i : Fin 3) :
        (∑ j : Fin 4, g (e (l.succAbove i)) * f (hessian L (l.succAbove i) j) * g (e j)) =
        ∑ j : Fin 3, g (e (l.succAbove i)) * H i j * g (e (l.succAbove j)) := by
      rw [Fin.sum_univ_succAbove _ l]
      simp only [hel,map_zero,mul_zero,zero_add]
      rfl
    simp only [hinner]
    have he : z * z * (∑ i : Fin 3, ∑ j : Fin 3,
        g (e (l.succAbove i)) * H i j * g (e (l.succAbove j))) = 0 := by
      calc
        _ = ∑ i : Fin 3, ∑ j : Fin 3, J i b * H i j * J j b := by
          simp only [Finset.mul_sum,hfac]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change z * z * (g (e (l.succAbove i)) * H i j * g (e (l.succAbove j))) =
            (z * g (e (l.succAbove i))) * H i j * (z * g (e (l.succAbove j)))
          ring
        _ = 0 := hiso
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hz hz)
  have hpair (x y : Fin 4 → K) :
      f (extremalHessianPair L x y) =
        ∑ i : Fin 4, ∑ j : Fin 4, g (x i) * f (hessian L i j) * g (y j) := by
    unfold extremalHessianPair
    simp only [map_sum,map_mul,hC]
  have hk (x : Fin 4 → K) :
      f (extremalHessianPair L x d) + t * f (extremalHessianPair L x e) = 0 := by
    rw [hpair,hpair,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    have hi : (∑ j : Fin 4, f (hessian L i j) * V j) = 0 := congrFun hV i
    have hsum : (∑ j : Fin 4,
        (g (x i) * f (hessian L i j) * g (d j) +
        t * (g (x i) * f (hessian L i j) * g (e j)))) =
          g (x i) * (∑ j : Fin 4, f (hessian L i j) * V j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hline]
      ring
    rw [hsum,hi,mul_zero]
  have hed : extremalHessianPair L e d = 0 := by
    apply IsFractionRing.injective (B K) (E K)
    have he := hk e
    rw [hee,map_zero,mul_zero,add_zero] at he
    simpa only [map_zero] using he
  have hde : extremalHessianPair L d e = 0 := by
    rw [← hed]
    unfold extremalHessianPair
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show hessian L j i = hessian L i j from pderiv_comm_backport _ _ _]
    ring
  have hdd : extremalHessianPair L d d = 0 := by
    apply IsFractionRing.injective (B K) (E K)
    have he := hk d
    rw [hde,map_zero,mul_zero,add_zero] at he
    simpa only [map_zero] using he
  let U := Submodule.span K ({d,e} : Set (Fin 4 → K))
  have hd0 : d ≠ 0 := by
    intro h
    rw [h] at hdl
    exact zero_ne_one hdl
  have hspan (c : K) : e ≠ c • d := by
    intro he
    have hh := congrFun he l
    change e l = c * d l at hh
    rw [hel,hdl,mul_one] at hh
    apply he0
    rw [he,← hh,zero_smul]
  exact globalWeightOptimum_no_constant_isotropicPlane P w m hw hm hcap hclock hopt
    U d e (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    hd0 hspan (extremalHessianPair_span_pair_zero L d e hdd hde hed hee)


set_option maxHeartbeats 5000000 in
/-- A second derivative vanishing along an actual straight rational
direction gives an affine polynomial restriction. In particular
the linear coefficient is the actual first directional derivative. -/
theorem rankThree_lineEval_affine_of_derivation_sq_zero
    (D : Derivation K (E K) (E K)) (z W : Fin 4 → E K)
    (hz : ∀ i, D (z i) = W i) (hW : ∀ i, D (W i) = 0)
    (P : B K) (hP : D (D (MvPolynomial.aeval z P)) = 0) :
    lineEval z W P = _root_.Polynomial.C (MvPolynomial.aeval z P) +
      _root_.Polynomial.C (D (MvPolynomial.aeval z P)) * _root_.Polynomial.X := by
  classical
  let A := lineEval (K := K) z W
  have hder : (A P).derivative = coeffDeriv D (A P) := by
    clear hP
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [show A (MvPolynomial.C a) = _root_.Polynomial.C (algebraMap K (E K) a) by
        simp [A,lineEval,IsScalarTower.algebraMap_apply K (E K) (_root_.Polynomial (E K)),
          _root_.Polynomial.algebraMap_eq]]
      ext n
      simp [coeff_coeffDeriv,_root_.Polynomial.coeff_C,apply_ite D,Derivation.map_algebraMap]
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp =>
      have hX : A (MvPolynomial.X i) =
          _root_.Polynomial.C (z i) + _root_.Polynomial.C (W i) * _root_.Polynomial.X := by
        simp [A,lineEval]
      have hDX : (A (MvPolynomial.X i)).derivative = coeffDeriv D (A (MvPolynomial.X i)) := by
        rw [hX]
        ext n
        simp only [map_add,_root_.Polynomial.derivative_C,_root_.Polynomial.derivative_mul,
          _root_.Polynomial.derivative_X,zero_mul,mul_one,zero_add,add_zero,coeff_coeffDeriv,
          _root_.Polynomial.coeff_add,_root_.Polynomial.coeff_C_mul_X,_root_.Polynomial.coeff_C,
          apply_ite D,map_add,map_zero,hz,hW,ite_self,add_zero]
      simp only [map_mul,_root_.Polynomial.derivative_mul,Derivation.leibniz,smul_eq_mul,hp,hDX]
      ring
  have hev : (_root_.Polynomial.constantCoeff.comp A.toRingHom) =
      (MvPolynomial.aeval z : B K →ₐ[K] E K).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [A,lineEval,IsScalarTower.algebraMap_apply K (E K) (_root_.Polynomial (E K)),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      simp [A,lineEval]
  have h0 : (A P).coeff 0 = MvPolynomial.aeval z P := RingHom.congr_fun hev P
  have h1 : (A P).coeff 1 = D (MvPolynomial.aeval z P) := by
    have h := congrArg (fun f : _root_.Polynomial (E K) => f.coeff 0) hder
    simpa [_root_.Polynomial.coeff_derivative,h0] using h
  have hzero (n : ℕ) : (A P).coeff (n+2) = 0 := by
    induction n with
    | zero =>
      have h := congrArg (fun f : _root_.Polynomial (E K) => f.coeff 1) hder
      simp only [_root_.Polynomial.coeff_derivative,coeff_coeffDeriv,h1,hP] at h
      exact (mul_eq_zero.mp h).resolve_right (by norm_num)
    | succ n ih =>
      have h := congrArg (fun f : _root_.Polynomial (E K) => f.coeff (n+2)) hder
      simp only [_root_.Polynomial.coeff_derivative,coeff_coeffDeriv,ih,map_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast Nat.succ_ne_zero (n+2))
  change A P = _
  apply _root_.Polynomial.ext
  intro n
  rcases n with _ | n
  · rw [h0,_root_.Polynomial.coeff_add]
    simp only [_root_.Polynomial.coeff_C,_root_.Polynomial.coeff_C_mul_X,
      if_true,if_pos rfl,if_neg Nat.zero_ne_one,add_zero]
  rcases n with _ | n
  · rw [h1,_root_.Polynomial.coeff_add]
    simp only [_root_.Polynomial.coeff_C,_root_.Polynomial.coeff_C_mul_X,
      if_true,if_neg Nat.one_ne_zero,if_pos rfl,zero_add]
  · change (A P).coeff (n+2) = _
    have hn0 : n+2 ≠ 0 := by omega
    have hn1 : n+2 ≠ 1 := by omega
    rw [hzero n,_root_.Polynomial.coeff_add]
    simp only [_root_.Polynomial.coeff_C,_root_.Polynomial.coeff_C_mul_X,
      if_neg hn0,if_neg hn1,add_zero]

/-- Actual partial derivatives of the generic point in the
four-variable fraction field. -/
theorem rankThreePartial_X (i j : Fin 4) :
    rankThreePartial (K := K) i (algebraMap (B K) (E K) (X j)) =
      if j = i then 1 else 0 := by
  rw [rankThreePartial_map]
  by_cases h : j = i
  · subst j
    simp
  · simp [h,pderiv_X_of_ne h]

/-- Differentiate the polynomial restriction along a rational
direction with respect to one original source coordinate. -/
theorem rankThree_lineEval_partial
    (W : Fin 4 → E K) (P : B K) (j : Fin 4) :
    coeffDeriv (rankThreePartial j)
      (lineEval (fun i => algebraMap (B K) (E K) (X i)) W P) =
      ∑ i : Fin 4, lineEval (fun a => algebraMap (B K) (E K) (X a)) W (pderiv i P) *
        (_root_.Polynomial.C (if i = j then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial j (W i))) := by
  classical
  let z : Fin 4 → _root_.Polynomial (E K) := fun i =>
    _root_.Polynomial.C (algebraMap (B K) (E K) (X i)) +
      _root_.Polynomial.C (W i) * _root_.Polynomial.X
  have he : (lineEval (K := K) (fun i => algebraMap (B K) (E K) (X i)) W :
      B K →ₐ[K] _root_.Polynomial (E K)) =
      MvPolynomial.aeval z := rfl
  have hd (i : Fin 4) : coeffDeriv (rankThreePartial j) (z i) =
      _root_.Polynomial.C (if i = j then 1 else 0) +
        _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial j (W i)) := by
    simp only [z,map_add,coeffDeriv_C,Derivation.leibniz,smul_eq_mul,
      coeffDeriv_X,mul_zero,zero_add,rankThreePartial_X]
  rw [he,derivation_aeval]
  simp only [hd]

set_option maxHeartbeats 6000000 in
/-- A moving isotropic tangent slope obeying its straight-line
transport equation either is constant in both active variables
or makes their principal Hessian minor zero. The proof specializes
only polynomial line evaluations, at the time where the derivative
of the line with respect to the second active coordinate vanishes. -/
theorem rankThree_isotropicSlope_activeMinor_zero
    (L : B K) (i k : Fin 4) (hik : i ≠ k) (r : E K)
    (hr : rankThreePartial i r + r * rankThreePartial k r = 0)
    (hvar : rankThreePartial k r ≠ 0)
    (hiso : let f := algebraMap (B K) (E K)
      f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0) :
    rankTwoPrincipalPivot (hessian L) i k = 0 := by
  classical
  let f := algebraMap (B K) (E K)
  let x : Fin 4 → E K := fun j => f (X j)
  let W : Fin 4 → E K := fun j =>
    (if j = i then 1 else 0) + r * (if j = k then 1 else 0)
  let D : Derivation K (E K) (E K) := rankThreePartial i + r • rankThreePartial k
  have hD (a : E K) : D a = rankThreePartial i a + r * rankThreePartial k a := by
    simp only [D,Derivation.add_apply,Derivation.smul_apply,smul_eq_mul]
  have hDr : D r = 0 := by rw [hD,hr]
  have hDx (j : Fin 4) : D (x j) = W j := by
    rw [hD]
    change rankThreePartial i (f (X j)) + r * rankThreePartial k (f (X j)) = _
    rw [rankThreePartial_X,rankThreePartial_X]
  have hWi : W i = 1 := by simp [W,hik]
  have hWk : W k = r := by simp [W,Ne.symm hik]
  have hWother (j : Fin 4) (hji : j ≠ i) (hjk : j ≠ k) : W j = 0 := by
    simp [W,hji,hjk]
  have hDW (j : Fin 4) : D (W j) = 0 := by
    by_cases hji : j = i
    · rw [hji,hWi,Derivation.map_one_eq_zero]
    · by_cases hjk : j = k
      · rw [hjk,hWk,hDr]
      · rw [hWother j hji hjk,map_zero]
  have hx : (MvPolynomial.aeval x : B K →ₐ[K] E K) =
      IsScalarTower.toAlgHom K (B K) (E K) := by
    apply MvPolynomial.algHom_ext
    intro j
    exact MvPolynomial.aeval_X _ j
  have hfirst : D (f L) = f (pderiv i L) + r * f (pderiv k L) := by
    rw [hD,rankThreePartial_map,rankThreePartial_map]
  have hmap (a : Fin 4) (Q : B K) : rankThreePartial a (f Q) = f (pderiv a Q) :=
    rankThreePartial_map a Q
  have hsym : hessian L k i = hessian L i k := pderiv_comm_backport _ _ _
  have hsecond : D (D (f L)) = 0 := by
    simp only [hfirst,map_add,Derivation.leibniz,smul_eq_mul,hDr,mul_zero,add_zero]
    simp only [hD,hmap]
    change (f (hessian L i i) + r*f (hessian L i k)) +
      r*(f (hessian L k i) + r*f (hessian L k k)) = 0
    rw [hsym]
    change f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0 at hiso
    linear_combination hiso
  have hline := rankThree_lineEval_affine_of_derivation_sq_zero D x W hDx hDW L
    (by rw [hx]; exact hsecond)
  rw [hx] at hline
  change lineEval x W L = _root_.Polynomial.C (f L) +
    _root_.Polynomial.C (D (f L)) * _root_.Polynomial.X at hline
  let A := lineEval (K := K) x W
  have hchain := rankThree_lineEval_partial W L k
  change coeffDeriv (rankThreePartial k) (A L) = _ at hchain
  rw [show A L = _ from hline] at hchain
  simp only [map_add,coeffDeriv_C,Derivation.leibniz,smul_eq_mul,
    coeffDeriv_X,mul_zero,zero_add,hmap] at hchain
  let t := -(rankThreePartial k r)⁻¹
  let ev := _root_.Polynomial.evalRingHom t
  have hzero (j : Fin 4) :
      ev (_root_.Polynomial.C (if j = k then 1 else 0) +
        _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial k (W j))) = 0 := by
    change (_root_.Polynomial.C (if j = k then 1 else 0) +
      _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial k (W j))).eval t = 0
    rw [_root_.Polynomial.eval_add,_root_.Polynomial.eval_mul,
      _root_.Polynomial.eval_X,_root_.Polynomial.eval_C,_root_.Polynomial.eval_C]
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl,hWk]
      change 1 + (-(rankThreePartial k r)⁻¹)*rankThreePartial k r = 0
      rw [neg_mul,inv_mul_cancel₀ hvar,add_neg_cancel]
    · rw [if_neg hj]
      by_cases hji : j = i
      · rw [hji,hWi,Derivation.map_one_eq_zero,mul_zero,zero_add]
      · rw [hWother j hji hj,map_zero,mul_zero,zero_add]
  have hc : _root_.Polynomial.C (f (pderiv k L)) +
      _root_.Polynomial.C (rankThreePartial k (D (f L))) * _root_.Polynomial.X =
      ∑ j : Fin 4, A (pderiv j L) *
        (_root_.Polynomial.C (if j = k then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial k (W j))) := by
    rw [mul_comm (_root_.Polynomial.C (rankThreePartial k (D (f L))))]
    exact hchain
  have he := congrArg (fun Q : _root_.Polynomial (E K) => ev Q) hc
  change ev (_root_.Polynomial.C (f (pderiv k L)) +
      _root_.Polynomial.C (rankThreePartial k (D (f L))) * _root_.Polynomial.X) =
      ev (∑ j : Fin 4, A (pderiv j L) *
        (_root_.Polynomial.C (if j = k then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial k (W j)))) at he
  have hright : ev (∑ j : Fin 4, A (pderiv j L) *
        (_root_.Polynomial.C (if j = k then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C (rankThreePartial k (W j)))) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_mul,hzero j,mul_zero]
  rw [hright] at he
  change (_root_.Polynomial.C (f (pderiv k L)) +
      _root_.Polynomial.C (rankThreePartial k (D (f L))) * _root_.Polynomial.X).eval t = 0 at he
  rw [_root_.Polynomial.eval_add,_root_.Polynomial.eval_mul,_root_.Polynomial.eval_C,
    _root_.Polynomial.eval_C,_root_.Polynomial.eval_X] at he
  have hdiff : rankThreePartial k (D (f L)) =
      f (hessian L i k) + r * f (hessian L k k) +
        rankThreePartial k r * f (pderiv k L) := by
    simp only [hfirst,map_add,Derivation.leibniz,smul_eq_mul,hmap]
    change f (hessian L i k) + (r * f (hessian L k k) +
      f (pderiv k L) * rankThreePartial k r) = _
    ring
  rw [hdiff] at he
  change f (pderiv k L) + _ * (-(rankThreePartial k r)⁻¹) = 0 at he
  have hmix : f (hessian L i k) + r*f (hessian L k k) = 0 := by
    field_simp [hvar] at he
    linear_combination -he
  have hdiag : f (hessian L i i) + r*f (hessian L i k) = 0 := by
    change f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0 at hiso
    linear_combination hiso - r*hmix
  apply IsFractionRing.injective (B K) (E K)
  unfold rankTwoPrincipalPivot
  rw [map_sub,map_mul,map_mul,map_zero,hsym]
  linear_combination f (hessian L k k)*hdiag - f (hessian L i k)*hmix


set_option maxHeartbeats 4000000 in
/-- The rational partials commute on the original fraction field. -/
theorem rankThreePartial_comm (i j : Fin 4) (r : E K) :
    rankThreePartial i (rankThreePartial j r) =
      rankThreePartial j (rankThreePartial i r) := by
  classical
  let f := algebraMap (B K) (E K)
  let p := IsFractionRing.num (B K) r
  let q : B K := IsFractionRing.den (B K) r
  have hq : q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) r)
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hrepr : f p / f q = r := IsFractionRing.mk'_num_den' (B K) r
  have hmul : r * f q = f p := by rw [← hrepr,div_mul_cancel₀ _ hqf]
  have hmap (a : Fin 4) (P : B K) : rankThreePartial a (f P) = f (pderiv a P) :=
    rankThreePartial_map a P
  have hdiff (a : Fin 4) :
      r * f (pderiv a q) + f q * rankThreePartial a r = f (pderiv a p) := by
    have h := congrArg (rankThreePartial (K := K) a) hmul
    change rankThreePartial a (r * f q) = rankThreePartial a (f p) at h
    simpa only [Derivation.leibniz,smul_eq_mul,hmap] using h
  have hi := congrArg (rankThreePartial (K := K) i) (hdiff j)
  have hj := congrArg (rankThreePartial (K := K) j) (hdiff i)
  change rankThreePartial i (r * f (pderiv j q) + f q * rankThreePartial j r) =
    rankThreePartial i (f (pderiv j p)) at hi
  change rankThreePartial j (r * f (pderiv i q) + f q * rankThreePartial i r) =
    rankThreePartial j (f (pderiv i p)) at hj
  simp only [map_add,Derivation.leibniz,smul_eq_mul,hmap] at hi hj
  rw [pderiv_comm_backport i j q,pderiv_comm_backport i j p] at hi
  apply mul_left_cancel₀ hqf
  linear_combination hi - hj

/-- A proportional differential has the same level directions
as its rational slope. -/
theorem rankThree_proportionalDifferential_slope
    (A B r : E K)
    (hrel : ∀ j : Fin 4, rankThreePartial j B = r * rankThreePartial j A)
    (i j : Fin 4) :
    rankThreePartial i r * rankThreePartial j A =
      rankThreePartial j r * rankThreePartial i A := by
  have hi := congrArg (rankThreePartial (K := K) i) (hrel j)
  have hj := congrArg (rankThreePartial (K := K) j) (hrel i)
  change rankThreePartial i (rankThreePartial j B) =
    rankThreePartial i (r * rankThreePartial j A) at hi
  change rankThreePartial j (rankThreePartial i B) =
    rankThreePartial j (r * rankThreePartial i A) at hj
  simp only [Derivation.leibniz,smul_eq_mul] at hi hj
  rw [rankThreePartial_comm i j A,rankThreePartial_comm i j B] at hi
  linear_combination hj - hi

/-- Trace zero gives the active slope straight-line equation. -/
theorem rankThree_rankOne_slope_transport
    (A B r : E K) (i k : Fin 4)
    (hrel : ∀ j : Fin 4, rankThreePartial j B = r * rankThreePartial j A)
    (htrace : rankThreePartial i A + rankThreePartial k B = 0)
    (hvar : rankThreePartial k A ≠ 0) :
    rankThreePartial i r + r * rankThreePartial k r = 0 := by
  have he := rankThree_proportionalDifferential_slope A B r hrel i k
  rw [hrel k] at htrace
  apply (mul_eq_zero.mp (show
      (rankThreePartial i r + r * rankThreePartial k r) *
        rankThreePartial k A = 0 by
    linear_combination he + rankThreePartial k r * htrace)).resolve_right hvar

/-- At a regular active pivot the isotropic tangent slope must
be constant in both active variables. -/
theorem rankThree_rankOne_regularActiveSlope_constant
    (L : B K) (i k : Fin 4) (hik : i ≠ k)
    (A B₀ r : E K)
    (hrel : ∀ j : Fin 4, rankThreePartial j B₀ = r * rankThreePartial j A)
    (htrace : rankThreePartial i A + rankThreePartial k B₀ = 0)
    (hvar : rankThreePartial k A ≠ 0)
    (hiso : let f := algebraMap (B K) (E K)
      f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0)
    (hreg : rankTwoPrincipalPivot (hessian L) i k ≠ 0) :
    rankThreePartial i r = 0 ∧ rankThreePartial k r = 0 := by
  have ht := rankThree_rankOne_slope_transport A B₀ r i k hrel htrace hvar
  have hk : rankThreePartial k r = 0 := by
    by_contra hn
    exact hreg (rankThree_isotropicSlope_activeMinor_zero L i k hik r ht hn hiso)
  rw [hk,mul_zero,add_zero] at ht
  exact ⟨ht,hk⟩


set_option maxHeartbeats 6000000 in
/-- The positive omitted-weight obstruction needs only the vanishing restricted minors. -/
theorem globalWeightOptimum_rankThree_no_restrictedRankOne_positiveWeight
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (s : Fin 4)
    (hmin : let L := initialForm w m P
      ∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p)
    (hpos : 0 < w s) :
    False := by
  classical
  let L := initialForm w m P
  have hnon (j : Fin 4) (hjs : j ≠ s) : hessian L j j ≠ 0 := by
    intro hj
    obtain ⟨p,i,hps,his,hip,hjp,hji,hcover⟩ :=
      rankThree_remaining_two_coordinates s j hjs
    have hp : hessian L p p ≠ 0 := by
      intro hz
      exact hjp (globalWeightOptimum_rankThree_restricted_atMostOne_zero P w m
        hw hm hcap hclock hopt s j p hjs hps hmin hj hz)
    have hi : hessian L i i ≠ 0 := by
      intro hz
      exact hji (globalWeightOptimum_rankThree_restricted_atMostOne_zero P w m
        hw hm hcap hclock hopt s j i hjs his hmin hj hz)
    exact globalWeightOptimum_rankThree_no_one_zero P w m hw hm hcap hclock hopt hdet
      s p i j hps his hjs hip hjp hji hcover hpos hp hi hj hmin
  have hdistinct (p i : Fin 4) (hps : p ≠ s) (his : i ≠ s) (hip : i ≠ p) :
      w i ≠ w p := by
    intro heq
    obtain ⟨q,j,hqs,hjs,hjq,hiq,hij,hcover⟩ :=
      rankThree_remaining_two_coordinates s i his
    have hpcover : p = q ∨ p = j := by
      rcases hcover p with h | h | h | h
      · exact (hps h).elim
      · exact Or.inl h
      · exact Or.inr h
      · exact (hip h.symm).elim
    rcases hpcover with h | h
    · subst q
      have hcover' (b : Fin 4) : b = s ∨ b = p ∨ b = i ∨ b = j := by
        rcases hcover b with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
      exact globalWeightOptimum_rankThree_no_repeated_nonzero_weights P w m hw hm
        hcap hclock hopt hdet s p i j hps his hjs hip hjq (Ne.symm hij)
        hcover' hpos heq (hnon p hps) (hnon i his) (hnon j hjs) hmin
    · subst j
      have hcover' (b : Fin 4) : b = s ∨ b = p ∨ b = i ∨ b = q := by
        rcases hcover b with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      exact globalWeightOptimum_rankThree_no_repeated_nonzero_weights P w m hw hm
        hcap hclock hopt hdet s p i q hps his hqs hip (Ne.symm hjq) (Ne.symm hiq)
        hcover' hpos heq (hnon p hps) (hnon i his) (hnon q hqs) hmin
  let T := Finset.univ.filter (fun i : Fin 4 => i ≠ s)
  have hT : T.Nonempty :=
    ⟨s.succAbove 0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Fin.succAbove_ne _ _⟩⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image T w hT
  have hps : p ≠ s := (Finset.mem_filter.mp hp).2
  have hsmall (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) : w i < w p :=
    lt_of_le_of_ne (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,his⟩))
      (hdistinct p i hps his hip)
  obtain ⟨i,j,his,hjs,hji,hpi,hpj,hcover⟩ := rankThree_remaining_two_coordinates s p hps
  have hgap (i : Fin 4) (his : i ≠ s) (hip : i ≠ p) : w s ≤ w p - w i := by
    have hmix : hessian L i p ≠ 0 := by
      intro hz
      have he := hmin p i p i hps his hps his
      rw [hz,mul_zero] at he
      exact (mul_ne_zero (hnon p hps) (hnon i his)) he
    rcases rankThree_restricted_weightedRatio L w m hw
      (initialForm_isWeightedHomogeneous w m P) s hmin p i hps his hip
      (hnon p hps) hmix with ⟨hz,_⟩ | ⟨_,n,t,c,e,hc,he,hd,_⟩
    · omega
    · have hprod : 0 < ((t : ℤ)-(n : ℤ))*w s := by rw [← hd]; exact sub_pos.mpr (hsmall i his hip)
      have hdiff : 1 ≤ (t : ℤ)-(n : ℤ) := by
        by_contra hn
        have hn' : (t : ℤ)-(n : ℤ) ≤ 0 := by omega
        exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn' (le_of_lt hpos))) hprod
      rw [hd]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff (le_of_lt hpos)
  have hbound := globalWeightOptimum_rankThree_restricted_no_gain P w m hw hm hcap
    hclock hopt hdet s p hps hpos (hnon p hps) hmin
  have hsums (f : Fin 4 → ℤ) : ∑ a, f a = f s + f i + f j + f p := by
    have hu : (Finset.univ : Finset (Fin 4)) = {s,i,j,p} := by
      ext a
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
      exact hcover a
    rw [hu,Finset.sum_insert,Finset.sum_insert,Finset.sum_insert,Finset.sum_singleton]
    · ring
    · simp [Ne.symm hpj]
    · simp [Ne.symm hji,Ne.symm hpi]
    · simp [Ne.symm his,Ne.symm hjs,Ne.symm hps]
  rw [hsums,hsums] at hbound
  have hcollapse (a : Fin 4) (ha : a ≠ s) :
      rankThreeCollapsedWeight (initialForm w m P) w m s p a = w p := by
    have hn : hessian (initialForm w m P) a a ≠ 0 := hnon a ha
    simp only [rankThreeCollapsedWeight,if_neg ha,if_neg hn]
  have hz : rankThreeCollapsedWeight (initialForm w m P) w m s p s = 0 := by
    simp [rankThreeCollapsedWeight]
  rw [hz,hcollapse i his,hcollapse j hjs,hcollapse p hps] at hbound
  have hi := hgap i his (Ne.symm hpi)
  have hj := hgap j hjs (Ne.symm hpj)
  omega

set_option maxHeartbeats 6000000 in
/-- Rank-one velocity with a regular active pivot is impossible.
The first active image component is chosen nonzero; the other
component may vanish, and no nonzero slope assumption is made. -/
theorem globalWeightOptimum_rankThree_rankOne_regularActive_oriented
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (l s i k : Fin 4)
    (hsl : s ≠ l) (hil : i ≠ l) (hkl : k ≠ l)
    (his : i ≠ s) (hks : k ≠ s) (hik : i ≠ k)
    (hcover : ∀ a : Fin 4, a = s ∨ a = l ∨ a = i ∨ a = k)
    (V : Fin 4 → E K) (hVl : V l = 1) (hVs : V s = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hactive : rankTwoPrincipalPivot (hessian (initialForm w m P)) i k ≠ 0)
    (hsq : let J := rankThreeComplementJacobian l V; J * J = 0)
    (r : E K)
    (hrel : ∀ j, j ≠ l → rankThreePartial j (V k) = r * rankThreePartial j (V i))
    (htrace : rankThreePartial i (V i) + rankThreePartial k (V k) = 0)
    (hiso : let f := algebraMap (B K) (E K); let L := initialForm w m P
      f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0) :
    False := by
  classical
  let L := initialForm w m P
  have hconstl (j : Fin 4) : rankThreePartial j (V l) = 0 := by
    rw [hVl,Derivation.map_one_eq_zero]
  have hconsts (j : Fin 4) : rankThreePartial j (V s) = 0 := by
    rw [hVs,map_zero]
  have hsum (F : Fin 4 → E K) : ∑ a, F a = F s + F l + F i + F k := by
    have hu : (Finset.univ : Finset (Fin 4)) = {s,l,i,k} := by
      ext a
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
      exact hcover a
    rw [hu,Finset.sum_insert,Finset.sum_insert,Finset.sum_insert,Finset.sum_singleton]
    · ring
    · simp [hik]
    · simp [Ne.symm hil,Ne.symm hkl]
    · simp [hsl,Ne.symm his,Ne.symm hks]
  have hacc (b : Fin 4) : rankThreePartial l (V b) +
      V i * rankThreePartial i (V b) + V k * rankThreePartial k (V b) = 0 := by
    have he := rankThree_normalizedKernel_acceleration_zero L l hreg V hVl hV b
    rw [hsum,hVs,hVl,zero_mul,one_mul,zero_add] at he
    exact he
  have hall (j : Fin 4) : rankThreePartial j (V k) = r * rankThreePartial j (V i) := by
    by_cases hj : j = l
    · subst j
      have ha := hacc i
      have hb := hacc k
      rw [hrel i hil,hrel k hkl] at hb
      linear_combination hb - r*ha
    · exact hrel j hj
  by_cases hvar : rankThreePartial k (V i) = 0
  · have hii : rankThreePartial i (V i) = 0 := by
      rw [hall k,hvar,mul_zero,add_zero] at htrace
      exact htrace
    have hik' : rankThreePartial i (V k) = 0 := by rw [hall i,hii,mul_zero]
    have hkk : rankThreePartial k (V k) = 0 := by rw [hall k,hvar,mul_zero]
    have hli : rankThreePartial l (V i) = 0 := by
      have he := hacc i
      rwa [hii,hvar,mul_zero,mul_zero,add_zero,add_zero] at he
    have hlk : rankThreePartial l (V k) = 0 := by rw [hall l,hli,mul_zero]
    have hrelative (a : Fin 4) (ha : a ≠ s) (b : Fin 4) :
        rankThreePartial a (V b) = 0 := by
      rcases hcover b with hb | hb | hb | hb
      · rw [hb,hconsts]
      · rw [hb,hconstl]
      · subst b
        rcases hcover a with hh | hh | hh | hh
        · exact (ha hh).elim
        · rw [hh,hli]
        · rw [hh,hii]
        · rw [hh,hvar]
      · subst b
        rcases hcover a with hh | hh | hh | hh
        · exact (ha hh).elim
        · rw [hh,hlk]
        · rw [hh,hik']
        · rw [hh,hkk]
    obtain ⟨d,hd,hker⟩ := rankThree_oneVariableKernel_constant L s l i k his hks hik
      hcover hactive V hVs hVl hV hrelative
    exact hd (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap
      hclock hopt hdet d hker)
  · obtain ⟨_,hrk⟩ := rankThree_rankOne_regularActiveSlope_constant L i k hik
      (V i) (V k) r hall htrace hvar hiso hactive
    have hrall (j : Fin 4) : rankThreePartial j r = 0 := by
      have he := rankThree_proportionalDifferential_slope (V i) (V k) r hall j k
      rw [hrk,zero_mul] at he
      exact (mul_eq_zero.mp he).resolve_right hvar
    obtain ⟨c,hc⟩ := rankOnePartial_constants r hrall
    have hdiff (j : Fin 4) :
        rankThreePartial j (V k - algebraMap K (E K) c * V i) = 0 := by
      simp only [map_sub,Derivation.leibniz,smul_eq_mul,Derivation.map_algebraMap,
        mul_zero,add_zero,hall,hc,sub_self]
    obtain ⟨b,hb⟩ := rankOnePartial_constants
      (V k - algebraMap K (E K) c * V i) hdiff
    let d : Fin 4 → K := Pi.single l 1 + Pi.single k b
    let e : Fin 4 → K := Pi.single i 1 + Pi.single k c
    have hdl : d l = 1 := by simp [d,Ne.symm hkl]
    have hel : e l = 0 := by simp [e,Ne.symm hil,Ne.symm hkl]
    have hei : e i = 1 := by simp [e,hik]
    have he0 : e ≠ 0 := by
      intro hz
      rw [hz] at hei
      exact zero_ne_one hei
    apply globalWeightOptimum_rankThree_no_affineKernelLine P w m hw hm hcap
      hclock hopt hdet l V hVl hreg hV hsq d e hdl hel he0 (V i)
    intro j
    rcases hcover j with hj | hj | hj | hj
    · subst j
      simp [d,e,hVs,hsl,Ne.symm hks,Ne.symm his]
    · subst j
      rw [hVl,hdl,hel,map_one,map_zero,mul_zero,add_zero]
    · subst j
      simp [d,e,hil,hik]
    · subst j
      have hd : d k = b := by simp [d,hkl]
      have he : e k = c := by simp [e,Ne.symm hik]
      rw [hd,he]
      linear_combination hb


set_option maxHeartbeats 6000000 in
/-- Extract the slope, trace and isotropy premises directly from
the actual complementary rank-one factorization. -/
theorem rankThree_rankOne_orientedSlope_data
    (L : B K) (l : Fin 4) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcover : ∀ j : Fin 3, j = a ∨ j = b ∨ j = c)
    (V : Fin 4 → E K)
    (u v : Fin 3 → E K) (hub : u b ≠ 0) (hua : u a = 0) (hv : v ≠ 0)
    (hfac : ∀ i j, rankThreeComplementJacobian l V i j = u i * v j)
    (hdot : v ⬝ᵥ u = 0)
    (hsq : let J := rankThreeComplementJacobian l V; J * J = 0)
    (hself : let J := rankThreeComplementJacobian l V
      let H := ((hessian L).submatrix l.succAbove l.succAbove).map
        (algebraMap (B K) (E K))
      H * J = J.transpose * H) :
    let i := l.succAbove b
    let k := l.succAbove c
    ∃ r : E K,
      (∀ j, j ≠ l → rankThreePartial j (V k) = r * rankThreePartial j (V i)) ∧
      rankThreePartial i (V i) + rankThreePartial k (V k) = 0 ∧
      (let f := algebraMap (B K) (E K)
       f (hessian L i i) + 2*r*f (hessian L i k) + r*r*f (hessian L k k) = 0) := by
  classical
  let J := rankThreeComplementJacobian l V
  let f := algebraMap (B K) (E K)
  let H := ((hessian L).submatrix l.succAbove l.succAbove).map f
  let i := l.succAbove b
  let k := l.succAbove c
  let r := u c / u b
  have hr : r * u b = u c := div_mul_cancel₀ _ hub
  have hfac' (i j : Fin 3) : J i j = u i * v j := hfac i j
  have hrow (j : Fin 3) : J c j = r * J b j := by
    rw [hfac',hfac',← mul_assoc,hr]
  have hsum (F : Fin 3 → E K) : ∑ j, F j = F a + F b + F c := by
    have hu : (Finset.univ : Finset (Fin 3)) = {a,b,c} := by
      ext j
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
      exact hcover j
    rw [hu,Finset.sum_insert,Finset.sum_insert,Finset.sum_singleton]
    · ring
    · simp [hbc]
    · simp [hab,hac]
  have htrace : J b b + J c c = 0 := by
    change (∑ j, v j * u j) = 0 at hdot
    rw [hsum,hua,mul_zero,zero_add] at hdot
    rw [hfac',hfac']
    linear_combination hdot
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  have hjb : J b j ≠ 0 := by rw [hfac']; exact mul_ne_zero hub hj
  have hja : J a j = 0 := by rw [hfac',hua,zero_mul]
  have hiso := rankThree_velocity_column_isotropic H J hself hsq j
  rw [hsum] at hiso
  rw [hsum (fun q => J a j * H a q * J q j),
      hsum (fun q => J b j * H b q * J q j),
      hsum (fun q => J c j * H c q * J q j)] at hiso
  simp only [hja,zero_mul,mul_zero,zero_add,add_zero] at hiso
  rw [hrow j] at hiso
  have hs : H c b = H b c := by
    change f (hessian L k i) = f (hessian L i k)
    rw [show hessian L k i = hessian L i k from pderiv_comm_backport _ _ _]
  rw [hs] at hiso
  refine ⟨r,?_,htrace,?_⟩
  · intro q hq
    obtain ⟨t,ht⟩ := Fin.exists_succAbove_eq hq
    rw [← ht]
    exact hrow t
  · change H b b + 2*r*H b c + r*r*H c c = 0
    apply (mul_eq_zero.mp (show J b j * J b j *
      (H b b + 2*r*H b c + r*r*H c c) = 0 by
      linear_combination hiso)).resolve_left (mul_ne_zero hjb hjb)

/-- Regular active principal minor excluded on every orientation
of the actual rank-one chart. -/
theorem counterexample_rankThree_no_regularActive
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    rankTwoPrincipalPivot (hessian (initialForm w m P))
      (l.succAbove (a.succAbove 0)) (l.succAbove (a.succAbove 1)) = 0 := by
  classical
  let L := initialForm w m P
  let b := a.succAbove 0
  let c := a.succAbove 1
  have hba : b ≠ a := Fin.succAbove_ne _ _
  have hca : c ≠ a := Fin.succAbove_ne _ _
  have hbc : b ≠ c := by
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (Fin.succAbove_right_injective he)
  have hcover (j : Fin 3) : j = a ∨ j = b ∨ j = c := by
    by_cases hj : j = a
    · exact Or.inl hj
    obtain ⟨q,hq⟩ := Fin.exists_succAbove_eq hj
    have h : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    rcases h with h | h
    · exact Or.inr (Or.inl (by rw [← hq,h]))
    · exact Or.inr (Or.inr (by rw [← hq,h]))
  obtain ⟨_,hself,u,v,hu,hv,hua,hfac,hdot,hsq⟩ :=
    counterexample_rankThree_rankOne_frontier hJC2 P w m hw hm hcap hclock hopt hdet
      hnoninj l a V hVl hVk hreg hV
  by_contra hactive
  have hclose (d e : Fin 3) (hda : d ≠ a) (hea : e ≠ a) (hde : d ≠ e)
      (hcov : ∀ j : Fin 3, j = a ∨ j = d ∨ j = e)
      (hud : u d ≠ 0)
      (hp : rankTwoPrincipalPivot (hessian L) (l.succAbove d) (l.succAbove e) ≠ 0) :
      False := by
    let s := l.succAbove a
    let i := l.succAbove d
    let k := l.succAbove e
    have his : i ≠ s := fun h => hda (Fin.succAbove_right_injective h)
    have hks : k ≠ s := fun h => hea (Fin.succAbove_right_injective h)
    have hik : i ≠ k := fun h => hde (Fin.succAbove_right_injective h)
    have hcov4 (j : Fin 4) : j = s ∨ j = l ∨ j = i ∨ j = k := by
      by_cases hj : j = l
      · exact Or.inr (Or.inl hj)
      obtain ⟨q,hq⟩ := Fin.exists_succAbove_eq hj
      rcases hcov q with h | h | h
      · exact Or.inl (by rw [← hq,h])
      · exact Or.inr (Or.inr (Or.inl (by rw [← hq,h])))
      · exact Or.inr (Or.inr (Or.inr (by rw [← hq,h])))
    obtain ⟨r,hrel,htrace,hiso⟩ := rankThree_rankOne_orientedSlope_data L l a d e
      (Ne.symm hda) (Ne.symm hea) hde hcov V u v hud hua hv hfac hdot hsq hself
    exact globalWeightOptimum_rankThree_rankOne_regularActive_oriented P w m hw hm hcap
      hclock hopt hdet l s i k (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
      (Fin.succAbove_ne _ _) his hks hik hcov4 V hVl hVk hreg hV hp hsq r hrel htrace hiso
  by_cases hub : u b = 0
  · have huc : u c ≠ 0 := by
      intro hz
      apply hu
      funext j
      rcases hcover j with h | h | h
      · rw [h,hua]; rfl
      · rw [h,hub]; rfl
      · rw [h,hz]; rfl
    refine hclose c b hca hba (Ne.symm hbc) ?_ huc ?_
    · intro j
      rcases hcover j with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · intro hz
      apply hactive
      unfold rankTwoPrincipalPivot at hz ⊢
      change hessian L (l.succAbove b) (l.succAbove b) *
        hessian L (l.succAbove c) (l.succAbove c) -
        hessian L (l.succAbove b) (l.succAbove c) *
          hessian L (l.succAbove c) (l.succAbove b) = 0
      linear_combination hz
  · exact hclose b c hba hca hbc hcover hub hactive



set_option maxHeartbeats 4000000 in
/-- The vanishing active pivot implies restricted Hessian rank at most one,
independently of the velocity rank. -/
theorem rankThree_activePivot_zero_restrictedMinors
    (L : B K) (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hV : (hessian L).map (algebraMap (B K) (E K)) *ᵥ V = 0)
    (hm : rankTwoPrincipalPivot (hessian L)
      (l.succAbove (a.succAbove 0)) (l.succAbove (a.succAbove 1)) = 0) :
    ∀ i j p q : Fin 4, i ≠ l.succAbove a → j ≠ l.succAbove a →
      p ≠ l.succAbove a → q ≠ l.succAbove a →
      hessian L i p * hessian L j q = hessian L i q * hessian L j p := by
  classical
  let f := algebraMap (B K) (E K)
  let H := (hessian L).map f
  let k := l.succAbove a
  let u := l.succAbove (a.succAbove 0)
  let v := l.succAbove (a.succAbove 1)
  have hminor : rankTwoPrincipalPivot H u v = 0 := by
    rw [← rankTwoPrincipalPivot_map]
    change f (rankTwoPrincipalPivot (hessian L) u v) = 0
    rw [hm,map_zero]
  have hs (i j : Fin 4) : H i j = H j i :=
    congrArg f (pderiv_comm_backport j i L)
  have hkl : k ≠ l := Fin.succAbove_ne l a
  have hku : k ≠ u := by
    intro he
    exact (Fin.succAbove_ne a 0) (Fin.succAbove_right_injective he).symm
  have hkv : k ≠ v := by
    intro he
    exact (Fin.succAbove_ne a 1) (Fin.succAbove_right_injective he).symm
  have hlu : l ≠ u := Ne.symm (Fin.succAbove_ne l _)
  have hlv : l ≠ v := Ne.symm (Fin.succAbove_ne l _)
  have huv : u ≠ v := by
    intro he
    have hz : (0 : Fin 2) = 1 :=
      Fin.succAbove_right_injective (Fin.succAbove_right_injective he)
    exact (by decide : (0 : Fin 2) ≠ 1) hz
  have hcover (i : Fin 4) : i = k ∨ i = l ∨ i = u ∨ i = v := by
    by_cases hi : i = l
    · exact Or.inr (Or.inl hi)
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hi
    by_cases hba : b = a
    · left
      rw [← hb,hba]
    obtain ⟨c,hc⟩ := Fin.exists_succAbove_eq hba
    have he : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    rcases he with he | he
    · right; right; left
      rw [← hb,← hc,he]
    · right; right; right
      rw [← hb,← hc,he]
  intro i j p q hi hj hp hq
  have he := rankThree_activeMinor_zero_all_restrictedMinors H hs k l u v hkl
    hcover V hVk hVl hV hku hkv hlu hlv huv hminor i j p q hi hj hp hq
  apply IsFractionRing.injective (B K) (E K)
  change f (hessian L i p * hessian L j q) = f (hessian L i q * hessian L j p)
  simp only [map_mul]
  exact he

set_option maxHeartbeats 6000000 in
/-- The remaining chart, if it exists, has zero omitted weight,
three equal restricted weights, and a normalized kernel depending
only on the omitted coordinate. -/
theorem counterexample_rankThree_zeroWeight_relative_frontier
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : B K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P))
    (l : Fin 4) (a : Fin 3) (V : Fin 4 → E K)
    (hVl : V l = 1) (hVk : V (l.succAbove a) = 0)
    (hreg : (hessian (initialForm w m P)).adjugate l l ≠ 0)
    (hV : (hessian (initialForm w m P)).map (algebraMap (B K) (E K)) *ᵥ V = 0) :
    let s := l.succAbove a
    let L := initialForm w m P
    w s = 0 ∧
      (∀ i, i ≠ s → hessian L i i ≠ 0 ∧ w i = w l) ∧
      (∀ i j p q : Fin 4, i ≠ s → j ≠ s → p ≠ s → q ≠ s →
        hessian L i p * hessian L j q = hessian L i q * hessian L j p) ∧
      ∀ j, j ≠ s → ∀ i, rankThreePartial j (V i) = 0 := by
  classical
  let L := initialForm w m P
  let s := l.succAbove a
  have hs := counterexample_rankThree_no_regularActive hJC2 P w m hw hm hcap
    hclock hopt hdet hnoninj l a V hVl hVk hreg hV
  have hmin := rankThree_activePivot_zero_restrictedMinors L l a V hVl hVk hV hs
  have hws : w s = 0 := by
    by_contra hz
    exact globalWeightOptimum_rankThree_no_restrictedRankOne_positiveWeight P w m
      hw hm hcap hclock hopt hdet s hmin (lt_of_le_of_ne (hw s) (Ne.symm hz))
  have hnon (i : Fin 4) (his : i ≠ s) : hessian L i i ≠ 0 := by
    intro hz
    exact hnoninj (globalWeightOptimum_rankThree_zeroWeight_zeroRow_terminal hJC2
      P w m hw hm hcap hclock hopt hdet s i his hws hmin hz)
  have hls : l ≠ s := Ne.symm (Fin.succAbove_ne l a)
  have hweights (i : Fin 4) (his : i ≠ s) : w i = w l := by
    by_cases hil : i = l
    · rw [hil]
    have hmix : hessian L i l ≠ 0 := by
      intro hz
      have he := hmin l i l i hls his hls his
      rw [hz,mul_zero] at he
      exact (mul_ne_zero (hnon l hls) (hnon i his)) he
    rcases rankThree_restricted_weightedRatio L w m hw
      (initialForm_isWeightedHomogeneous w m P) s hmin l i hls his hil
      (hnon l hls) hmix with ⟨_,he⟩ | ⟨he,_⟩
    · exact he
    · omega
  obtain ⟨r,hrs,hrp,hrows,hgrad,hconst⟩ :=
    rankThree_zeroWeight_gradient_ratios L w m hw hm
      (initialForm_isWeightedHomogeneous w m P) s l hls hws hnon hmin
  exact ⟨hws,fun i hi => ⟨hnon i hi,hweights i hi⟩,hmin,
    rankThree_kernel_relative_of_gradient_ratios L s l l hls
      (hnon l hls) hreg V hVk hVl hV r hrs hrows hgrad hconst⟩

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankThree_oneVariableKernel_derivative_rows
#print axioms HC4.Polynomial.rankThree_oneVariableKernel_constant

#print axioms HC4.Polynomial.rankThree_normalizedKernel_exists
#print axioms HC4.Polynomial.rankThree_kernel_mixedDifferential
#print axioms HC4.Polynomial.rankThree_normalizedKernel_lineGradient

#print axioms HC4.Polynomial.rankThree_complement_transport
#print axioms HC4.Polynomial.rankThree_complement_det_one
#print axioms HC4.Polynomial.rankThree_complement_cube_zero

#print axioms HC4.Polynomial.rankThree_complement_zeroRow
#print axioms HC4.Polynomial.rankThree_complement_selfAdjoint

#print axioms HC4.Polynomial.rankThree_normalizedKernel_acceleration_zero
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_complementJacobian_ne_zero
#print axioms HC4.Polynomial.rankThree_zeroRow_rankTwo_principalCofactor_zero

#print axioms HC4.Polynomial.rankThree_activeMinor_zero_all_restrictedMinors
#print axioms HC4.Polynomial.rankThree_rankTwoVelocity_restrictedMinors_zero

#print axioms HC4.Polynomial.rankThree_rankTwoVelocity_ratio_num_den_independent

#print axioms HC4.Polynomial.rankThree_rankTwoVelocity_weightedRatio

#print axioms HC4.Polynomial.rankThree_support_transfer_to_pivot
#print axioms HC4.Polynomial.rankThree_support_cap_of_monomial_rows

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_unique_active_max

#print axioms HC4.Polynomial.rankThree_restricted_weightedRatio
#print axioms HC4.Polynomial.rankThree_restricted_row_zero
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_restricted_atMostOne_zero
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_restricted_no_gain

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_zeroRow_weight_gap
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_one_zero_distinct_weights

#print axioms HC4.Polynomial.rankThree_restricted_equalWeight_rows
#print axioms HC4.Polynomial.rankThree_restricted_shear_zero_row

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_one_zero
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_repeated_nonzero_weights

#print axioms HC4.Polynomial.rankThree_remaining_two_coordinates
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_rankTwoVelocity_positiveWeight

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_zeroWeight_zeroRow_terminal
#print axioms HC4.Polynomial.rankThree_weightedEuler
#print axioms HC4.Polynomial.rankThree_relative_derivative_constant

#print axioms HC4.Polynomial.rankThree_zeroWeight_gradient_ratios
#print axioms HC4.Polynomial.rankThree_kernel_relative_of_gradient_ratios

#print axioms HC4.Polynomial.counterexample_rankThree_no_rankTwoVelocity_zeroWeight
#print axioms HC4.Polynomial.counterexample_rankThree_no_rankTwoVelocity

#print axioms HC4.Polynomial.rankThree_rankOne_factor_square_zero
#print axioms HC4.Polynomial.counterexample_rankThree_rankOne_frontier
#print axioms HC4.Polynomial.rankThree_velocity_column_isotropic

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_affineKernelLine

#print axioms HC4.Polynomial.rankThree_lineEval_affine_of_derivation_sq_zero
#print axioms HC4.Polynomial.rankThree_lineEval_partial
#print axioms HC4.Polynomial.rankThree_isotropicSlope_activeMinor_zero

#print axioms HC4.Polynomial.rankThreePartial_comm
#print axioms HC4.Polynomial.rankThree_proportionalDifferential_slope
#print axioms HC4.Polynomial.rankThree_rankOne_slope_transport
#print axioms HC4.Polynomial.rankThree_rankOne_regularActiveSlope_constant

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_no_restrictedRankOne_positiveWeight

#print axioms HC4.Polynomial.globalWeightOptimum_rankThree_rankOne_regularActive_oriented

#print axioms HC4.Polynomial.rankThree_rankOne_orientedSlope_data
#print axioms HC4.Polynomial.counterexample_rankThree_no_regularActive

#print axioms HC4.Polynomial.rankThree_activePivot_zero_restrictedMinors
#print axioms HC4.Polynomial.counterexample_rankThree_zeroWeight_relative_frontier
