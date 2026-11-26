import HC4.Polynomial.RankThreeExtremalReduction

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
  have hsum {R : Type*} [AddCommMonoid R] (g : Fin 4 → R) (hg : g l = 0) :
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
  rw [hsum _ (by rw [hc, mul_zero])] at e
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
