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
    let v : Fin 4 → ℤ := fun i => if i = s then 0 else
      if hessian (initialForm w m P) i i = 0 then m else w p
    (∑ i, v i) ≤ ∑ i, w i := by
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
