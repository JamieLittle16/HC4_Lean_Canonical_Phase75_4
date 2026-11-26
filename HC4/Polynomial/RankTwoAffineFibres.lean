import HC4.Polynomial.RankTwoPrincipalPivot

/-!
# Affine fibres of a rank-two polynomial gradient

The normalized rational kernel construction is performed over the
localization at an actual principal two-minor. Hessian third derivative
symmetry puts the acceleration in the kernel, while its two free
coordinates are constants. The pivot then kills the acceleration.

Specializing the resulting polynomial line at a regular ground-field
point proves that every direction in the evaluated kernel gives an
entire line of constant gradient. Thus the whole affine kernel plane
is in the gradient fibre. No classification of Hessians is assumed.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton RankThreeCubic
open nonZeroDivisors
open scoped Matrix BigOperators
noncomputable section

section Matrix

variable {R : Type*} [CommRing R]

/-- A regular principal pivot detects a kernel vector supported
on its two coordinates. -/
theorem rankTwo_kernel_zero_of_supportedOnPivot
    (A : Matrix (Fin 4) (Fin 4) R) (k p : Fin 4) (hkp : k ≠ p)
    (hreg : IsUnit (rankTwoPrincipalPivot A k p))
    (v : Fin 4 → R) (hv : A *ᵥ v = 0)
    (hs : ∀ i, i ≠ k → i ≠ p → v i = 0) : v = 0 := by
  classical
  have hrepr : v = (Pi.single k (v k) : Fin 4 → R) + Pi.single p (v p) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp [hkp]
    · by_cases hj : i = p
      · subst i
        simp [hi]
      · simp [Pi.single_eq_of_ne hi,Pi.single_eq_of_ne hj,hs i hi hj]
  have he (i : Fin 4) : A i k * v k + A i p * v p = 0 := by
    have h := congrArg (fun z : Fin 4 → R => A *ᵥ z) hrepr
    change A *ᵥ v = A *ᵥ ((Pi.single k (v k) : Fin 4 → R) + Pi.single p (v p)) at h
    rw [hv,Matrix.mulVec_add,Matrix.mulVec_single,Matrix.mulVec_single] at h
    exact (congrFun h i).symm
  have hk : rankTwoPrincipalPivot A k p * v k = 0 := by
    unfold rankTwoPrincipalPivot
    linear_combination A p p * he k - A k p * he p
  have hp : rankTwoPrincipalPivot A k p * v p = 0 := by
    unfold rankTwoPrincipalPivot
    linear_combination A k k * he p - A p k * he k
  have hk0 : v k = 0 := hreg.mul_right_inj.mp (by rw [hk,mul_zero])
  have hp0 : v p = 0 := hreg.mul_right_inj.mp (by rw [hp,mul_zero])
  rw [hrepr,hk0,hp0]
  simp

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 4) K

set_option maxHeartbeats 3000000 in
/-- Kernel acceleration vanishes when the nonpivot components
are constants. This is the same characteristic argument as the
verified corank-one theorem, with two normalized free coordinates. -/
theorem rankTwo_lineEval_gradient_of_normalizedKernel
    {S : Type*} [CommRing S] [IsDomain S] [CharZero S] [Algebra K S]
    [Algebra (B K) S] [IsScalarTower K (B K) S]
    (N : Submonoid (B K)) [IsLocalization N S]
    (L : B K) (k p : Fin 4) (hkp : k ≠ p)
    (hreg : IsUnit (algebraMap (B K) S (rankTwoPrincipalPivot (hessian L) k p)))
    (V : Fin 4 → S) (hker : (hessian L).map (algebraMap (B K) S) *ᵥ V = 0)
    (hfree : ∀ i, i ≠ k → i ≠ p → ∃ c : K, V i = algebraMap K S c) :
    ∀ i, lineEval (fun j => algebraMap (B K) S (X j)) V (pderiv i L) =
      _root_.Polynomial.C (algebraMap (B K) S (pderiv i L)) := by
  classical
  let g := algebraMap (B K) S
  let z : Fin 4 → S := fun i => g (X i)
  let H := (hessian L).map g
  let d : Fin 4 → Derivation K S S := fun i => localizationDerivation N (pderiv i)
  have hd (i : Fin 4) (q : B K) : d i (g q) = g (pderiv i q) :=
    localizationDerivation_algebraMap N _ _
  have hregH : IsUnit (rankTwoPrincipalPivot H k p) := by
    have he : rankTwoPrincipalPivot H k p = g (rankTwoPrincipalPivot (hessian L) k p) := by
      simp only [rankTwoPrincipalPivot,H,Matrix.map_apply,map_sub,map_mul]
    rw [he]
    exact hreg
  have hker' (i : Fin 4) : ∑ j, H i j * V j = 0 := congrFun hker i
  have hs (i j : Fin 4) : H i j = H j i := by
    change g (pderiv j (pderiv i L)) = g (pderiv i (pderiv j L))
    rw [pderiv_comm_backport]
  have ht (i j l : Fin 4) : d l (H i j) = d i (H l j) := by
    change d l (g (pderiv j (pderiv i L))) = d i (g (pderiv j (pderiv l L)))
    rw [hd,hd,pderiv_comm_backport l j,pderiv_comm_backport i j,
      pderiv_comm_backport l i]
  let D : Derivation K S S := ∑ i, V i • d i
  have hD (x : S) : D x = ∑ i, V i * d i x := by
    change Derivation.coeFnAddMonoidHom D x = _
    simp only [D,map_sum,Finset.sum_apply,Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply,smul_eq_mul]
  have hacc : H *ᵥ (fun i => D (V i)) = 0 := by
    funext i
    simp only [Matrix.mulVec,dotProduct,hD,Pi.zero_apply]
    exact hessianKernel_acceleration d H V hs ht hker' i
  have hfreeD (i : Fin 4) (hi : i ≠ k) (hj : i ≠ p) : D (V i) = 0 := by
    obtain ⟨c,hc⟩ := hfree i hi hj
    rw [hc,D.map_algebraMap]
  have hD0 (i : Fin 4) : D (V i) = 0 :=
    congrFun (rankTwo_kernel_zero_of_supportedOnPivot H k p hkp hregH _
      hacc hfreeD) i
  have hz (i : Fin 4) : D (z i) = V i := by
    simp only [z,hD,hd,pderiv_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hg (q : B K) : MvPolynomial.aeval z q = g q := by
    let f := IsScalarTower.toAlgHom K (B K) S
    have he : MvPolynomial.aeval z = f := by
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

set_option maxHeartbeats 3000000 in
/-- Lift any constant vector to a normalized kernel vector in the
pivot localization. It specializes to the original vector wherever
that vector is in the evaluated kernel and the pivot is regular. -/
theorem rankTwo_regularPoint_lineEval_gradient
    (L : B K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (hkp : k ≠ p)
    (x v : Fin 4 → K)
    (hreg : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hv : (hessian L).map (MvPolynomial.eval x) *ᵥ v = 0) :
    ∀ i, lineEval x v (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.eval x (pderiv i L)) := by
  classical
  let Δ := rankTwoPrincipalPivot (hessian L) k p
  let S := Localization.Away Δ
  have hΔ : Δ ≠ 0 := by
    intro h
    exact hreg (by change MvPolynomial.eval x Δ = 0; rw [h,map_zero])
  have hpow := powers_le_nonZeroDivisors_of_noZeroDivisors hΔ
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hpow
  letI : CharZero S := charZero_of_injective_algebraMap (IsLocalization.injective S hpow)
  let g := algebraMap (B K) S
  let H := (hessian L).map g
  let c : Fin 4 → S := fun i => algebraMap K S (v i)
  let u := H *ᵥ c
  have hunit : IsUnit (g Δ) := IsLocalization.Away.algebraMap_isUnit Δ
  letI : Invertible (g Δ) := hunit.invertible
  let t := ⅟ (g Δ)
  have ht : g Δ * t = 1 := mul_invOf_self _
  have hδ : rankTwoPrincipalPivot H k p = g Δ := by
    simp only [rankTwoPrincipalPivot,H,Matrix.map_apply,Δ,map_mul,map_sub]
  let a := H p p * u k - H k p * u p
  let b := H k k * u p - H p k * u k
  let V : Fin 4 → S := c - (Pi.single k (t*a) : Fin 4 → S) - Pi.single p (t*b)
  have hminor : AllThreeMinorsZero H := hL.map g
  have hcross (i : Fin 4) : g Δ * u i = H i k * a + H i p * b := by
    have he := rankTwo_pivotEquations_of_image H hminor k p c i
    rw [hδ] at he
    exact he
  have hker : H *ᵥ V = 0 := by
    change H *ᵥ (c - (Pi.single k (t*a) : Fin 4 → S) - Pi.single p (t*b)) = 0
    rw [Matrix.mulVec_sub,Matrix.mulVec_sub,Matrix.mulVec_single,Matrix.mulVec_single]
    funext i
    change u i - H i k * (t*a) - H i p * (t*b) = 0
    have hu : u i = t * (H i k * a + H i p * b) := by
      calc
        u i = t * (g Δ * u i) := by rw [← mul_assoc,mul_comm t (g Δ),ht,one_mul]
        _ = _ := by rw [hcross i]
    rw [hu]
    ring
  have hfree (i : Fin 4) (hi : i ≠ k) (hj : i ≠ p) :
      ∃ d : K, V i = algebraMap K S d := by
    refine ⟨v i,?_⟩
    change c i - (Pi.single k (t*a) : Fin 4 → S) i -
      (Pi.single p (t*b) : Fin 4 → S) i = c i
    rw [Pi.single_eq_of_ne hi,Pi.single_eq_of_ne hj,sub_zero,sub_zero]
  have hline := rankTwo_lineEval_gradient_of_normalizedKernel
    (S := S) (Submonoid.powers Δ) L k p hkp hunit V hker hfree
  let φ : S →+* K := IsLocalization.Away.lift Δ (g := MvPolynomial.eval x)
    (isUnit_iff_ne_zero.mpr hreg)
  have hφ (q : B K) : φ (g q) = MvPolynomial.eval x q :=
    IsLocalization.Away.lift_eq Δ _ q
  have hφC (r : K) : φ (algebraMap K S r) = r := by
    rw [IsScalarTower.algebraMap_apply K (B K) S]
    change φ (g (MvPolynomial.C r)) = r
    rw [hφ,MvPolynomial.eval_C]
  have hu (i : Fin 4) : φ (u i) = 0 := by
    have he := congrFun hv i
    change (∑ j : Fin 4, MvPolynomial.eval x (hessian L i j) * v j) = 0 at he
    change φ (∑ j : Fin 4, g (hessian L i j) * algebraMap K S (v j)) = 0
    simp only [map_sum,map_mul,hφ,hφC]
    exact he
  have ha : φ a = 0 := by
    change φ (H p p * u k - H k p * u p) = 0
    simp only [map_sub,map_mul,hu,mul_zero,sub_zero]
  have hb : φ b = 0 := by
    change φ (H k k * u p - H p k * u k) = 0
    simp only [map_sub,map_mul,hu,mul_zero,sub_zero]
  have hV (i : Fin 4) : φ (V i) = v i := by
    change φ (c i - (Pi.single k (t*a) : Fin 4 → S) i -
      (Pi.single p (t*b) : Fin 4 → S) i) = v i
    have h1 : φ ((Pi.single k (t*a) : Fin 4 → S) i) = 0 := by
      by_cases hi : i = k
      · subst i
        rw [Pi.single_eq_same,map_mul,ha,mul_zero]
      · rw [Pi.single_eq_of_ne hi,map_zero]
    have h2 : φ ((Pi.single p (t*b) : Fin 4 → S) i) = 0 := by
      by_cases hi : i = p
      · subst i
        rw [Pi.single_eq_same,map_mul,hb,mul_zero]
      · rw [Pi.single_eq_of_ne hi,map_zero]
    rw [map_sub,map_sub,h1,h2,sub_zero,sub_zero]
    exact hφC (v i)
  let z : Fin 4 → S := fun i => g (X i)
  have hmap : (_root_.Polynomial.mapRingHom φ).comp (lineEval z V).toRingHom =
      (lineEval (K := K) x v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change _root_.Polynomial.mapRingHom φ ((lineEval (K := K) z V) (MvPolynomial.C r)) =
        (lineEval (K := K) x v) (MvPolynomial.C r)
      simp [lineEval,IsScalarTower.algebraMap_apply K S (_root_.Polynomial S),
        _root_.Polynomial.algebraMap_eq,hφC]
    · intro i
      change _root_.Polynomial.mapRingHom φ ((lineEval (K := K) z V) (X i)) =
        (lineEval (K := K) x v) (X i)
      simp [lineEval,z,hφ,hV]
  intro i
  have he := congrArg (_root_.Polynomial.mapRingHom φ) (hline i)
  rw [show _root_.Polynomial.mapRingHom φ (lineEval z V (pderiv i L)) =
    lineEval x v (pderiv i L) from RingHom.congr_fun hmap (pderiv i L)] at he
  change lineEval x v (pderiv i L) =
    _root_.Polynomial.map φ (_root_.Polynomial.C (g (pderiv i L))) at he
  rw [_root_.Polynomial.map_C,hφ] at he
  exact he

/-- Every point of the affine evaluated kernel plane has the
same actual polynomial gradient as the regular basepoint. -/
theorem rankTwo_regularPoint_affineKernel_fibre
    (L : B K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (hkp : k ≠ p)
    (x v : Fin 4 → K)
    (hreg : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hv : (hessian L).map (MvPolynomial.eval x) *ᵥ v = 0) :
    mvGradientMap L (x+v) = mvGradientMap L x := by
  classical
  have hline := rankTwo_regularPoint_lineEval_gradient L hL k p hkp x v hreg hv
  have hmap : (_root_.Polynomial.evalRingHom (1 : K)).comp (lineEval (K := K) x v).toRingHom =
      MvPolynomial.eval (x+v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lineEval,_root_.Polynomial.algebraMap_eq]
    · intro i
      simp [lineEval,Pi.add_apply]
  funext i
  have he := congrArg (_root_.Polynomial.evalRingHom (1 : K)) (hline i)
  change ((_root_.Polynomial.evalRingHom (1 : K)).comp (lineEval (K := K) x v).toRingHom)
      (pderiv i L) = (_root_.Polynomial.C (MvPolynomial.eval x (pderiv i L))).eval 1 at he
  rw [hmap,_root_.Polynomial.eval_C] at he
  exact he


/-- Distinct gradient fibres cannot have complementary evaluated
kernel spaces. In fact even a decomposition of the displacement of
the basepoints into the two kernels would force equal gradients. -/
theorem rankTwo_distinctGradient_no_kernelDisplacement
    (L : B K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (hkp : k ≠ p) (x y : Fin 4 → K)
    (hx : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hy : MvPolynomial.eval y (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hxy : mvGradientMap L x ≠ mvGradientMap L y)
    (u v : Fin 4 → K)
    (hu : (hessian L).map (MvPolynomial.eval x) *ᵥ u = 0)
    (hv : (hessian L).map (MvPolynomial.eval y) *ᵥ v = 0) :
    x + u ≠ y + v := by
  intro he
  apply hxy
  calc
    mvGradientMap L x = mvGradientMap L (x+u) :=
      (rankTwo_regularPoint_affineKernel_fibre L hL k p hkp x u hx hu).symm
    _ = mvGradientMap L (y+v) := congrArg (mvGradientMap L) he
    _ = mvGradientMap L y :=
      rankTwo_regularPoint_affineKernel_fibre L hL k p hkp y v hy hv

/-- The sum of two evaluated kernel spaces of distinct regular
gradient fibres is a proper subspace of the four-dimensional
ground-field space. -/
theorem rankTwo_distinctGradient_kernel_sup_ne_top
    (L : B K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (hkp : k ≠ p) (x y : Fin 4 → K)
    (hx : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hy : MvPolynomial.eval y (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hxy : mvGradientMap L x ≠ mvGradientMap L y) :
    LinearMap.ker ((hessian L).map (MvPolynomial.eval x)).mulVecLin ⊔
      LinearMap.ker ((hessian L).map (MvPolynomial.eval y)).mulVecLin ≠ ⊤ := by
  classical
  let A := (hessian L).map (MvPolynomial.eval x)
  let B := (hessian L).map (MvPolynomial.eval y)
  let U := LinearMap.ker A.mulVecLin
  let V := LinearMap.ker B.mulVecLin
  intro he
  have htop : U ⊔ V = ⊤ := he
  have hm : y-x ∈ U ⊔ V := by rw [htop]; trivial
  obtain ⟨u,hu,v,hv,hs⟩ := Submodule.mem_sup.mp hm
  have hu' : A *ᵥ u = 0 := hu
  have hv' : B *ᵥ v = 0 := hv
  have hvneg : B *ᵥ (-v) = 0 := by rw [Matrix.mulVec_neg,hv',neg_zero]
  apply rankTwo_distinctGradient_no_kernelDisplacement L hL k p hkp x y hx hy hxy
    u (-v) hu' hvneg
  calc
    x+u = x+(u+v)-v := by abel
    _ = x+(y-x)-v := by rw [hs]
    _ = y+(-v) := by abel

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_lineEval_gradient_of_normalizedKernel
#print axioms HC4.Polynomial.rankTwo_regularPoint_lineEval_gradient
#print axioms HC4.Polynomial.rankTwo_regularPoint_affineKernel_fibre

#print axioms HC4.Polynomial.rankTwo_distinctGradient_kernel_sup_ne_top
