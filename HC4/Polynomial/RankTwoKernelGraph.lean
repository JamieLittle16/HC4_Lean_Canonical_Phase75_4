module

public import HC4.Polynomial.RankTwoAffineFibres

/-!
# Kernel graph differences and polynomial density

At a regular two-by-two principal pivot, each kernel is the graph
of a two-by-two linear map on the other coordinates. The coefficients
are the denominator-cleared Schur coefficients.

If two evaluated graph maps have invertible difference, their kernels
sum to the entire space. Affine gradient fibres rule this out when
the gradients differ. A nonzero polynomial gradient component and
the pivot then clear the exceptional set by polynomial density.
-/

@[expose] public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators
noncomputable section

section Matrix

variable {R : Type*} [CommRing R]

def rankTwoGraphNumerator (A : Matrix (Fin 4) (Fin 4) R)
    (k p : Fin 4) (s : Fin 2 → Fin 4) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if i = 0 then -(A p p * A k (s j) - A k p * A p (s j))
    else -(A k k * A p (s j) - A p k * A k (s j))

theorem rankTwoGraphNumerator_map {T : Type*} [CommRing T]
    (A : Matrix (Fin 4) (Fin 4) R) (f : R →+* T)
    (k p : Fin 4) (s : Fin 2 → Fin 4) :
    (rankTwoGraphNumerator A k p s).map f =
      rankTwoGraphNumerator (A.map f) k p s := by
  apply Matrix.ext
  intro i j
  by_cases hi : i = 0 <;> simp [rankTwoGraphNumerator,hi]

theorem rankTwoPrincipalPivot_map {T : Type*} [CommRing T]
    (A : Matrix (Fin 4) (Fin 4) R) (f : R →+* T) (k p : Fin 4) :
    f (rankTwoPrincipalPivot A k p) =
      rankTwoPrincipalPivot (A.map f) k p := by
  simp [rankTwoPrincipalPivot]

end Matrix

variable {K : Type*} [Field K] [CharZero K]
abbrev RankTwoKernelGraph.B (K : Type*) [Field K] := MvPolynomial (Fin 4) K

open RankTwoKernelGraph (B)

section Graph

/-- A partition into pivot and free coordinates. -/
def RankTwoGraphCoordinates (k p : Fin 4) (s : Fin 2 → Fin 4) : Prop :=
  k ≠ p ∧ Function.Injective s ∧
    (∀ j, s j ≠ k ∧ s j ≠ p) ∧
    (∀ i, i = k ∨ i = p ∨ ∃ j, s j = i)

theorem rankTwo_exists_graphCoordinates (k p : Fin 4) (hkp : k ≠ p) :
    ∃ s : Fin 2 → Fin 4, RankTwoGraphCoordinates k p s := by
  fin_cases k <;> fin_cases p <;> first | contradiction | unfold RankTwoGraphCoordinates; decide

variable {k p : Fin 4} {s : Fin 2 → Fin 4}

/-- The vector with prescribed pivot and free coordinates. -/
def rankTwoGraphVector (k p : Fin 4) (s : Fin 2 → Fin 4)
    (b c : Fin 2 → K) : Fin 4 → K :=
  (Pi.single k (b 0) : Fin 4 → K) + Pi.single p (b 1) +
    Pi.single (s 0) (c 0) + Pi.single (s 1) (c 1)

theorem rankTwoGraphVector_add
    (b c d e : Fin 2 → K) :
    rankTwoGraphVector k p s b c + rankTwoGraphVector k p s d e =
      rankTwoGraphVector k p s (b+d) (c+e) := by
  funext i
  have hs (l : Fin 4) (a b : K) :
      (Pi.single l (a+b) : Fin 4 → K) i =
        (Pi.single l a : Fin 4 → K) i + (Pi.single l b : Fin 4 → K) i := by
    by_cases h : i = l
    · subst i
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne h,add_zero]
  simp only [rankTwoGraphVector,Pi.add_apply,hs]
  abel

theorem rankTwoGraphVector_eta (hc : RankTwoGraphCoordinates k p s)
    (v : Fin 4 → K) :
    rankTwoGraphVector k p s ![v k,v p] (v ∘ s) = v := by
  classical
  obtain ⟨hkp,hinj,hs,hcover⟩ := hc
  have h01 : s 0 ≠ s 1 := hinj.ne (by decide)
  funext i
  rcases hcover i with hi | hi | ⟨j,hj⟩
  · subst i
    simp [rankTwoGraphVector,Ne.symm hkp,Ne.symm (hs 0).1,Ne.symm (hs 1).1]
  · subst i
    simp [rankTwoGraphVector,Ne.symm hkp,Ne.symm (hs 0).2,Ne.symm (hs 1).2]
  · subst i
    fin_cases j
    · simp [rankTwoGraphVector,(hs 0).1,(hs 0).2,h01]
    · simp [rankTwoGraphVector,(hs 1).1,(hs 1).2,Ne.symm h01]

def rankTwoKernelGraph (A : Matrix (Fin 4) (Fin 4) K)
    (k p : Fin 4) (s : Fin 2 → Fin 4) : Matrix (Fin 2) (Fin 2) K :=
  (rankTwoPrincipalPivot A k p)⁻¹ • rankTwoGraphNumerator A k p s

/-- Every graph vector is in the evaluated Hessian kernel. -/
theorem rankTwoKernelGraph_mem_kernel
    (A : Matrix (Fin 4) (Fin 4) K) (hA : AllThreeMinorsZero A)
    (hreg : rankTwoPrincipalPivot A k p ≠ 0) (c : Fin 2 → K) :
    A *ᵥ rankTwoGraphVector k p s (rankTwoKernelGraph A k p s *ᵥ c) c = 0 := by
  classical
  let Δ := rankTwoPrincipalPivot A k p
  let G := rankTwoKernelGraph A k p s
  have hG0 : Δ * (G *ᵥ c) 0 =
      -((A p p * A k (s 0) - A k p * A p (s 0)) * c 0 +
        (A p p * A k (s 1) - A k p * A p (s 1)) * c 1) := by
    change Δ * (∑ j : Fin 2, (Δ⁻¹ * rankTwoGraphNumerator A k p s 0 j) * c j) = _
    rw [Fin.sum_univ_two]
    change Δ * ((Δ⁻¹ * (-(A p p * A k (s 0) - A k p * A p (s 0)))) * c 0 +
      (Δ⁻¹ * (-(A p p * A k (s 1) - A k p * A p (s 1)))) * c 1) = _
    rw [mul_add]
    have h (a b : K) : Δ * (Δ⁻¹ * a * b) = a*b := by
      rw [← mul_assoc,← mul_assoc,mul_inv_cancel₀ hreg,one_mul]
    rw [h,h]
    ring
  have hG1 : Δ * (G *ᵥ c) 1 =
      -((A k k * A p (s 0) - A p k * A k (s 0)) * c 0 +
        (A k k * A p (s 1) - A p k * A k (s 1)) * c 1) := by
    change Δ * (∑ j : Fin 2, (Δ⁻¹ * rankTwoGraphNumerator A k p s 1 j) * c j) = _
    rw [Fin.sum_univ_two]
    simp only [rankTwoGraphNumerator,if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [mul_add]
    have h (a b : K) : Δ * (Δ⁻¹ * a * b) = a*b := by
      rw [← mul_assoc,← mul_assoc,mul_inv_cancel₀ hreg,one_mul]
    rw [h,h]
    ring
  unfold rankTwoGraphVector
  rw [Matrix.mulVec_add,Matrix.mulVec_add,Matrix.mulVec_add,
    Matrix.mulVec_single,Matrix.mulVec_single,Matrix.mulVec_single,Matrix.mulVec_single]
  funext i
  change A i k * (G *ᵥ c) 0 + A i p * (G *ᵥ c) 1 +
    A i (s 0) * c 0 + A i (s 1) * c 1 = 0
  apply mul_left_cancel₀ hreg
  rw [mul_zero]
  change Δ * _ = 0
  have h0 := rankTwo_schur_cross A hA k p i (s 0)
  have h1 := rankTwo_schur_cross A hA k p i (s 1)
  change Δ * A i (s 0) = _ at h0
  change Δ * A i (s 1) = _ at h1
  linear_combination A i k * hG0 + A i p * hG1 + c 0 * h0 + c 1 * h1

/-- Invertible difference of graph maps gives complementary
kernel spaces, by an explicit solution of the two-coordinate system. -/
theorem rankTwoKernelGraph_sup_eq_top_of_det_ne_zero
    (A D : Matrix (Fin 4) (Fin 4) K)
    (hA : AllThreeMinorsZero A) (hD : AllThreeMinorsZero D)
    (hc : RankTwoGraphCoordinates k p s)
    (ha : rankTwoPrincipalPivot A k p ≠ 0)
    (hd : rankTwoPrincipalPivot D k p ≠ 0)
    (hdet : (rankTwoKernelGraph A k p s - rankTwoKernelGraph D k p s).det ≠ 0) :
    LinearMap.ker A.mulVecLin ⊔ LinearMap.ker D.mulVecLin = ⊤ := by
  classical
  let G := rankTwoKernelGraph A k p s
  let J := rankTwoKernelGraph D k p s
  have hsurj : Function.Surjective (G-J).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hdet))
  apply top_unique
  intro v _
  let b : Fin 2 → K := ![v k,v p]
  let c : Fin 2 → K := v ∘ s
  obtain ⟨u,hu⟩ := hsurj (b-J *ᵥ c)
  let t := c-u
  have hfree : u+t = c := by dsimp [t]; abel
  have hpivot : G *ᵥ u + J *ᵥ t = b := by
    have he : G *ᵥ u - J *ᵥ u = b-J *ᵥ c := by
      rw [← Matrix.sub_mulVec]
      exact hu
    dsimp [t]
    rw [Matrix.mulVec_sub]
    calc
      G *ᵥ u + (J *ᵥ c - J *ᵥ u) =
        (G *ᵥ u - J *ᵥ u) + J *ᵥ c := by abel
      _ = b := by rw [he]; abel
  apply Submodule.mem_sup.mpr
  refine ⟨rankTwoGraphVector k p s (G *ᵥ u) u,?_,
    rankTwoGraphVector k p s (J *ᵥ t) t,?_,?_⟩
  · exact rankTwoKernelGraph_mem_kernel A hA ha u
  · exact rankTwoKernelGraph_mem_kernel D hD hd t
  · rw [rankTwoGraphVector_add,hpivot,hfree]
    exact rankTwoGraphVector_eta hc v

end Graph

/-- Vanishing on the complement of the zero set of a nonzero
polynomial forces a polynomial identity over a characteristic-zero
field. This is the sole density principle used here. -/
theorem rankTwo_polynomial_eq_zero_of_regular_eval
    (f q : B K) (hf : f ≠ 0)
    (hq : ∀ x : Fin 4 → K, MvPolynomial.eval x f ≠ 0 → MvPolynomial.eval x q = 0) :
    q = 0 := by
  have h : f*q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul,map_zero]
    by_cases hx : MvPolynomial.eval x f = 0
    · rw [hx,zero_mul]
    · rw [hq x hx,mul_zero]
  exact (mul_eq_zero.mp h).resolve_left hf

/-- The difference of kernel graph numerators, with both
denominators cleared, has vanishing determinant for every regular
pair, even when the gradients are equal. -/
theorem rankTwo_kernelGraph_difference_det_zero
    (L : B K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (s : Fin 2 → Fin 4) (hc : RankTwoGraphCoordinates k p s)
    (x : Fin 4 → K)
    (hx : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (r j : Fin 4) (hnc : hessian L r j ≠ 0) :
    let A := hessian L
    let Δ := rankTwoPrincipalPivot A k p
    let N := rankTwoGraphNumerator A k p s
    ((MvPolynomial.C (MvPolynomial.eval x Δ) : B K) • N -
      Δ • ((N.map (MvPolynomial.eval x)).map (MvPolynomial.C : K →+* B K)) :
        Matrix (Fin 2) (Fin 2) (B K)).det = 0 := by
  classical
  let A := hessian L
  let Δ := rankTwoPrincipalPivot A k p
  let N := rankTwoGraphNumerator A k p s
  let a := MvPolynomial.eval x Δ
  let Q : Matrix (Fin 2) (Fin 2) (B K) :=
    (MvPolynomial.C a : B K) • N -
      Δ • ((N.map (MvPolynomial.eval x)).map (MvPolynomial.C : K →+* B K))
  let F := pderiv r L - MvPolynomial.C (MvPolynomial.eval x (pderiv r L))
  have hF : F ≠ 0 := by
    intro h
    have he := congrArg (pderiv j) h
    change pderiv j (pderiv r L - MvPolynomial.C (MvPolynomial.eval x (pderiv r L))) =
      pderiv j (0 : B K) at he
    rw [map_sub,pderiv_C,sub_zero,map_zero] at he
    exact hnc he
  have hΔ : Δ ≠ 0 := by
    intro h
    exact hx (by change MvPolynomial.eval x Δ = 0; rw [h,map_zero])
  change Q.det = 0
  apply rankTwo_polynomial_eq_zero_of_regular_eval (Δ*F) Q.det (mul_ne_zero hΔ hF)
  intro y hy
  have hprod : MvPolynomial.eval y Δ * MvPolynomial.eval y F ≠ 0 := by
    simpa only [map_mul] using hy
  have hyΔ : MvPolynomial.eval y Δ ≠ 0 := fun h => hprod (by rw [h,zero_mul])
  have hyF : MvPolynomial.eval y F ≠ 0 := fun h => hprod (by rw [h,mul_zero])
  have hxy : mvGradientMap L x ≠ mvGradientMap L y := by
    intro h
    apply hyF
    have he := congrFun h r
    change MvPolynomial.eval x (pderiv r L) = MvPolynomial.eval y (pderiv r L) at he
    change MvPolynomial.eval y (pderiv r L - MvPolynomial.C (MvPolynomial.eval x (pderiv r L))) = 0
    rw [map_sub,MvPolynomial.eval_C,he,sub_self]
  let U := A.map (MvPolynomial.eval x)
  let V := A.map (MvPolynomial.eval y)
  let b := MvPolynomial.eval y Δ
  have ha : a ≠ 0 := hx
  have hb : b ≠ 0 := hyΔ
  have hpa : rankTwoPrincipalPivot U k p = a :=
    (rankTwoPrincipalPivot_map A (MvPolynomial.eval x) k p).symm
  have hpb : rankTwoPrincipalPivot V k p = b :=
    (rankTwoPrincipalPivot_map A (MvPolynomial.eval y) k p).symm
  have hdiff : (rankTwoKernelGraph V k p s - rankTwoKernelGraph U k p s).det = 0 := by
    by_contra hn
    have hh := rankTwoKernelGraph_sup_eq_top_of_det_ne_zero V U
      (hL.map (MvPolynomial.eval y)) (hL.map (MvPolynomial.eval x)) hc
      (by rw [hpb]; exact hb) (by rw [hpa]; exact ha) hn
    exact rankTwo_distinctGradient_kernel_sup_ne_top L hL k p hc.1 y x hyΔ hx
      (Ne.symm hxy) hh
  have hQ : Q.map (MvPolynomial.eval y) =
      (a*b) • (rankTwoKernelGraph V k p s - rankTwoKernelGraph U k p s) := by
    apply Matrix.ext
    intro i j
    have hNx := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M i j)
      (rankTwoGraphNumerator_map A (MvPolynomial.eval x) k p s)
    have hNy := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M i j)
      (rankTwoGraphNumerator_map A (MvPolynomial.eval y) k p s)
    change MvPolynomial.eval x (N i j) = rankTwoGraphNumerator U k p s i j at hNx
    change MvPolynomial.eval y (N i j) = rankTwoGraphNumerator V k p s i j at hNy
    change MvPolynomial.eval y (MvPolynomial.C a * N i j -
      Δ * MvPolynomial.C (MvPolynomial.eval x (N i j))) =
      a*b * ((rankTwoPrincipalPivot V k p)⁻¹ * rankTwoGraphNumerator V k p s i j -
        (rankTwoPrincipalPivot U k p)⁻¹ * rankTwoGraphNumerator U k p s i j)
    rw [map_sub,map_mul,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_C,hNx,hNy,hpa,hpb]
    change a * _ - b * _ = _
    field_simp [ha,hb] <;> ring
  change MvPolynomial.eval y Q.det = 0
  rw [RingHom.map_det]
  change (Q.map (MvPolynomial.eval y)).det = 0
  rw [hQ,Matrix.det_smul,hdiff,mul_zero]

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwoKernelGraph_mem_kernel
#print axioms HC4.Polynomial.rankTwoKernelGraph_sup_eq_top_of_det_ne_zero
#print axioms HC4.Polynomial.rankTwo_kernelGraph_difference_det_zero
