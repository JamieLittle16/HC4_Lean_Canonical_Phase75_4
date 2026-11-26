import HC4.Polynomial.RankTwoGraphDichotomy

/-!
# Complete rank-at-most-two extremal obstruction

Use the actual regular kernel graphs and the verified affine-fibre
density identity. The elementary singular-difference dichotomy
produces a constant kernel, or a constant image covector. Lift the
evaluated identities by polynomial density and apply the existing
global extremal contradictions.
-/

namespace HC4.Polynomial
open MvPolynomial HC4.Newton
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev R (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The polynomial difference identity implies the evaluated
singular difference, now with no distinct-gradient restriction. -/
theorem rankTwo_regularGraph_sub_det_zero
    (L : R K) (hL : AllThreeMinorsZero (hessian L))
    (k p : Fin 4) (s : Fin 2 → Fin 4) (hc : RankTwoGraphCoordinates k p s)
    (x y : Fin 4 → K)
    (hx : MvPolynomial.eval x (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (hy : MvPolynomial.eval y (rankTwoPrincipalPivot (hessian L) k p) ≠ 0)
    (r j : Fin 4) (hnc : hessian L r j ≠ 0) :
    (rankTwoKernelGraph ((hessian L).map (MvPolynomial.eval y)) k p s -
      rankTwoKernelGraph ((hessian L).map (MvPolynomial.eval x)) k p s).det = 0 := by
  classical
  let A := hessian L
  let Δ := rankTwoPrincipalPivot A k p
  let N := rankTwoGraphNumerator A k p s
  let a := MvPolynomial.eval x Δ
  let b := MvPolynomial.eval y Δ
  let Q : Matrix (Fin 2) (Fin 2) (R K) :=
    (MvPolynomial.C a : R K) • N -
      Δ • ((N.map (MvPolynomial.eval x)).map (MvPolynomial.C : K →+* R K))
  let U := A.map (MvPolynomial.eval x)
  let V := A.map (MvPolynomial.eval y)
  have ha : a ≠ 0 := hx
  have hb : b ≠ 0 := hy
  have hpa : rankTwoPrincipalPivot U k p = a :=
    (rankTwoPrincipalPivot_map A (MvPolynomial.eval x) k p).symm
  have hpb : rankTwoPrincipalPivot V k p = b :=
    (rankTwoPrincipalPivot_map A (MvPolynomial.eval y) k p).symm
  have hQ0 : Q.det = 0 :=
    rankTwo_kernelGraph_difference_det_zero L hL k p s hc x hx r j hnc
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
  have he := congrArg (MvPolynomial.eval y) hQ0
  change MvPolynomial.eval y Q.det = MvPolynomial.eval y 0 at he
  rw [map_zero,RingHom.map_det] at he
  change (Q.map (MvPolynomial.eval y)).det = 0 at he
  rw [hQ,Matrix.det_smul] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (mul_ne_zero ha hb))

/-- Read the pivot coordinates of a graph vector. -/
theorem rankTwoGraphVector_pivot
    {k p : Fin 4} {s : Fin 2 → Fin 4} (hc : RankTwoGraphCoordinates k p s)
    (b c : Fin 2 → K) :
    rankTwoGraphVector k p s b c k = b 0 ∧
      rankTwoGraphVector k p s b c p = b 1 := by
  obtain ⟨hkp,_,hs,_⟩ := hc
  constructor
  · simp [rankTwoGraphVector,Ne.symm hkp,Ne.symm (hs 0).1,Ne.symm (hs 1).1]
  · simp [rankTwoGraphVector,Ne.symm hkp,Ne.symm (hs 0).2,Ne.symm (hs 1).2]

theorem rankTwoGraphVector_free
    {k p : Fin 4} {s : Fin 2 → Fin 4} (hc : RankTwoGraphCoordinates k p s)
    (b c : Fin 2 → K) (j : Fin 2) :
    rankTwoGraphVector k p s b c (s j) = c j := by
  obtain ⟨_,hinj,hs,_⟩ := hc
  have h01 : s 0 ≠ s 1 := hinj.ne (by decide)
  fin_cases j
  · simp [rankTwoGraphVector,(hs 0).1,(hs 0).2,h01]
  · simp [rankTwoGraphVector,(hs 1).1,(hs 1).2,Ne.symm h01]

/-- The graph of minus the transpose, in pivot/free coordinates,
is in the image of a symmetric rank-two matrix. Prove the exact
denominator-cleared image equations. -/
theorem rankTwo_graphNormal_pivotEquations
    (A : Matrix (Fin 4) (Fin 4) K) (hs : ∀ i j, A i j = A j i)
    (k p : Fin 4) (s : Fin 2 → Fin 4) (hc : RankTwoGraphCoordinates k p s)
    (hreg : rankTwoPrincipalPivot A k p ≠ 0) (c : Fin 2 → K)
    (d : Fin 4 → K)
    (hdk : d k = c 0) (hdp : d p = c 1)
    (hds : ∀ j, d (s j) = -(c ᵥ* rankTwoKernelGraph A k p s) j) :
    ∀ i, rankTwoPrincipalPivot A k p * d i =
      A i k * (A p p * d k - A k p * d p) +
      A i p * (A k k * d p - A p k * d k) := by
  intro i
  rcases hc.2.2.2 i with hi | hi | ⟨j,hj⟩
  · subst i
    unfold rankTwoPrincipalPivot
    ring
  · subst i
    unfold rankTwoPrincipalPivot
    ring
  · subst i
    rw [hds j,hdk,hdp]
    let Δ := rankTwoPrincipalPivot A k p
    change Δ * (-(∑ a : Fin 2, c a *
      (Δ⁻¹ * rankTwoGraphNumerator A k p s a j))) = _
    rw [Fin.sum_univ_two]
    change Δ * (-(c 0 * (Δ⁻¹ * (-(A p p * A k (s j) - A k p * A p (s j)))) +
      c 1 * (Δ⁻¹ * (-(A k k * A p (s j) - A p k * A k (s j)))))) = _
    rw [hs (s j) k,hs (s j) p]
    have hδ : Δ ≠ 0 := hreg
    field_simp [hδ]
    rw [hs p k]
    ring

set_option maxHeartbeats 4000000 in
/-- The unconditional rank-at-most-two contradiction on the
original positive-clock global optimum. No image apex or affine
coordinate assumption remains. -/
theorem globalWeightOptimum_not_rankAtMostTwo
    (P : R K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1) :
    ¬ AllThreeMinorsZero (hessian (initialForm w m P)) := by
  classical
  intro hL
  let L := initialForm w m P
  let A := hessian L
  let k : Fin 4 := 0
  obtain ⟨p,hpk,hreg⟩ :=
    globalWeightOptimum_rankTwo_exists_principalPivot P w m hw hm hcap hclock hopt hdet hL k
  have hk : A k k ≠ 0 :=
    globalWeightOptimum_rankTwo_no_affineCoordinate P w m hw hm hcap hclock hopt hdet hL k
  obtain ⟨s,hc⟩ := rankTwo_exists_graphCoordinates k p (Ne.symm hpk)
  let Δ := rankTwoPrincipalPivot A k p
  have hΔ : Δ ≠ 0 := hreg
  let T := {x : Fin 4 → K // MvPolynomial.eval x Δ ≠ 0}
  have hex : ∃ x : Fin 4 → K, MvPolynomial.eval x Δ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hΔ
    apply MvPolynomial.funext
    intro x
    rw [h x,map_zero]
  obtain ⟨x₀,hx₀⟩ := hex
  let t₀ : T := ⟨x₀,hx₀⟩
  let G (x : T) := rankTwoKernelGraph (A.map (MvPolynomial.eval x.val)) k p s
  let B (x : T) := G x - G t₀
  have hp (x y : T) : (G x - G y).det = 0 :=
    rankTwo_regularGraph_sub_det_zero L hL k p s hc y.val x.val y.property x.property k k hk
  have hB (x : T) : (B x).det = 0 := hp x t₀
  have hdiff (x y : T) : (B x - B y).det = 0 := by
    have he : B x - B y = G x - G y := by dsimp [B]; abel
    rw [he]
    exact hp x y
  rcases rankTwo_singularFamily_commonKernel_or_leftKernel B hB hdiff with hr | hl
  · obtain ⟨c,hc0,hcR⟩ := hr
    let d := rankTwoGraphVector k p s (G t₀ *ᵥ c) c
    have hd : d ≠ 0 := by
      intro he
      apply hc0
      funext j
      have hj := rankTwoGraphVector_free hc (G t₀ *ᵥ c) c j
      change d (s j) = c j at hj
      rw [he] at hj
      exact hj.symm
    have hker (x : T) : (A.map (MvPolynomial.eval x.val)) *ᵥ d = 0 := by
      have he := hcR x
      change (G x - G t₀) *ᵥ c = 0 at he
      rw [Matrix.sub_mulVec] at he
      have hh := sub_eq_zero.mp he
      change (A.map (MvPolynomial.eval x.val)) *ᵥ
        rankTwoGraphVector k p s (G t₀ *ᵥ c) c = 0
      rw [← hh]
      exact rankTwoKernelGraph_mem_kernel _ (hL.map (MvPolynomial.eval x.val))
        (by rw [← rankTwoPrincipalPivot_map]; exact x.property) c
    have hpoly : A *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
      funext i
      change (∑ j : Fin 4, A i j * MvPolynomial.C (d j)) = 0
      apply rankTwo_polynomial_eq_zero_of_regular_eval Δ _ hΔ
      intro x hx
      have he := congrFun (hker ⟨x,hx⟩) i
      change (∑ j : Fin 4, MvPolynomial.eval x (A i j) * d j) = 0 at he
      simp only [map_sum,map_mul,MvPolynomial.eval_C]
      exact he
    exact hd (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap hclock hopt hdet d hpoly)
  · obtain ⟨c,hc0,hcL⟩ := hl
    let d := rankTwoGraphVector k p s c (-(c ᵥ* G t₀))
    have hdpiv := rankTwoGraphVector_pivot hc c (-(c ᵥ* G t₀))
    have hdk : d k = c 0 := hdpiv.1
    have hdp : d p = c 1 := hdpiv.2
    have hd : d ≠ 0 := by
      intro he
      apply hc0
      funext j
      fin_cases j
      · rw [he] at hdk
        exact hdk.symm
      · rw [he] at hdp
        exact hdp.symm
    have heval (x : T) :
        ∀ i, rankTwoPrincipalPivot (A.map (MvPolynomial.eval x.val)) k p * d i =
          (MvPolynomial.eval x.val (A i k)) *
            (MvPolynomial.eval x.val (A p p) * d k - MvPolynomial.eval x.val (A k p) * d p) +
          (MvPolynomial.eval x.val (A i p)) *
            (MvPolynomial.eval x.val (A k k) * d p - MvPolynomial.eval x.val (A p k) * d k) := by
      have he := hcL x
      change c ᵥ* (G x - G t₀) = 0 at he
      rw [Matrix.vecMul_sub] at he
      have hh := sub_eq_zero.mp he
      have hs (i j : Fin 4) : (A.map (MvPolynomial.eval x.val)) i j =
          (A.map (MvPolynomial.eval x.val)) j i :=
        congrArg (MvPolynomial.eval x.val) (pderiv_comm_backport j i L)
      have hds (j : Fin 2) : d (s j) = -(c ᵥ* G x) j := by
        have hf := rankTwoGraphVector_free hc c (-(c ᵥ* G t₀)) j
        change d (s j) = (-(c ᵥ* G t₀)) j at hf
        rw [← hh] at hf
        exact hf
      exact rankTwo_graphNormal_pivotEquations _ hs k p s hc
        (by rw [← rankTwoPrincipalPivot_map]; exact x.property) c d hdk hdp hds
    have hpoly (i : Fin 4) :
        Δ * MvPolynomial.C (d i) =
          A i k * (A p p * MvPolynomial.C (d k) - A k p * MvPolynomial.C (d p)) +
          A i p * (A k k * MvPolynomial.C (d p) - A p k * MvPolynomial.C (d k)) := by
      apply sub_eq_zero.mp
      apply rankTwo_polynomial_eq_zero_of_regular_eval Δ _ hΔ
      intro x hx
      have he := heval ⟨x,hx⟩ i
      rw [← rankTwoPrincipalPivot_map] at he
      simp only [map_sub,map_mul,map_add,MvPolynomial.eval_C]
      exact sub_eq_zero.mpr he
    exact hd (globalWeightOptimum_rankTwo_no_constantPivotSolution P w m hw hm hcap hclock
      hopt hdet hL k p (Ne.symm hpk) hreg d hpoly)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_regularGraph_sub_det_zero
#print axioms HC4.Polynomial.rankTwo_graphNormal_pivotEquations
#print axioms HC4.Polynomial.globalWeightOptimum_not_rankAtMostTwo
