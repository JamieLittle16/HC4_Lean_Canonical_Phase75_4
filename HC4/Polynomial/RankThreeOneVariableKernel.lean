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
    exact one_ne_zero (by simpa using hl)
  · funext i
    apply IsFractionRing.injective (B K) (E K)
    change f (∑ j : Fin 4, hessian L i j * MvPolynomial.C (d j)) = f 0
    simp only [map_sum,map_mul,map_zero]
    have hC (a : K) : f (MvPolynomial.C a) = algebraMap K (E K) a :=
      (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    simp only [hC,← hd]
    exact congrFun hV i

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankThree_oneVariableKernel_derivative_rows
#print axioms HC4.Polynomial.rankThree_oneVariableKernel_constant
