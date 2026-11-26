import HC4.Polynomial.RankTwoAffineClosure

/-!
# Rank-two constant image direction closure

An actual constant direction in the Hessian image can be aligned
with a coordinate. In that chart the other three Hessian rows
have rank at most one. Full row proportionality, together with
the polynomial tangent obstruction, forces constant ratios and
hence a genuine constant Hessian kernel.

The image-direction existence is deliberately not assumed in the
unrestricted theorem: the conditional endpoint here isolates
exactly the missing geometric input.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

section Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nonzero coordinate vector in the image forces every minor
of order two off that row to vanish. The witness is polynomial
and may be denominator-cleared. -/
theorem rankTwo_coordinateImage_rowMinors
    (A : Matrix (Fin 4) (Fin 4) R) (hA : AllThreeMinorsZero A)
    (k : Fin 4) (z : Fin 4 → R) (a : R) (ha : a ≠ 0)
    (hz : A *ᵥ z = Pi.single k a)
    (i j : Fin 4) (hik : i ≠ k) (hjk : j ≠ k)
    (p q : Fin 4) :
    A i p * A j q = A i q * A j p := by
  classical
  have hdet (l : Fin 4) :
      A k l * (A i p * A j q - A i q * A j p) -
      A i l * (A k p * A j q - A k q * A j p) +
      A j l * (A k p * A i q - A k q * A i p) = 0 := by
    have he := hA (![k,i,j] : Fin 3 → Fin 4) (![l,p,q] : Fin 3 → Fin 4)
    rw [Matrix.det_fin_three] at he
    change A k l * A i p * A j q - A k l * A i q * A j p -
      A k p * A i l * A j q + A k p * A i q * A j l +
      A k q * A i l * A j p - A k q * A i p * A j l = 0 at he
    linear_combination he
  have hsum (l : Fin 4) : (∑ t : Fin 4, A l t * z t) =
      (Pi.single k a : Fin 4 → R) l :=
    congrFun hz l
  have hk : (∑ t : Fin 4, A k t * z t) = a := by simpa using hsum k
  have hi : (∑ t : Fin 4, A i t * z t) = 0 := by
    simpa only [Pi.single_eq_of_ne hik] using hsum i
  have hj : (∑ t : Fin 4, A j t * z t) = 0 := by
    simpa only [Pi.single_eq_of_ne hjk] using hsum j
  have h :
      (∑ l : Fin 4, A k l * z l) * (A i p * A j q - A i q * A j p) -
      (∑ l : Fin 4, A i l * z l) * (A k p * A j q - A k q * A j p) +
      (∑ l : Fin 4, A j l * z l) * (A k p * A i q - A k q * A i p) = 0 := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l _
    linear_combination z l * hdet l
  rw [hk,hi,hj,zero_mul,zero_mul,sub_zero,add_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ha)

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- A rank-two Hessian with a coordinate image direction has
either a zero diagonal or a nonzero constant Hessian kernel. -/
theorem rankTwo_coordinateImage_affine_or_kernel
    (L : S K) (hL : AllThreeMinorsZero (hessian L))
    (k : Fin 4) (z : Fin 4 → S K) (a : S K) (ha : a ≠ 0)
    (hz : hessian L *ᵥ z = Pi.single k a) :
    (∃ i : Fin 4, hessian L i i = 0) ∨
      ∃ d : Fin 4 → K, d ≠ 0 ∧
        hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  by_cases he : ∃ i : Fin 4, hessian L i i = 0
  · exact Or.inl he
  push_neg at he
  have hp : ∃ p i : Fin 4, p ≠ k ∧ i ≠ k ∧ i ≠ p := by
    fin_cases k <;> decide
  obtain ⟨p,i,hpk,hik,hip⟩ := hp
  have hr (j : Fin 4) : hessian L p p * hessian L i j =
      hessian L i p * hessian L p j := by
    rw [mul_comm (hessian L i p)]
    exact rankTwo_coordinateImage_rowMinors (hessian L) hL k z a ha hz p i hpk hik p j
  obtain ⟨c,hc⟩ := rankOneHessian_twoRows_constant L p i hip (he p) hr
  apply Or.inr
  apply rankOne_kernel_of_proportional_columns L p i hip c
  intro j
  rw [show hessian L j i = hessian L i j from pderiv_comm_backport i j L,
    show hessian L j p = hessian L p j from pderiv_comm_backport p j L]
  exact hc j

/-- No coordinate image direction is possible in any actual
determinant-one chart of a positive-clock optimal rank-two source. -/
theorem globalWeightOptimum_rankTwo_no_coordinateImage_chart
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hL : AllThreeMinorsZero (hessian (initialForm w m P)))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : M.det = 1)
    (k : Fin 4) (z : Fin 4 → S K) (a : S K) (ha : a ≠ 0) :
    hessian (weightedLinearSubstitution M (initialForm w m P)) *ᵥ z ≠
      Pi.single k a := by
  intro hz
  let L := initialForm w m P
  let Q := weightedLinearSubstitution M L
  have hQ : AllThreeMinorsZero (hessian Q) :=
    rankTwo_allThreeMinorsZero_substitution L M hL
  rcases rankTwo_coordinateImage_affine_or_kernel Q hQ k z a ha hz with he | he
  · obtain ⟨i,hi⟩ := he
    exact globalWeightOptimum_rankTwo_no_affineChart P w m hw hm hcap hclock hopt hdet hL M hM i hi
  · obtain ⟨d,hd,hker⟩ := he
    obtain ⟨e,he0,heker⟩ := rankOne_constantKernel_pullback L M hM d hd hker
    exact he0 (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap hclock hopt hdet e heker)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_coordinateImage_rowMinors
#print axioms HC4.Polynomial.rankTwo_coordinateImage_affine_or_kernel
#print axioms HC4.Polynomial.globalWeightOptimum_rankTwo_no_coordinateImage_chart
