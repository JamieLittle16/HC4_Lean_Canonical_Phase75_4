import HC4.Polynomial.RankTwoImageDirectionClosure

/-!
# Actual principal rank-two pivot and image equations

A surviving positive-clock rank-two Hessian has a nonzero principal
two-by-two minor at every specified diagonal pivot. Otherwise the
order-three principal minor identity makes all rows proportional
to that pivot, and the verified two-row rigidity yields a constant
kernel.

At a regular two-by-two pivot the image condition is equivalent
to explicit denominator-cleared two-column equations. This gives
a concrete polynomial target for the remaining image existence
theorem; it does not assert existence of a constant image vector.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

section Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

def rankTwoPrincipalPivot (A : Matrix (Fin 4) (Fin 4) R) (k p : Fin 4) : R :=
  A k k * A p p - A k p * A p k

/-- The cross-multiplied Schur-complement identity from a genuine
order-three minor. Repeated indices are allowed. -/
theorem rankTwo_schur_cross
    (A : Matrix (Fin 4) (Fin 4) R) (hA : AllThreeMinorsZero A)
    (k p i j : Fin 4) :
    rankTwoPrincipalPivot A k p * A i j =
      A i k * (A p p * A k j - A k p * A p j) +
      A i p * (A k k * A p j - A p k * A k j) := by
  have h := hA (![k,p,i] : Fin 3 → Fin 4) (![k,p,j] : Fin 3 → Fin 4)
  rw [Matrix.det_fin_three] at h
  change A k k * A p p * A i j - A k k * A p j * A i p -
    A k p * A p k * A i j + A k p * A p j * A i k +
    A k j * A p k * A i p - A k j * A p p * A i k = 0 at h
  unfold rankTwoPrincipalPivot
  linear_combination h

/-- If every principal two-minor through k vanishes, symmetry and
the three-minor equation force the entire Schur complement to vanish. -/
theorem rankTwo_zeroPrincipalPivots_crossProducts
    (A : Matrix (Fin 4) (Fin 4) R) (hs : ∀ i j, A i j = A j i)
    (hA : AllThreeMinorsZero A)
    (k : Fin 4) (hk : A k k ≠ 0)
    (hp : ∀ p, rankTwoPrincipalPivot A k p = 0) :
    ∀ i j, A k k * A i j = A i k * A k j := by
  intro i j
  have hi := hp i
  unfold rankTwoPrincipalPivot at hi
  rw [hs k i] at hi
  have he := rankTwo_schur_cross A hA k i j j
  rw [hp i,zero_mul] at he
  have hsij : A j i = A i j := hs j i
  rw [hsij,hs j k,hs k i] at he
  have hsq : (A k k * A i j - A i k * A k j)^2 = 0 := by
    linear_combination -A k k * he - (A k j)^2 * hi
  rw [pow_two] at hsq
  rcases mul_eq_zero.mp hsq with h | h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mp h

/-- A vector satisfies the two-column image equations exactly
when its multiple by the pivot is in the original column image.
This supplies a polynomial witness without division. -/
theorem rankTwo_imageWitness_of_pivotEquations
    (A : Matrix (Fin 4) (Fin 4) R) (k p : Fin 4) (hkp : k ≠ p)
    (d : Fin 4 → R)
    (h : ∀ i, rankTwoPrincipalPivot A k p * d i =
      A i k * (A p p * d k - A k p * d p) +
      A i p * (A k k * d p - A p k * d k)) :
    ∃ z : Fin 4 → R, A *ᵥ z = fun i => rankTwoPrincipalPivot A k p * d i := by
  classical
  let b := A p p * d k - A k p * d p
  let c := A k k * d p - A p k * d k
  let z : Fin 4 → R := (Pi.single k b : Fin 4 → R) + Pi.single p c
  refine ⟨z,?_⟩
  change A *ᵥ ((Pi.single k b : Fin 4 → R) + Pi.single p c) = _
  rw [Matrix.mulVec_add,Matrix.mulVec_single,Matrix.mulVec_single]
  funext i
  change A i k * b + A i p * c = _
  exact (h i).symm

/-- Every actual image vector satisfies the two-column equations.
This is just the summed cross-multiplied Schur identity. -/
theorem rankTwo_pivotEquations_of_image
    (A : Matrix (Fin 4) (Fin 4) R) (hA : AllThreeMinorsZero A)
    (k p : Fin 4) (z : Fin 4 → R) :
    ∀ i, rankTwoPrincipalPivot A k p * (A *ᵥ z) i =
      A i k * (A p p * (A *ᵥ z) k - A k p * (A *ᵥ z) p) +
      A i p * (A k k * (A *ᵥ z) p - A p k * (A *ᵥ z) k) := by
  classical
  intro i
  change rankTwoPrincipalPivot A k p * (∑ j : Fin 4, A i j * z j) =
    A i k * (A p p * (∑ j : Fin 4, A k j * z j) -
      A k p * (∑ j : Fin 4, A p j * z j)) +
    A i p * (A k k * (∑ j : Fin 4, A p j * z j) -
      A p k * (∑ j : Fin 4, A k j * z j))
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination z j * rankTwo_schur_cross A hA k p i j

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- A genuine rank-two candidate has a regular principal
two-by-two block through every fixed coordinate. -/
theorem globalWeightOptimum_rankTwo_exists_principalPivot
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hL : AllThreeMinorsZero (hessian (initialForm w m P))) (k : Fin 4) :
    ∃ p : Fin 4, p ≠ k ∧
      rankTwoPrincipalPivot (hessian (initialForm w m P)) k p ≠ 0 := by
  classical
  let L := initialForm w m P
  let A := hessian L
  have hk : A k k ≠ 0 :=
    globalWeightOptimum_rankTwo_no_affineCoordinate P w m hw hm hcap hclock hopt hdet hL k
  by_contra hn
  have hp (p : Fin 4) : rankTwoPrincipalPivot A k p = 0 := by
    by_cases hpk : p = k
    · subst p
      unfold rankTwoPrincipalPivot
      ring
    · by_contra he
      exact hn ⟨p,hpk,he⟩
  have hs (i j : Fin 4) : A i j = A j i := pderiv_comm_backport j i L
  have hc := rankTwo_zeroPrincipalPivots_crossProducts A hs hL k hk hp
  have hex : ∃ i : Fin 4, i ≠ k := by fin_cases k <;> decide
  obtain ⟨i,hi⟩ := hex
  obtain ⟨c,hc'⟩ := rankOneHessian_twoRows_constant L k i hi hk (hc i)
  obtain ⟨d,hd,hker⟩ := rankOne_kernel_of_proportional_columns L k i hi c (by
    intro j
    rw [show hessian L j i = hessian L i j from hs j i,
      show hessian L j k = hessian L k j from hs j k]
    exact hc' j)
  exact hd (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap hclock hopt hdet d hker)

/-- Exact remaining rank-two image condition, on the original
polynomial Hessian. A nonzero constant solution of these linear
polynomial identities contradicts the global optimum. -/
theorem globalWeightOptimum_rankTwo_no_constantPivotSolution
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hL : AllThreeMinorsZero (hessian (initialForm w m P)))
    (k p : Fin 4) (hkp : k ≠ p)
    (hreg : rankTwoPrincipalPivot (hessian (initialForm w m P)) k p ≠ 0)
    (d : Fin 4 → K)
    (hd : let A := hessian (initialForm w m P)
      ∀ i, rankTwoPrincipalPivot A k p * MvPolynomial.C (d i) =
        A i k * (A p p * MvPolynomial.C (d k) - A k p * MvPolynomial.C (d p)) +
        A i p * (A k k * MvPolynomial.C (d p) - A p k * MvPolynomial.C (d k))) :
    d = 0 := by
  by_contra hn
  let A := hessian (initialForm w m P)
  obtain ⟨z,hz⟩ := rankTwo_imageWitness_of_pivotEquations A k p hkp
    (fun i => MvPolynomial.C (d i)) hd
  exact globalWeightOptimum_rankTwo_no_constantImage P w m hw hm hcap hclock hopt hdet
    hL d hn z (rankTwoPrincipalPivot A k p) hreg hz

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_schur_cross
#print axioms HC4.Polynomial.globalWeightOptimum_rankTwo_exists_principalPivot
#print axioms HC4.Polynomial.globalWeightOptimum_rankTwo_no_constantPivotSolution
