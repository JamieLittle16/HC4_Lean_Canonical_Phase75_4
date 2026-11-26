import HC4.Polynomial.RankTwoAffineLevelCurvature

/-!
# Source-honest rank-two minor transport

Vanishing of all three-by-three minors is preserved by arbitrary
left and right multiplication over a commutative ring. Expand the
determinant as a multilinear map on its rows. Each summand is a
scalar multiple of an original minor (allowing repeated indices).

Apply this to the exact Hessian congruence of a linear substitution.
No rank assumption about the transformed polynomial is introduced.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

section Matrix

variable {R : Type*} [CommRing R]

/-- All order-three minors vanish, with repeated indices allowed. -/
def AllThreeMinorsZero (A : Matrix (Fin 4) (Fin 4) R) : Prop :=
  ∀ r c : Fin 3 → Fin 4, (A.submatrix r c).det = 0

theorem AllThreeMinorsZero.left_mul
    {A : Matrix (Fin 4) (Fin 4) R} (hA : AllThreeMinorsZero A)
    (M : Matrix (Fin 4) (Fin 4) R) :
    AllThreeMinorsZero (M*A) := by
  classical
  intro r c
  let D : MultilinearMap R (fun _ : Fin 3 => Fin 3 → R) R :=
    Matrix.detRowAlternating.toMultilinearMap
  let g (i : Fin 3) (j : Fin 4) : Fin 3 → R :=
    M (r i) j • (fun k => A j (c k))
  have hsum : (M*A).submatrix r c = fun i => ∑ j : Fin 4, g i j := by
    apply Matrix.ext
    intro i k
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Finset.sum_apply,
      g, Pi.smul_apply, smul_eq_mul]
  change D ((M*A).submatrix r c) = 0
  rw [hsum, D.map_sum]
  apply Finset.sum_eq_zero
  intro p _
  change D (fun i => M (r i) (p i) • (fun k => A (p i) (c k))) = 0
  rw [D.map_smul_univ]
  change (∏ i : Fin 3, M (r i) (p i)) • (A.submatrix p c).det = 0
  rw [hA p c, smul_zero]

theorem AllThreeMinorsZero.transpose
    {A : Matrix (Fin 4) (Fin 4) R} (hA : AllThreeMinorsZero A) :
    AllThreeMinorsZero A.transpose := by
  intro r c
  have he : A.transpose.submatrix r c = (A.submatrix c r).transpose := rfl
  rw [he, Matrix.det_transpose]
  exact hA c r

theorem AllThreeMinorsZero.right_mul
    {A : Matrix (Fin 4) (Fin 4) R} (hA : AllThreeMinorsZero A)
    (M : Matrix (Fin 4) (Fin 4) R) :
    AllThreeMinorsZero (A*M) := by
  have he := ((hA.transpose).left_mul M.transpose).transpose
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose] at he
  exact he

theorem AllThreeMinorsZero.map
    {T : Type*} [CommRing T]
    {A : Matrix (Fin 4) (Fin 4) R} (hA : AllThreeMinorsZero A)
    (f : R →+* T) : AllThreeMinorsZero (A.map f) := by
  intro r c
  change (f.mapMatrix (A.submatrix r c)).det = 0
  rw [← RingHom.map_det, hA r c, map_zero]

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- The order-three minor condition survives the actual Hessian
substitution, even in a chart that changes the original weights. -/
theorem rankTwo_allThreeMinorsZero_substitution
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K)
    (hL : AllThreeMinorsZero (hessian L)) :
    AllThreeMinorsZero (hessian (weightedLinearSubstitution M L)) := by
  rw [weightedLinearSubstitution_hessian]
  exact ((hL.map (weightedLinearSubstitution M).toRingHom).left_mul
    (M.map (MvPolynomial.C : K →+* S K)).transpose).right_mul (M.map MvPolynomial.C)

/-- The affine scalar flatness identity in any genuine chart whose
selected diagonal entry vanishes. The rank hypothesis is on L. -/
theorem rankTwo_affine_gradient_flatLevel_in_chart
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K) (k : Fin 4)
    (hL : AllThreeMinorsZero (hessian L))
    (hkk : hessian (weightedLinearSubstitution M L) k k = 0) :
    ∀ i j : Fin 4, let F := pderiv k (weightedLinearSubstitution M L)
      (pderiv i F)^2 * hessian F j j -
      2 * pderiv i F * pderiv j F * hessian F i j +
      (pderiv j F)^2 * hessian F i i = 0 := by
  exact rankTwo_affine_gradient_flatLevel _ k hkk
    (fun i j => rankTwo_allThreeMinorsZero_substitution L M hL
      (![k,i,j] : Fin 3 → Fin 4) (![k,i,j] : Fin 3 → Fin 4))

end
end HC4.Polynomial

#print axioms HC4.Polynomial.AllThreeMinorsZero.left_mul
#print axioms HC4.Polynomial.rankTwo_allThreeMinorsZero_substitution
#print axioms HC4.Polynomial.rankTwo_affine_gradient_flatLevel_in_chart
