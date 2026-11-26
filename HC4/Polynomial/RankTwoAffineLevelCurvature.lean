module

public import HC4.Polynomial.WeightedExtremalIsotropicPlane

/-!
# Rank-two Hessian with an affine coordinate

If the leading Hessian has rank at most two and H_kk = 0,
the coefficient F = partial_k L is independent of x_k.
The principal three-by-three minor on (k,i,j) gives

  F_i^2 H_jj - 2 F_i F_j H_ij + F_j^2 H_ii = 0.

Differentiate this genuine source identity in x_k. The first
derivatives of F are independent of x_k, so the same contraction
of the Hessian of F vanishes. This is exactly the scalar
flat-level transport condition, with no additional hypothesis.
-/

public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
abbrev RankTwoAffineLevelCurvature.S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

open RankTwoAffineLevelCurvature (S)

/-- The principal minor involving an affine coordinate is the
negative of the tangent Hessian contraction. -/
theorem rankTwo_affine_principalMinor_curvature
    (L : S K) (k i j : Fin 4)
    (hkk : hessian L k k = 0)
    (hminor : ((hessian L).submatrix
      (![k,i,j] : Fin 3 → Fin 4) (![k,i,j] : Fin 3 → Fin 4)).det = 0) :
    let F := pderiv k L
    (pderiv i F)^2 * hessian L j j -
      2 * pderiv i F * pderiv j F * hessian L i j +
      (pderiv j F)^2 * hessian L i i = 0 := by
  classical
  dsimp only
  let H := hessian L
  have hs (a b : Fin 4) : H a b = H b a :=
    pderiv_comm_backport b a L
  have he : (!![0, H k i, H k j;
      H k i, H i i, H i j;
      H k j, H i j, H j j] : Matrix (Fin 3) (Fin 3) (S K)).det = 0 := by
    have hm : (H.submatrix (![k,i,j] : Fin 3 → Fin 4)
      (![k,i,j] : Fin 3 → Fin 4)) =
        !![0, H k i, H k j; H k i, H i i, H i j; H k j, H i j, H j j] := by
      apply Matrix.ext
      intro a b
      fin_cases a <;> fin_cases b
      · exact hkk
      · rfl
      · rfl
      · exact hs i k
      · rfl
      · rfl
      · exact hs j k
      · exact hs j i
      · rfl
    rw [← hm]
    exact hminor
  rw [Matrix.det_fin_three] at he
  change H k i ^ 2 * H j j - 2 * H k i * H k j * H i j +
    H k j ^ 2 * H i i = 0
  simp at he
  linear_combination -he

/-- The flat-level curvature equation comes from differentiation
of the actual rank-two Hessian minor in the affine coordinate. -/
theorem rankTwo_affine_gradient_flatLevel
    (L : S K) (k : Fin 4) (hkk : hessian L k k = 0)
    (hminor : ∀ i j : Fin 4, ((hessian L).submatrix
      (![k,i,j] : Fin 3 → Fin 4) (![k,i,j] : Fin 3 → Fin 4)).det = 0) :
    ∀ i j : Fin 4, let F := pderiv k L
      (pderiv i F)^2 * hessian F j j -
      2 * pderiv i F * pderiv j F * hessian F i j +
      (pderiv j F)^2 * hessian F i i = 0 := by
  classical
  intro i j
  dsimp only
  let F := pderiv k L
  have hF : pderiv k F = 0 := hkk
  have hz (a : Fin 4) : pderiv k (pderiv a F) = 0 := by
    rw [pderiv_comm_backport k a F, hF, map_zero]
  have ht (a b : Fin 4) : pderiv k (hessian L a b) = hessian F a b := by
    change pderiv k (pderiv b (pderiv a L)) = pderiv b (pderiv a (pderiv k L))
    rw [pderiv_comm_backport k b (pderiv a L), pderiv_comm_backport k a L]
  have hc := rankTwo_affine_principalMinor_curvature L k i j hkk (hminor i j)
  change (pderiv i F)^2 * hessian L j j -
    2 * pderiv i F * pderiv j F * hessian L i j +
    (pderiv j F)^2 * hessian L i i = 0 at hc
  have he := congrArg (pderiv k) hc
  rw [map_add, map_sub, map_zero] at he
  have htwo : pderiv k (2 : S K) = 0 :=
    (pderiv k : Derivation K (S K) (S K)).map_natCast 2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, hz, ht, htwo,
    mul_zero, add_zero, smul_zero] at he
  change (pderiv i F)^2 * hessian F j j -
    2 * pderiv i F * pderiv j F * hessian F i j +
    (pderiv j F)^2 * hessian F i i = 0
  exact he

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_affine_principalMinor_curvature
#print axioms HC4.Polynomial.rankTwo_affine_gradient_flatLevel
