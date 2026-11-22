import HC4.Polynomial.RankThreeCubicTensorKernelLeaf
import Mathlib.Tactic

/-!
# Repeated linear Hessian poles: tangent residue or triple factor

For a symmetric ternary cubic tensor D, let H(v) be its linear
Hessian pencil. Assume det H(v) factors as

  (ell · v)^2 * (gamma · v).

Suppose S is a nonzero kernel vector of H(x) on ell · x = 0,
and that the cubic third-derivative quadratic contractions
T(S,S,_) vanish. Tensor symmetry gives H(S)S=0; the Hessian
is singular at S and x+S. Comparing the two determinant
factorisations yields

  (ell · S)^2 * (gamma · x) = 0.

Hence the residue S is tangent to the pole hyperplane unless
the complementary factor vanishes at x. In the source quotient
K[y]/(p), gamma · x = 0 means p divides the complementary
linear cofactor, i.e. the *triple-pole* alternative.

No nonzero complement, selected Schur pivot, or prior
kernel-tangency assumption is inserted.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

def cubicPoleLinearFunctional
    {R : Type*} [CommRing R]
    (ell v : Fin 3 → R) : R :=
  ∑ i : Fin 3, ell i * v i

theorem cubicPoleLinearFunctional_add
    {R : Type*} [CommRing R]
    (ell u v : Fin 3 → R) :
    cubicPoleLinearFunctional ell (u + v) =
      cubicPoleLinearFunctional ell u +
        cubicPoleLinearFunctional ell v := by
  classical
  simp only [cubicPoleLinearFunctional, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

/-- Source-cubic rank-two residue geometry, expressed without a
coordinate chart: the kernel is tangent to a genuinely double
pole, or the residual linear determinant factor also vanishes
on the given point of the pole plane. -/
theorem cubicTensor_repeatedPole_kernel_tangent_or_triple
    {R : Type*} [CommRing R] [IsDomain R]
    (D : Fin 3 → Fin 3 → Fin 3 → R)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (ell gamma : Fin 3 → R)
    (hfactor : ∀ v : Fin 3 → R,
      (cubicTensorHessianAt D v).det =
        (cubicPoleLinearFunctional ell v) *
        (cubicPoleLinearFunctional ell v) *
        (cubicPoleLinearFunctional gamma v))
    (x S : Fin 3 → R)
    (k : Fin 3)
    (hSk : S k ≠ 0)
    (hpX : cubicPoleLinearFunctional ell x = 0)
    (hker : (cubicTensorHessianAt D x) *ᵥ S = 0)
    (hquad : ∀ i : Fin 3,
      (∑ j : Fin 3, ∑ m : Fin 3,
        D i j m * S j * S m) = 0) :
    cubicPoleLinearFunctional ell S = 0 ∨
      cubicPoleLinearFunctional gamma x = 0 := by
  let H : (Fin 3 → R) → Matrix (Fin 3) (Fin 3) R :=
    cubicTensorHessianAt D
  let p : (Fin 3 → R) → R := cubicPoleLinearFunctional ell
  let c : (Fin 3 → R) → R := cubicPoleLinearFunctional gamma
  have hHadd (u v : Fin 3 → R) :
      H (u + v) = H u + H v :=
    cubicTensorHessianAt_add D u v
  have hpadd (u v : Fin 3 → R) :
      p (u + v) = p u + p v :=
    cubicPoleLinearFunctional_add ell u v
  have hcadd (u v : Fin 3 → R) :
      c (u + v) = c u + c v :=
    cubicPoleLinearFunctional_add gamma u v
  have hself : (H S) *ᵥ S = 0 :=
    cubicTensor_quadraticResidue_implies_selfKernel
      D hswap₁ hswap₂ S hquad
  exact additivePencil_repeatedPole_kernel_tangent_or_cofactor_zero
    H p c hHadd hpadd hcadd hfactor x S k hSk hpX hker hself

end
end HC4.Polynomial.RankThreeCubic
