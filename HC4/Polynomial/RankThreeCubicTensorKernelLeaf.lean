import HC4.Polynomial.RankThreeCubicRepeatedPoleKernelTangency
import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Symmetric cubic kernel leaves

The cubic third-derivative tensor D determines a linear Hessian
H(v). Symmetry in its three indices has a concrete geometric
consequence: if a vector S annihilates the quadratic form

   sum_{j,k} D(i,j,k) S(j) S(k)

for every i, then H(S)*S=0. If S is already a kernel vector of
H(x), linearity implies it remains a kernel vector at x+S.

This is exactly the bridge from the source-derived quadratic
characteristic residue equations to the singular-Hessian
trajectory needed for the repeated-pole tangency dichotomy.
It is proved without dividing by a pivot.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- The Hessian of a cubic tensor is linear in its basepoint. -/
theorem cubicTensorHessianAt_add
    {R : Type*} [CommRing R]
    (D : Fin 3 → Fin 3 → Fin 3 → R)
    (u v : Fin 3 → R) :
    cubicTensorHessianAt D (u + v) =
      cubicTensorHessianAt D u + cubicTensorHessianAt D v := by
  classical
  ext i j
  simp only [cubicTensorHessianAt, Matrix.add_apply, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]

/-- The symmetric tensor's quadratic residue identities imply that
the same vector lies in the kernel of the Hessian evaluated at
the vector itself. -/
theorem cubicTensor_quadraticResidue_implies_selfKernel
    {R : Type*} [CommRing R]
    (D : Fin 3 → Fin 3 → Fin 3 → R)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (S : Fin 3 → R)
    (hquad : ∀ i : Fin 3,
      (∑ j : Fin 3, ∑ k : Fin 3,
        D i j k * S j * S k) = 0) :
    (cubicTensorHessianAt D S) *ᵥ S = 0 := by
  classical
  funext i
  change (∑ j : Fin 3,
      (∑ k : Fin 3, S k * D k i j) * S j) = 0
  calc
    (∑ j : Fin 3,
      (∑ k : Fin 3, S k * D k i j) * S j) =
        ∑ j : Fin 3, ∑ k : Fin 3,
          D i j k * S j * S k := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [hswap₁ k i j, hswap₂ i k j]
            ring
    _ = 0 := hquad i

/-- A source kernel vector with vanishing third-derivative quadratic
contractions stays in the kernel along its own line direction. -/
theorem cubicTensor_quadraticResidue_kernelAt_translate
    {R : Type*} [CommRing R]
    (D : Fin 3 → Fin 3 → Fin 3 → R)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (x S : Fin 3 → R)
    (hker : (cubicTensorHessianAt D x) *ᵥ S = 0)
    (hquad : ∀ i : Fin 3,
      (∑ j : Fin 3, ∑ k : Fin 3,
        D i j k * S j * S k) = 0) :
    (cubicTensorHessianAt D (x + S)) *ᵥ S = 0 := by
  rw [cubicTensorHessianAt_add]
  rw [Matrix.add_mulVec, hker,
    cubicTensor_quadraticResidue_implies_selfKernel D hswap₁ hswap₂ S hquad,
    zero_add]

end
end HC4.Polynomial.RankThreeCubic
