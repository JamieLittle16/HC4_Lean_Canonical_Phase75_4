import HC4.Polynomial.RankThreeCubicPrincipalAdjugateDirection
import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Fixed rank-two tangent kernels and the genuine pole residue

A surviving principal cofactor makes a singular Hessian's
kernel a rank-one line over the residue domain. Two nonzero
vectors in that kernel must therefore be collinear, with
cross-multiplied coordinates:
  S_i * W_k = W_i * S_k.

The second fact below isolates an important *limitation*
of the existing source transport identities. For a fully
symmetric cubic tensor, if H_D(W) W = 0 then its quadratic
third-derivative contractions D_i(W,W) vanish automatically.
In particular once a source residue is aligned with a
fixed tangent-kernel direction, the time-zero quadratic
transport identities alone do not exclude that direction.
The obstruction must involve additional source information.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- Under a nonzero principal cofactor, any two singular
matrix-kernel vectors have proportional coordinates, without
passing from the residue domain to its field of fractions. -/
theorem principalCofactor_twoKernelVectors_crossMultiply
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (S W : Fin 3 → R)
    (hS : H *ᵥ S = 0)
    (hW : H *ᵥ W = 0)
    (hdet : H.det = 0)
    (k : Fin 3)
    (hk : H.adjugate k k ≠ 0) :
    ∀ i : Fin 3, S i * W k = W i * S k := by
  classical
  have hs := principalCofactor_kernelVector_adjugate_proportional
    H S hS hdet k hk
  have hw := principalCofactor_kernelVector_adjugate_proportional
    H W hW hdet k hk
  intro i
  apply (mul_left_cancel₀ hk)
  calc
    H.adjugate k k * (S i * W k) =
        (H.adjugate k k * S i) * W k := by ring
    _ = (H.adjugate i k * S k) * W k := by rw [hs i]
    _ = (H.adjugate i k * W k) * S k := by ring
    _ = (H.adjugate k k * W i) * S k := by rw [hw i]
    _ = H.adjugate k k * (W i * S k) := by ring

/-- A nonzero kernel vector has a nonzero selected pivot whenever
the corresponding principal cofactor survives. -/
theorem principalCofactor_kernelVector_pivot_of_nonzero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (W : Fin 3 → R)
    (hW : H *ᵥ W = 0)
    (hWnonzero : W ≠ 0)
    (k : Fin 3)
    (hk : H.adjugate k k ≠ 0) :
    W k ≠ 0 :=
  principalCofactor_kernelVector_pivot_ne_zero
    H W hW hWnonzero k hk

/-- The self-kernel identity for a symmetric cubic tensor makes
its quadratic third-derivative contraction identically zero.
This is precisely the shape of the source time-zero quadratic
residue identity, but with the kernel direction itself rather
than the actual normalized residue. -/
theorem cubicTensor_selfKernel_implies_quadraticContraction_zero
    {R : Type*} [CommRing R]
    (D : Fin 3 → Fin 3 → Fin 3 → R)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (W : Fin 3 → R)
    (hself : cubicTensorHessianAt D W *ᵥ W = 0) :
    ∀ i : Fin 3,
      (∑ l : Fin 3, ∑ m : Fin 3,
        D i l m * W l * W m) = 0 := by
  classical
  intro i
  have hi := congrFun hself i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply,
    cubicTensorHessianAt] at hi
  calc
    (∑ l : Fin 3, ∑ m : Fin 3, D i l m * W l * W m) =
        ∑ l : Fin 3, ∑ m : Fin 3,
          (W m * D m i l) * W l := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro m _
          rw [hswap₁ m i l, hswap₂ i m l]
          ring
    _ = ∑ l : Fin 3, (∑ m : Fin 3, W m * D m i l) * W l := by
      simp only [Finset.sum_mul]
    _ = 0 := hi

end
end HC4.Polynomial.RankThreeCubic
