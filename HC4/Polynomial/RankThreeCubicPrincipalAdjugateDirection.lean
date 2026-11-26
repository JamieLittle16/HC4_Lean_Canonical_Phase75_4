module

public import HC4.Polynomial.RankThreeCubicPrincipalKernelPivot
public import Mathlib.Tactic

/-!
# Adjugate-column alignment of a singular rank-two kernel

Over an integral domain, a nonzero principal cofactor of a
singular 3x3 matrix determines the entire kernel direction.

If H*S=0, det(H)=0 and adj(H)_{k,k} != 0, then
  adj(H)_{k,k} * S_i = adj(H)_{i,k} * S_k
for every i.

The proof avoids dividing by a cofactor or passing to the
fraction field. It subtracts a scalar multiple of the kth
adjugate column from the kernel vector, then uses the
previously verified principal-pivot injectivity lemma to
show that this new vector vanishes.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A nonzero principal cofactor determines the direction of
every kernel vector of a singular 3x3 matrix, over any domain.
No symmetry or invertibility of the ambient matrix is assumed. -/
theorem principalCofactor_kernelVector_adjugate_proportional
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (S : Fin 3 → R)
    (hker : H *ᵥ S = 0)
    (hdet : H.det = 0)
    (k : Fin 3)
    (hk : H.adjugate k k ≠ 0) :
    ∀ i : Fin 3,
      H.adjugate k k * S i = H.adjugate i k * S k := by
  classical
  have hcol (i : Fin 3) :
      (∑ j : Fin 3, H i j * H.adjugate j k) = 0 := by
    have hmul :=
      congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i k)
        (Matrix.mul_adjugate H)
    simpa [Matrix.mul_apply, hdet] using hmul
  have hrow (i : Fin 3) :
      (∑ j : Fin 3, H i j * S j) = 0 := by
    have hi := congrFun hker i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hi
  let W : Fin 3 → R :=
    fun i => H.adjugate k k * S i - H.adjugate i k * S k
  have hWker : H *ᵥ W = 0 := by
    funext i
    change (∑ j : Fin 3,
      H i j * (H.adjugate k k * S j - H.adjugate j k * S k)) = 0
    calc
      _ = ∑ j : Fin 3,
          (H.adjugate k k * (H i j * S j) -
            S k * (H i j * H.adjugate j k)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = H.adjugate k k * (∑ j : Fin 3, H i j * S j) -
          S k * (∑ j : Fin 3, H i j * H.adjugate j k) := by
            simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by rw [hrow i, hcol i]; ring
  have hWk : W k = 0 := by
    dsimp [W]
    ring
  have hWzero : W = 0 := by
    by_contra hWne
    exact (principalCofactor_kernelVector_pivot_ne_zero
      H W hWker hWne k hk) hWk
  intro i
  have hi := congrFun hWzero i
  change H.adjugate k k * S i - H.adjugate i k * S k = 0 at hi
  exact sub_eq_zero.mp hi

end
end HC4.Polynomial.RankThreeCubic
