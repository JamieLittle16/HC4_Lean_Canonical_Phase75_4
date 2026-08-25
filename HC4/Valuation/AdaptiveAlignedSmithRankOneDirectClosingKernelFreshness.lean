import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingAdjugate
import Mathlib.Tactic

/-!
# Kernel freshness at direct rank-one closing

The green adjugate bridge gives, in the equality branch `j = Delta`,

    Adj(H₀) * Hⱼ * Adj(H₀) = Adj(H₀)

with `Adj(H₀) != 0` and `det H₀ = 0`.

This file turns that matrix identity into the exact source direction needed
for freshness.  The argument is rank-free.  Put `C = Adj(H₀)`.  Since
`H₀ C = 0`, every column of `C` is in the kernel of `H₀`.  Since `H₀` is
symmetric, `C` is symmetric.  The sandwich identity says that the `Hⱼ`
bilinear pairing of the `i`th and `k`th columns is exactly `C i k`.

Choose a nonzero entry `C i k`.  If either corresponding diagonal entry is
nonzero, that column already has nonzero `Hⱼ`-quadratic value.  Otherwise
the sum of the two columns has quadratic value `2 * C i k`, nonzero in
characteristic zero.

Thus direct closing canonically produces an honest nonzero vector `v` with

    H₀ v = 0,
    vᵀ Hⱼ v != 0.

This is the finite-dimensional kernel-freshness certificate needed to make a
fresh square source contact.
-/

namespace HC4.Valuation

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Rank-free linear algebra behind kernel freshness.  If a symmetric
singular matrix `A` has nonzero adjugate `C` and `C B C = C`, then some
nonzero vector in `ker A` has nonzero `B`-quadratic value. -/
theorem exists_kernel_quadratic_ne_zero_of_adjugate_sandwich
    (A B : Matrix (Fin 4) (Fin 4) K)
    (hA : ∀ i j, A i j = A j i)
    (hdet : A.det = 0)
    (hAdj : A.adjugate ≠ 0)
    (hsand : A.adjugate * B * A.adjugate = A.adjugate) :
    ∃ v : Fin 4 → K,
      v ≠ 0 ∧
      A.mulVec v = 0 ∧
      dotProduct v (B.mulVec v) ≠ 0 := by
  let C := A.adjugate
  have hCne : C ≠ 0 := by simpa [C] using hAdj
  have hAT : A.transpose = A := by
    ext i j
    exact hA j i
  have hCsymm : ∀ i j, C i j = C j i := by
    have hCT : C.transpose = C := by
      dsimp [C]
      calc
        A.adjugate.transpose = A.transpose.adjugate := Matrix.adjugate_transpose A
        _ = A.adjugate := congrArg Matrix.adjugate hAT
    intro i j
    have h := congrFun (congrFun hCT i) j
    exact h.symm
  have hAC : A * C = 0 := by
    have h := Matrix.mul_adjugate A
    rw [hdet] at h
    simpa [C] using h
  have hCBC : C * B * C = C := by
    simpa [C] using hsand
  have hCentry : ∃ i k : Fin 4, C i k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hCne
    ext i k
    exact h i k
  rcases hCentry with ⟨i, k, hik⟩

  have hCtranspose (r : Fin 4) : C.transpose r = C r := by
    funext x
    exact hCsymm x r

  have hkernel (r : Fin 4) : A.mulVec (C r) = 0 := by
    have hrowcol : C r = C.col r := by
      funext x
      have hx := congrFun (hCtranspose r) x
      simpa using hx.symm
    rw [hrowcol]
    funext x
    have hx := congrFun (congrFun hAC x) r
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hx

  have hpair (r s : Fin 4) :
      dotProduct (C r) (B.mulVec (C s)) = C r s := by
    have h := congrFun (congrFun hCBC r) s
    rw [Matrix.mul_mul_apply] at h
    rw [hCtranspose s] at h
    exact h

  by_cases hii : C i i = 0
  · by_cases hkk : C k k = 0
    · let v : Fin 4 → K := C i + C k
      have hvker : A.mulVec v = 0 := by
        rw [show v = C i + C k by rfl, Matrix.mulVec_add, hkernel i, hkernel k]
        simp
      have hki : C k i = C i k := by
        exact hCsymm k i
      have hq : dotProduct v (B.mulVec v) = 2 * C i k := by
        change dotProduct (C i + C k) (B.mulVec (C i + C k)) = 2 * C i k
        rw [Matrix.mulVec_add]
        simp only [add_dotProduct, dotProduct_add]
        rw [hpair i i, hpair i k, hpair k i, hpair k k, hii, hkk, hki]
        ring
      have hqne : dotProduct v (B.mulVec v) ≠ 0 := by
        rw [hq]
        exact mul_ne_zero (by norm_num) hik
      have hvne : v ≠ 0 := by
        intro hv
        apply hqne
        rw [hv]
        simp
      exact ⟨v, hvne, hvker, hqne⟩
    · let v : Fin 4 → K := C k
      have hvker : A.mulVec v = 0 := by
        simpa [v] using hkernel k
      have hq : dotProduct v (B.mulVec v) = C k k := by
        simpa [v] using hpair k k
      have hqne : dotProduct v (B.mulVec v) ≠ 0 := by
        rw [hq]
        exact hkk
      have hvne : v ≠ 0 := by
        intro hv
        apply hqne
        rw [hv]
        simp
      exact ⟨v, hvne, hvker, hqne⟩
  · let v : Fin 4 → K := C i
    have hvker : A.mulVec v = 0 := by
      simpa [v] using hkernel i
    have hq : dotProduct v (B.mulVec v) = C i i := by
      simpa [v] using hpair i i
    have hqne : dotProduct v (B.mulVec v) ≠ 0 := by
      rw [hq]
      exact hii
    have hvne : v ≠ 0 := by
      intro hv
      apply hqne
      rw [hv]
      simp
    exact ⟨v, hvne, hvker, hqne⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Every honest source-origin Hessian parameter layer is symmetric. -/
theorem sourceOriginHessianLayer_isSymm
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (n : ℕ) :
    ∀ i k,
      sourceOriginHessianLayer C.family n i k =
        sourceOriginHessianLayer C.family n k i := by
  intro i k
  rw [sourceOriginHessianLayer_apply, sourceOriginHessianLayer_apply]
  exact quadraticFamilyHessianMatrix_coeff_symmetric C.family n i k

/-- The direct-closing equality branch already contains a genuinely fresh
kernel quadratic direction at the honest source origin. -/
theorem directClosing_exists_kernelFreshDirection
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    ∃ v : Fin 4 → K,
      v ≠ 0 ∧
      (sourceOriginHessianLayer C.family 0).mulVec v = 0 ∧
      dotProduct v
        ((sourceOriginHessianLayer C.family C.firstActualLayerOrder).mulVec v) ≠ 0 := by
  exact exists_kernel_quadratic_ne_zero_of_adjugate_sandwich
    (sourceOriginHessianLayer C.family 0)
    (sourceOriginHessianLayer C.family C.firstActualLayerOrder)
    (C.sourceOriginHessianLayer_isSymm 0)
    C.sourceOriginSpecialHessian_det_eq_zero
    (C.directClosing_specialHessian_adjugate_ne_zero heq)
    (C.directClosing_specialHessian_adjugate_sandwich heq)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
