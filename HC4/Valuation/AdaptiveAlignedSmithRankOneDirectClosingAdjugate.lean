import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingGapJet
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Adjugate algebra of the direct-closing dual jet

The green gap-jet identity packages the equality branch as a matrix `D` over
`DualNumber K` with

    det D = eps.

This file extracts the finite-dimensional content needed for kernel freshness
without introducing matrix rank.  Write

    A = fst D,   B = snd D,   C = adjugate A.

From `D * adjugate D = eps • I`, constant/nilpotent projection gives the
first adjugate identity

    A * E + B * C = I,

where `E = snd (adjugate D)`.  Since `det A = 0`, this already forces
`C != 0`.  Multiplying on the left by `C` and using `C * A = 0` yields the
stronger sandwich identity

    C * B * C = C.

For the honest direct-closing Hessian this says that the special-fibre
adjugate is nonzero and that the first actual Hessian layer acts nontrivially
on its image.  The next file can turn this, by symmetry and polarization,
into a kernel vector `v` with `v^T H_j v != 0`.
-/

namespace HC4.Valuation

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Constant part of a dual-number matrix. -/
noncomputable def dualMatrixFst
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K)) :
    Matrix (Fin 4) (Fin 4) K :=
  (TrivSqZeroExt.fstHom K K K).toRingHom.mapMatrix D

/-- Nilpotent part of a dual-number matrix. -/
noncomputable def dualMatrixSnd
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K)) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i k => TrivSqZeroExt.snd (D i k)

@[simp]
theorem dualMatrixFst_apply
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (i k : Fin 4) :
    dualMatrixFst D i k = TrivSqZeroExt.fst (D i k) := by
  rfl

@[simp]
theorem dualMatrixSnd_apply
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (i k : Fin 4) :
    dualMatrixSnd D i k = TrivSqZeroExt.snd (D i k) := by
  rfl

/-- Constant projection commutes with determinant. -/
theorem dualMatrixFst_det
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K)) :
    (dualMatrixFst D).det = TrivSqZeroExt.fst D.det := by
  have h :=
    (TrivSqZeroExt.fstHom K K K).toRingHom.map_det D
  exact h.symm

/-- Constant projection commutes with adjugation. -/
theorem dualMatrixFst_adjugate
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K)) :
    dualMatrixFst D.adjugate = (dualMatrixFst D).adjugate := by
  exact (TrivSqZeroExt.fstHom K K K).toRingHom.map_adjugate D

/-- The nilpotent part of a matrix product obeys the Leibniz rule. -/
theorem dualMatrixSnd_mul
    (D E : Matrix (Fin 4) (Fin 4) (DualNumber K)) :
    dualMatrixSnd (D * E) =
      dualMatrixFst D * dualMatrixSnd E +
        dualMatrixSnd D * dualMatrixFst E := by
  ext i k
  simp only [dualMatrixSnd, dualMatrixFst, RingHom.mapMatrix_apply,
    Matrix.mul_apply, Matrix.add_apply]
  change
    (TrivSqZeroExt.sndHom K K)
        (∑ x, D i x * E x k) =
      (∑ x, TrivSqZeroExt.fst (D i x) * TrivSqZeroExt.snd (E x k)) +
        ∑ x, TrivSqZeroExt.snd (D i x) * TrivSqZeroExt.fst (E x k)
  rw [map_sum]
  change
    (∑ x, TrivSqZeroExt.snd (D i x * E x k)) =
      (∑ x, TrivSqZeroExt.fst (D i x) * TrivSqZeroExt.snd (E x k)) +
        ∑ x, TrivSqZeroExt.snd (D i x) * TrivSqZeroExt.fst (E x k)
  simp_rw [DualNumber.snd_mul]
  exact Finset.sum_add_distrib

/-- The constant matrix is singular whenever the dual determinant is `eps`. -/
theorem dualMatrixFst_det_eq_zero_of_det_eq_eps
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (hdet : D.det = DualNumber.eps) :
    (dualMatrixFst D).det = 0 := by
  rw [dualMatrixFst_det, hdet]
  simp

/-- Taking the nilpotent part of `D * adjugate D = eps I` gives the exact
first adjugate equation `A E + B adj(A) = I`. -/
theorem dualMatrix_firstAdjugateIdentity_of_det_eq_eps
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (hdet : D.det = DualNumber.eps) :
    dualMatrixFst D * dualMatrixSnd D.adjugate +
        dualMatrixSnd D * (dualMatrixFst D).adjugate =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  have h := congrArg (dualMatrixSnd (K := K)) (Matrix.mul_adjugate D)
  rw [dualMatrixSnd_mul, dualMatrixFst_adjugate, hdet] at h
  ext i k
  have hikEntry := congrFun (congrFun h i) k
  by_cases hik : i = k
  · subst k
    simpa [dualMatrixSnd] using hikEntry
  · simpa [dualMatrixSnd, Matrix.one_apply, hik] using hikEntry

/-- A dual matrix with determinant exactly `eps` must have nonzero adjugate
on its constant part.  This avoids a separate rank-three argument. -/
theorem dualMatrixFst_adjugate_ne_zero_of_det_eq_eps
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (hdet : D.det = DualNumber.eps) :
    (dualMatrixFst D).adjugate ≠ 0 := by
  let A := dualMatrixFst D
  let B := dualMatrixSnd D
  let E := dualMatrixSnd D.adjugate
  have hsplit : A * E + B * A.adjugate =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [A, B, E] using
      dualMatrix_firstAdjugateIdentity_of_det_eq_eps D hdet
  have hdetA : A.det = 0 := by
    simpa [A] using dualMatrixFst_det_eq_zero_of_det_eq_eps D hdet
  intro hAdj
  have hAdjA : A.adjugate = 0 := by
    simpa [A] using hAdj
  have hAE : A * E = (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [hAdjA, Matrix.mul_zero, add_zero] at hsplit
    exact hsplit
  have hdetAE : A.det * E.det = (1 : K) := by
    simpa [Matrix.det_mul] using congrArg Matrix.det hAE
  rw [hdetA, zero_mul] at hdetAE
  exact zero_ne_one hdetAE

/-- The strongest rank-free consequence of the direct dual determinant:
`adj(A) * B * adj(A) = adj(A)`. -/
theorem dualMatrixFst_adjugate_sandwich_of_det_eq_eps
    (D : Matrix (Fin 4) (Fin 4) (DualNumber K))
    (hdet : D.det = DualNumber.eps) :
    (dualMatrixFst D).adjugate * dualMatrixSnd D *
        (dualMatrixFst D).adjugate =
      (dualMatrixFst D).adjugate := by
  let A := dualMatrixFst D
  let B := dualMatrixSnd D
  let C := A.adjugate
  let E := dualMatrixSnd D.adjugate
  have hsplit : A * E + B * C =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
    simpa [A, B, C, E] using
      dualMatrix_firstAdjugateIdentity_of_det_eq_eps D hdet
  have hdetA : A.det = 0 := by
    simpa [A] using dualMatrixFst_det_eq_zero_of_det_eq_eps D hdet
  have hCA : C * A = 0 := by
    have h := Matrix.adjugate_mul A
    rw [hdetA] at h
    simpa [C] using h
  have hCAE : C * (A * E) = 0 := by
    rw [← Matrix.mul_assoc, hCA, zero_mul]
  have hBC : C * (B * C) = C := by
    calc
      C * (B * C) = C * (A * E + B * C) := by
        rw [Matrix.mul_add, hCAE, zero_add]
      _ = C * 1 := by rw [hsplit]
      _ = C := Matrix.mul_one C
  rw [← Matrix.mul_assoc] at hBC
  simpa [A, B, C] using hBC

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable [CharZero K]
variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Constant part of the direct-closing dual Hessian is the honest
special-fibre source-origin Hessian. -/
theorem directClosingOriginDualHessian_fst
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    dualMatrixFst C.directClosingOriginDualHessian =
      sourceOriginHessianLayer C.family 0 := by
  ext i k
  rw [dualMatrixFst_apply, C.directClosingOriginDualHessian_apply]
  simp

/-- Nilpotent part of the direct-closing dual Hessian is the honest first
actual source-origin Hessian layer. -/
theorem directClosingOriginDualHessian_snd
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    dualMatrixSnd C.directClosingOriginDualHessian =
      sourceOriginHessianLayer C.family C.firstActualLayerOrder := by
  ext i k
  rw [dualMatrixSnd_apply, C.directClosingOriginDualHessian_apply]
  simp

/-- At `j = Delta`, the special-fibre source-origin Hessian has nonzero
adjugate.  In particular a genuine kernel direction is already visible
without invoking a rank API. -/
theorem directClosing_specialHessian_adjugate_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (sourceOriginHessianLayer C.family 0).adjugate ≠ 0 := by
  have h := dualMatrixFst_adjugate_ne_zero_of_det_eq_eps
    C.directClosingOriginDualHessian
    (C.directClosingOriginDualHessian_det heq)
  rw [C.directClosingOriginDualHessian_fst] at h
  exact h

/-- At `j = Delta`, if `A = H_0` and `B = H_j`, then
`adj(A) B adj(A) = adj(A)`.  This is the exact algebraic input for the
kernel-freshness/polarization step. -/
theorem directClosing_specialHessian_adjugate_sandwich
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (sourceOriginHessianLayer C.family 0).adjugate *
        sourceOriginHessianLayer C.family C.firstActualLayerOrder *
        (sourceOriginHessianLayer C.family 0).adjugate =
      (sourceOriginHessianLayer C.family 0).adjugate := by
  have h := dualMatrixFst_adjugate_sandwich_of_det_eq_eps
    C.directClosingOriginDualHessian
    (C.directClosingOriginDualHessian_det heq)
  rw [C.directClosingOriginDualHessian_fst,
      C.directClosingOriginDualHessian_snd] at h
  exact h

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
