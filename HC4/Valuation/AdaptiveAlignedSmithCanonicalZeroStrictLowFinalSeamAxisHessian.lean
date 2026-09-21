import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamExactHessianOrder
import HC4.Newton.TerminalCenteredWeights
import Mathlib.Tactic

/-!
# G4: determinant-one axis Hessian at the final seam

G3 identifies one strict-low Hessian entry together with its exact
longitudinal order.  This file records the matrix-level fact which that order
must satisfy.

Restrict the honest right-recentered Hessian to the distinguished
longitudinal axis.  Because the full Hessian determinant is exactly one, this
axis Hessian also has determinant one.  Evaluating at the recentered endpoint
therefore gives an invertible symmetric `4 x 4` matrix.

The first useful consequence is elementary but important: if the longitudinal
diagonal entry has positive exact order, then it vanishes at the endpoint, so
invertibility forces a nonzero off-diagonal entry in row zero.  The
corresponding principal `2 x 2` minor is then exactly a nonzero negative
square.

No progress theorem, repair transition, support homogeneity, cocharacter, or
JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Hessian of the right-recentered determinant-one fibre restricted to the
marked longitudinal axis. -/
noncomputable def finalSeamAxisHessian
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber)

/-- The axis restriction preserves the determinant-one identity. -/
theorem finalSeamAxisHessian_det_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.finalSeamAxisHessian.det = 1 := by
  let phi := longitudinalAxisRestrictionRingHom (K := K)
  let H := HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
  have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
  have hdet := T.rightRecenteredSpecialFiber_hessianDeterminant_eq_one
  calc
    T.finalSeamAxisHessian.det = (phi.mapMatrix H).det := by rfl
    _ = phi H.det := hmap.symm
    _ = phi (HC4.Polynomial.hessianDeterminant
        T.rightRecenteredSpecialFiber) := by rfl
    _ = phi 1 := by rw [hdet]
    _ = 1 := map_one phi

/-- Constant matrix obtained from the axis Hessian at the recentered right
endpoint `x₀ = 0`. -/
noncomputable def finalSeamOriginHessian
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Matrix (Fin 4) (Fin 4) K :=
  (Polynomial.evalRingHom (0 : K)).mapMatrix T.finalSeamAxisHessian

/-- The endpoint Hessian is invertible, with determinant exactly one. -/
theorem finalSeamOriginHessian_det_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.finalSeamOriginHessian.det = 1 := by
  let phi : Polynomial K →+* K := Polynomial.evalRingHom (0 : K)
  let H := T.finalSeamAxisHessian
  have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
  calc
    T.finalSeamOriginHessian.det = (phi.mapMatrix H).det := by rfl
    _ = phi H.det := hmap.symm
    _ = phi 1 := by rw [T.finalSeamAxisHessian_det_one]
    _ = 1 := map_one phi

/-- The origin matrix entry is the constant coefficient of the corresponding
axis-restricted Hessian entry. -/
theorem finalSeamOriginHessian_eq_coeff_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4) :
    T.finalSeamOriginHessian i j =
      (longitudinalAxisRestriction
        (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber i j)).coeff 0 := by
  change
    Polynomial.eval 0
        (longitudinalAxisRestriction
          (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber i j)) =
      (longitudinalAxisRestriction
        (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber i j)).coeff 0
  simp

/-- Mixed partial symmetry survives both axis restriction and endpoint
evaluation. -/
theorem finalSeamOriginHessian_symmetric
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4) :
    T.finalSeamOriginHessian i j = T.finalSeamOriginHessian j i := by
  rw [T.finalSeamOriginHessian_eq_coeff_zero,
    T.finalSeamOriginHessian_eq_coeff_zero]
  congr 1
  rw [HC4.Polynomial.hessian_apply, HC4.Polynomial.hessian_apply,
    pderiv_comm_commRing]

/-- Positive exact longitudinal order forces the corresponding Hessian entry
to vanish at the recentered endpoint. -/
theorem finalSeamOriginHessian_entry_eq_zero_of_exactOrder_pos
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4) (m : ℕ)
    (horder :
      HasExactPolynomialInitialOrder
        (longitudinalAxisRestriction
          (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber i j)) m)
    (hm : 0 < m) :
    T.finalSeamOriginHessian i j = 0 := by
  rw [T.finalSeamOriginHessian_eq_coeff_zero]
  exact horder.1 0 hm

/-- If the longitudinal diagonal vanishes at the endpoint, determinant one
forces a nonzero principal binary Hessian minor containing coordinate zero.

The nonzero minor is literally `-H₀ⱼ²`, because Hessian symmetry identifies
the two mixed entries. -/
theorem finalSeamOrigin_principalMinor_ne_zero_of_zero_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (h00 : T.finalSeamOriginHessian 0 0 = 0) :
    ∃ j : Fin 4,
      j ≠ 0 ∧
      T.finalSeamOriginHessian 0 0 *
            T.finalSeamOriginHessian j j -
          T.finalSeamOriginHessian 0 j *
            T.finalSeamOriginHessian j 0 ≠ 0 := by
  let H := T.finalSeamOriginHessian
  have hdet : H.det ≠ 0 := by
    rw [T.finalSeamOriginHessian_det_one]
    exact one_ne_zero
  rcases matrix4_det_ne_zero_row_exists_entry H hdet (0 : Fin 4) with
    ⟨j, hj⟩
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact hj h00
  have hsym : H j 0 = H 0 j := by
    exact T.finalSeamOriginHessian_symmetric j 0
  refine ⟨j, hj0, ?_⟩
  change H 0 0 * H j j - H 0 j * H j 0 ≠ 0
  rw [show H 0 0 = 0 by exact h00, hsym]
  simp only [zero_mul, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero hj hj)

/-- Direct consumer for any positive exact order of the longitudinal diagonal
entry. -/
theorem finalSeamOrigin_principalMinor_ne_zero_of_diagonalExactOrder_pos
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (m : ℕ)
    (horder :
      HasExactPolynomialInitialOrder
        (longitudinalAxisRestriction
          (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber 0 0)) m)
    (hm : 0 < m) :
    ∃ j : Fin 4,
      j ≠ 0 ∧
      T.finalSeamOriginHessian 0 0 *
            T.finalSeamOriginHessian j j -
          T.finalSeamOriginHessian 0 j *
            T.finalSeamOriginHessian j 0 ≠ 0 := by
  exact T.finalSeamOrigin_principalMinor_ne_zero_of_zero_zero
    (T.finalSeamOriginHessian_entry_eq_zero_of_exactOrder_pos
      0 0 m horder hm)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
