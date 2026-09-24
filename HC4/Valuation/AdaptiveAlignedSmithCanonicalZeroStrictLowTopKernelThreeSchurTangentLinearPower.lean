import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentCross
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurHomogeneousLinearPower
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import Mathlib.Tactic

/-!
# Linear-power rigidity of the tangent three-Schur opening

The source-level tangent cross equation from the previous stage is

    H_D(p,p) G_E(r,k) - H_D(p,r) G_E(p,k) = 0,

where H_D = a L^D is the maximal linear-power top face, p is the selected
nonzero scalar pivot, and k is the stored kernel coordinate.

The Hessian of a L^D is a nonzero common scalar-polynomial factor times
c c^T, where c is the coefficient vector of L.  Cancelling that factor gives

    c_p G_E(r,k) = c_r G_E(p,k).

Put A = partial_k G_E.  Mixed-partial commutation turns the preceding
identity into

    partial_r A = (c_r / c_p) partial_p A

for every source coordinate r.  The retained nonzero mixed Hessian entry
forces partial_p A != 0.  Since G_E is homogeneous of degree E >= 3,
A is homogeneous of positive degree E-1.

The already-green homogeneous constant-gradient-ratio theorem therefore gives

    A = beta * L_tilde^(E-1),

where L_tilde is the top linear form normalized so that its pivot coefficient
is one.

Thus the tangent branch is an explicit staircase seed: the part of the first
lower source layer which is linear in the kernel coordinate is a power of the
same top direction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Original source coordinate corresponding to the scalar Schur pivot. -/
def TopKernelThreeSchurClockData.pivotCoordinate
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Fin 4 :=
  kernelLastPerm kernelCoordinate S.pivotSlot

/-- The selected Schur pivot has a nonzero coefficient in the top linear
form. -/
theorem TopKernelThreeSchurClockData.pivotRatio_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    P.ratio S.pivotCoordinate ≠ 0 := by
  intro hp
  have hdiag := S.topFace_pivotDiagonal_ne_zero
  let n := T.topFace.degree - 2
  have hm3 : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  have hD : n + 2 = T.topFace.degree := by
    dsimp [n]
    omega
  have hformula :=
    hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin
      P.coefficient P.ratio n S.pivotCoordinate S.pivotCoordinate
  change HC4.Polynomial.hessian T.topFace.face
      S.pivotCoordinate S.pivotCoordinate ≠ 0 at hdiag
  rw [P.eq_power, ← hD, hformula, hp] at hdiag
  simp at hdiag

/-- Top-direction ratios normalized by the selected scalar pivot. -/
def TopKernelThreeSchurClockData.normalizedTopRatio
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Fin 4 → K :=
  fun i => P.ratio i / P.ratio S.pivotCoordinate

@[simp] theorem TopKernelThreeSchurClockData.normalizedTopRatio_pivot
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    S.normalizedTopRatio S.pivotCoordinate = 1 := by
  simp [TopKernelThreeSchurClockData.normalizedTopRatio,
    S.pivotRatio_ne_zero]

@[simp] theorem TopKernelThreeSchurClockData.normalizedTopRatio_kernel
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    S.normalizedTopRatio kernelCoordinate = 0 := by
  simp [TopKernelThreeSchurClockData.normalizedTopRatio,
    P.kernel_ratio_zero]

private theorem linearPower_cross_cancel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (S : P.TopKernelThreeSchurClockData)
    (G : MvPolynomial (Fin 4) K)
    (r : Fin 4)
    (hcross :
      HC4.Polynomial.hessian T.topFace.face
            S.pivotCoordinate S.pivotCoordinate *
          HC4.Polynomial.hessian G r kernelCoordinate -
        HC4.Polynomial.hessian T.topFace.face
            S.pivotCoordinate r *
          HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate = 0) :
    HC4.Polynomial.hessian G r kernelCoordinate =
      MvPolynomial.C (S.normalizedTopRatio r) *
        HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate := by
  let n := T.topFace.degree - 2
  let L := gradientRatioLinearForm P.ratio
  let cp := P.ratio S.pivotCoordinate
  let cr := P.ratio r
  let s : K :=
    P.coefficient *
      (((n + 2 : ℕ) : K)) *
      (((n + 1 : ℕ) : K))

  have hm3 : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  have hD : n + 2 = T.topFace.degree := by
    dsimp [n]
    omega
  have hpp0 :=
    hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin
      P.coefficient P.ratio n S.pivotCoordinate S.pivotCoordinate
  have hpr0 :=
    hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin
      P.coefficient P.ratio n S.pivotCoordinate r
  have hpp :
      HC4.Polynomial.hessian T.topFace.face
          S.pivotCoordinate S.pivotCoordinate =
        MvPolynomial.C (s * cp * cp) * L ^ n := by
    rw [P.eq_power, ← hD]
    simpa [s, cp, L] using hpp0
  have hpr :
      HC4.Polynomial.hessian T.topFace.face
          S.pivotCoordinate r =
        MvPolynomial.C (s * cp * cr) * L ^ n := by
    rw [P.eq_power, ← hD]
    simpa [s, cp, cr, L] using hpr0

  have hs : s ≠ 0 := by
    dsimp [s]
    have hn2 : (((n + 2 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (show n + 2 ≠ 0 by
        rw [hD]
        omega)
    have hn1 : (((n + 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (show n + 1 ≠ 0 by omega)
    exact mul_ne_zero
      (mul_ne_zero (P.coefficient_ne_zero) hn2) hn1
  have hcp : cp ≠ 0 := by
    simpa [cp] using S.pivotRatio_ne_zero
  have hL : L ≠ 0 := by
    simpa [L] using P.linearForm_ne_zero
  have hfactor :
      (MvPolynomial.C (s * cp) * L ^ n :
        MvPolynomial (Fin 4) K) ≠ 0 := by
    exact mul_ne_zero
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero hs hcp))
      (pow_ne_zero _ hL)

  rw [hpp, hpr] at hcross
  have hCcp :
      MvPolynomial.C (s * cp * cp) =
        MvPolynomial.C (s * cp) * MvPolynomial.C cp := by
    rw [← MvPolynomial.C_mul]
  have hCcr :
      MvPolynomial.C (s * cp * cr) =
        MvPolynomial.C (s * cp) * MvPolynomial.C cr := by
    rw [← MvPolynomial.C_mul]
  rw [hCcp, hCcr] at hcross
  have hprod :
      (MvPolynomial.C (s * cp) * L ^ n) *
        (MvPolynomial.C cp *
            HC4.Polynomial.hessian G r kernelCoordinate -
          MvPolynomial.C cr *
            HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate) = 0 := by
    linear_combination hcross
  have hinner :
      MvPolynomial.C cp *
            HC4.Polynomial.hessian G r kernelCoordinate =
        MvPolynomial.C cr *
            HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hfactor)

  calc
    HC4.Polynomial.hessian G r kernelCoordinate =
        MvPolynomial.C (cp⁻¹) *
          (MvPolynomial.C cp *
            HC4.Polynomial.hessian G r kernelCoordinate) := by
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [hcp]
    _ = MvPolynomial.C (cp⁻¹) *
          (MvPolynomial.C cr *
            HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate) := by
      rw [hinner]
    _ = MvPolynomial.C (cr / cp) *
          HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate := by
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [div_eq_mul_inv, mul_comm]
    _ = MvPolynomial.C (S.normalizedTopRatio r) *
          HC4.Polynomial.hessian G S.pivotCoordinate kernelCoordinate := by
      rfl

/-- The tangent source layer has the top gradient ratio on every source
coordinate. -/
theorem ThreeSchurTangentAtFirstBreak.kernelDerivative_gradientRatio
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M)
    (i : Fin 4) :
    MvPolynomial.pderiv i
        (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) =
      MvPolynomial.C (S.normalizedTopRatio i) *
        MvPolynomial.pderiv S.pivotCoordinate
          (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) := by
  let rho := kernelLastPerm kernelCoordinate
  generalize hr : rho.symm i = r
  have hrho : rho r = i := by
    rw [← hr]
    exact rho.apply_symm_apply i

  have hslot :
      MvPolynomial.pderiv (rho r)
          (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) =
        MvPolynomial.C (S.normalizedTopRatio (rho r)) *
          MvPolynomial.pderiv S.pivotCoordinate
            (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) := by
    fin_cases r
    · have hc := R.sourceLayer_cross_zero (0 : Fin 3)
      have hratio := linearPower_cross_cancel
        P S M.sourceLayer (rho 0) (by
          simpa [rho] using hc)
      simpa [HC4.Polynomial.hessian_apply,
        pderiv_comm_backport] using hratio
    · have hc := R.sourceLayer_cross_zero (1 : Fin 3)
      have hratio := linearPower_cross_cancel
        P S M.sourceLayer (rho 1) (by
          simpa [rho] using hc)
      simpa [HC4.Polynomial.hessian_apply,
        pderiv_comm_backport] using hratio
    · have hc := R.sourceLayer_cross_zero (2 : Fin 3)
      have hratio := linearPower_cross_cancel
        P S M.sourceLayer (rho 2) (by
          simpa [rho] using hc)
      simpa [HC4.Polynomial.hessian_apply,
        pderiv_comm_backport] using hratio
    · have hk :
          MvPolynomial.pderiv kernelCoordinate
              (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) = 0 := by
        simpa [sourceLayer, HC4.Polynomial.hessian_apply] using
          M.mixed.kernelDiagonal_eq_zero
      simpa [rho, kernelLastPerm_last, hk,
        TopKernelThreeSchurClockData.normalizedTopRatio,
        P.kernel_ratio_zero]
  simpa [hrho] using hslot

/-- The pivot derivative of the kernel derivative is genuinely nonzero. -/
theorem ThreeSchurTangentAtFirstBreak.kernelDerivative_pivot_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    MvPolynomial.pderiv S.pivotCoordinate
      (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) ≠ 0 := by
  have hmixed :
      MvPolynomial.pderiv M.mixed.layer.index
          (MvPolynomial.pderiv kernelCoordinate M.sourceLayer) ≠ 0 := by
    intro hz
    apply M.mixed.mixed_ne_zero
    have hcomm :=
      pderiv_comm_backport
        M.mixed.layer.index kernelCoordinate M.sourceLayer
    rw [hcomm] at hz
    simpa [HC4.Polynomial.hessian_apply] using hz
  intro hpivot
  have hratio :=
    R.kernelDerivative_gradientRatio M.mixed.layer.index
  rw [hpivot] at hratio
  simp at hratio
  exact hmixed hratio

/-- The exact lower source layer is ordinary homogeneous of its stored
degree. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.sourceLayer_homogeneous
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    M.sourceLayer.IsHomogeneous M.mixed.layer.sourceDegree := by
  have h :=
    fourOrdinaryDegreeComponent_isHomogeneous
      T.topKernelReesSource M.mixed.layer.sourceDegree
  simpa [sourceLayer, fourOrdinaryDegreeComponent,
    ordinaryTopNatWeight, fourOrdinaryIntegerWeight] using h

/-- Explicit linear-power packet carried by the tangent branch. -/
structure ThreeSchurTangentKernelDerivativeLinearPowerData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1) where
  tangent : ThreeSchurTangentAtFirstBreak S M
  coefficient : K
  kernelDerivative_eq_power :
    MvPolynomial.pderiv kernelCoordinate M.sourceLayer =
      MvPolynomial.C coefficient *
        (gradientRatioLinearForm S.normalizedTopRatio) ^
          (M.mixed.layer.sourceDegree - 1)

/-- **Tangent branch linear-power rigidity.**

The kernel derivative of the first lower source layer is a scalar multiple of
the (E-1)-st power of the normalized top linear direction. -/
theorem ThreeSchurTangentAtFirstBreak.toKernelDerivativeLinearPowerData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    Nonempty (ThreeSchurTangentKernelDerivativeLinearPowerData S M) := by
  let A :=
    MvPolynomial.pderiv kernelCoordinate M.sourceLayer
  have hhomG := M.sourceLayer_homogeneous
  have hhomA : A.IsHomogeneous (M.mixed.layer.sourceDegree - 1) := by
    dsimp [A]
    simpa using hhomG.pderiv
  have hdeg3 : 3 ≤ M.mixed.layer.sourceDegree :=
    M.sourceDegree_ge_three
  have hdegpos : 0 < M.mixed.layer.sourceDegree - 1 := by
    omega
  have hpivot :
      MvPolynomial.pderiv S.pivotCoordinate A ≠ 0 := by
    simpa [A] using R.kernelDerivative_pivot_ne_zero
  have hratio :
      ∀ i : Fin 4,
        MvPolynomial.pderiv i A =
          MvPolynomial.C (S.normalizedTopRatio i) *
            MvPolynomial.pderiv S.pivotCoordinate A := by
    intro i
    simpa [A] using R.kernelDerivative_gradientRatio i
  rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
      (M.mixed.layer.sourceDegree - 1)
      A hhomA hdegpos
      S.pivotCoordinate hpivot
      S.normalizedTopRatio hratio with
    ⟨a, ha⟩
  exact ⟨{
    tangent := R
    coefficient := a
    kernelDerivative_eq_power := by
      simpa [A] using ha
  }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
