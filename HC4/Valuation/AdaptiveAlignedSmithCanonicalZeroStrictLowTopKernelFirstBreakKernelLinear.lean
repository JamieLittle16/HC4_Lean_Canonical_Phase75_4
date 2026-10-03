import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakMixedNonlinear
import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import Mathlib.Tactic

/-!
# Kernel-linear support form of the final top-kernel residual

The nonlinear mixed first-break packet retains an exact ordinary homogeneous
source layer G_E of degree E >= 3 with

    Hess(G_E)_{k,k} = 0
    Hess(G_E)_{i,k} != 0

for a coordinate i != k.

Characteristic zero turns this Hessian statement into a precise support
statement.

* The zero pure second derivative forces every supported monomial to have
  k-exponent at most one.
* The nonzero mixed derivative produces an actual supported monomial with
  k-exponent exactly one and positive i-exponent.

Thus the residual lower layer is genuinely linear in the kernel coordinate
and genuinely coupled to another source coordinate.  This is the support
normal form required by the finite staircase / direction-lock continuation.

No terminal cocharacter, progress theorem, or JC2 input is used.
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

/-- The exact lower source layer stored by a nonlinear mixed first break. -/
noncomputable def exactNonlinearMixedLayer
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm
    (fun i => (ordinaryTopNatWeight i : ℤ))
    (M.mixed.layer.sourceDegree : ℤ)
    T.topKernelReesSource

/-- Every supported monomial of the residual layer is at most linear in the
stored kernel coordinate. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.kernelExponent_le_one
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    ∀ d ∈ M.exactNonlinearMixedLayer.support,
      d kernelCoordinate ≤ 1 := by
  intro d hd
  by_contra hnot
  have hd2 : 2 ≤ d kernelCoordinate := by omega
  have hne :=
    pderiv_pderiv_ne_zero_of_support_exponent_ge_two
      (K := K) kernelCoordinate M.exactNonlinearMixedLayer d hd hd2
  apply hne
  simpa [exactNonlinearMixedLayer, HC4.Polynomial.hessian_apply] using
    M.mixed.kernelDiagonal_eq_zero

/-- The nonzero mixed Hessian entry comes from an actual source monomial
which is linear in the kernel coordinate and uses the retained mixed
coordinate positively. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.exists_kernelLinear_coupledSupport
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    ∃ d ∈ M.exactNonlinearMixedLayer.support,
      d kernelCoordinate = 1 ∧
      0 < d M.mixed.layer.index := by
  let G := M.exactNonlinearMixedLayer
  let i := M.mixed.layer.index
  have hik : HC4.Polynomial.hessian G i kernelCoordinate ≠ 0 := by
    simpa [G, i, exactNonlinearMixedLayer] using M.mixed.mixed_ne_zero
  have hder :
      MvPolynomial.pderiv kernelCoordinate
        (MvPolynomial.pderiv i G) ≠ 0 := by
    simpa [HC4.Polynomial.hessian_apply] using hik

  rcases MvPolynomial.support_nonempty.mpr hder with ⟨m, hm⟩
  have hmcoeff :
      MvPolynomial.coeff m
        (MvPolynomial.pderiv kernelCoordinate
          (MvPolynomial.pderiv i G)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm

  let d1 : Fin 4 →₀ ℕ := m + Finsupp.single kernelCoordinate 1
  have hd1coeff :
      MvPolynomial.coeff d1 (MvPolynomial.pderiv i G) ≠ 0 := by
    have hformula :=
      coeff_pderiv_backport
        (K := K) kernelCoordinate (MvPolynomial.pderiv i G) m
    rw [show m + Finsupp.single kernelCoordinate 1 = d1 by rfl] at hformula
    intro hz
    apply hmcoeff
    rw [hformula, hz]
    simp

  let d : Fin 4 →₀ ℕ := d1 + Finsupp.single i 1
  have hdcoeff : MvPolynomial.coeff d G ≠ 0 := by
    have hformula :=
      coeff_pderiv_backport (K := K) i G d1
    rw [show d1 + Finsupp.single i 1 = d by rfl] at hformula
    intro hz
    apply hd1coeff
    rw [hformula, hz]
    simp

  have hdmem : d ∈ G.support := MvPolynomial.mem_support_iff.mpr hdcoeff
  have hikne : i ≠ kernelCoordinate := M.mixed.layer.index_ne_kernel
  have hkpos : 0 < d kernelCoordinate := by
    dsimp [d, d1]
    simp [Finsupp.single_apply, hikne, Ne.symm hikne]
  have hkle : d kernelCoordinate ≤ 1 := by
    exact M.kernelExponent_le_one d (by simpa [G] using hdmem)
  have hkeq : d kernelCoordinate = 1 := by omega
  have hipos : 0 < d i := by
    dsimp [d]
    simp [Finsupp.single_apply]
  exact ⟨d, by simpa [G] using hdmem, hkeq, by simpa [i] using hipos⟩

/-- Source-facing packet for the genuinely surviving lower layer. -/
structure ExactKernelLinearCoupledOrdinaryLayerData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  residual : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak
  kernelExponent_le_one :
    ∀ d ∈ residual.exactNonlinearMixedLayer.support,
      d kernelCoordinate ≤ 1
  coupledExponent : Fin 4 →₀ ℕ
  coupled_mem :
    coupledExponent ∈ residual.exactNonlinearMixedLayer.support
  coupled_kernel_eq_one :
    coupledExponent kernelCoordinate = 1
  coupled_index_pos :
    0 < coupledExponent residual.mixed.layer.index

/-- Package the exact kernel-linear coupled support normal form. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.toKernelLinearCoupledData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    Nonempty P.ExactKernelLinearCoupledOrdinaryLayerData := by
  rcases M.exists_kernelLinear_coupledSupport with
    ⟨d, hd, hdk, hdi⟩
  exact ⟨{
    residual := M
    kernelExponent_le_one := M.kernelExponent_le_one
    coupledExponent := d
    coupled_mem := hd
    coupled_kernel_eq_one := hdk
    coupled_index_pos := hdi
  }⟩

/-- **Kernel-linear top-kernel frontier.**

After all currently green source lifts and low-degree eliminations, the only
top-kernel residual is an exact strictly lower nonlinear ordinary layer which
is linear in the stored kernel coordinate and genuinely coupled to another
coordinate. -/
theorem actualRankTwo_or_exactKernelLinearCoupledLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactKernelLinearCoupledOrdinaryLayerData := by
  rcases P.actualRankTwo_or_exactLowerNonlinearMixedLayer with
    hactual | hres
  · exact Or.inl hactual
  · rcases hres with ⟨M⟩
    exact Or.inr M.toKernelLinearCoupledData

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
