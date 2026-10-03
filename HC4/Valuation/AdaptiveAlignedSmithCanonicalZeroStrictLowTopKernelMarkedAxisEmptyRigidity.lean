import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisSupportFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# E1: rigidity of an empty marked-axis slice in the top-kernel branch

The exact E1 support frontier has one apparently degenerate constructor: the
marked-axis first-contact fibre may be zero because the singular maximal top
face has no exponent with longitudinal coordinate zero.

In the residual top-kernel branch the same top face is already known to be a
nonzero scalar multiple of a power of one linear form.  That extra structure
makes the empty-slice case completely rigid.  Evaluating the top face at each
transverse coordinate-axis point gives zero from the support condition, but
the linear-power normal form evaluates there as

    a * c_j^D.

Since `a != 0` and `D > 0`, every transverse coefficient `c_j` vanishes.
Thus the top face is literally a nonzero pure `X₀^D` power.  In particular
the stored top-face kernel coordinate cannot itself be coordinate zero.

No new Rees family, Schur clock, or terminal conclusion is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Vanishing of the marked-axis slice means that the singular top face has
no monomial with longitudinal exponent zero. -/
theorem noZeroCoordinateSupport_of_markedAxisFibre_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfibre :
      polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0) :
    ¬ (zeroCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty := by
  intro hzero
  rcases hzero with ⟨d, hd⟩
  have hspec := mem_zeroCoordinateSupport.mp hd
  have hmarked :
      d ∈ (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support := by
    apply
      (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
        d).2
    exact hspec
  rw [hfibre] at hmarked
  simpa using hmarked

/-- If the marked slice is empty, every transverse coefficient of the
top-face linear form vanishes. -/
theorem ratio_eq_zero_of_ne_zero_of_markedAxisFibre_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfibre :
      polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0)
    (j : Fin 4)
    (hj0 : j ≠ (0 : Fin 4)) :
    P.ratio j = 0 := by
  classical
  have hnozero :=
    P.noZeroCoordinateSupport_of_markedAxisFibre_eq_zero hfibre
  let point : Fin 4 → K :=
    coordinateAxisPoint (K := K) j

  have htopEval :
      MvPolynomial.eval point T.topFace.face = 0 := by
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_eq_zero
    intro d hd
    have hd0ne : d (0 : Fin 4) ≠ 0 := by
      intro hd0
      exact hnozero
        ⟨d, mem_zeroCoordinateSupport.mpr ⟨hd, hd0⟩⟩
    have hd0pos : 0 < d (0 : Fin 4) :=
      Nat.pos_of_ne_zero hd0ne
    have hpoint0 : point (0 : Fin 4) = 0 := by
      simp [point, coordinateAxisPoint, Ne.symm hj0]
    have hprod :
        ∏ i : Fin 4, point i ^ d i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
      rw [hpoint0]
      exact zero_pow (Nat.ne_of_gt hd0pos)
    rw [hprod, mul_zero]

  have hlineEval :
      MvPolynomial.eval point
          (gradientRatioLinearForm P.ratio) =
        P.ratio j := by
    simp [point, gradientRatioLinearForm, coordinateAxisPoint]

  have heval :
      0 = P.coefficient * P.ratio j ^ T.topFace.degree := by
    calc
      0 = MvPolynomial.eval point T.topFace.face := htopEval.symm
      _ = MvPolynomial.eval point
          (MvPolynomial.C P.coefficient *
            (gradientRatioLinearForm P.ratio) ^ T.topFace.degree) := by
            rw [P.eq_power]
      _ = P.coefficient * P.ratio j ^ T.topFace.degree := by
            simp [hlineEval]
  by_contra hj
  have hright :
      P.coefficient * P.ratio j ^ T.topFace.degree ≠ 0 :=
    mul_ne_zero P.coefficient_ne_zero
      (pow_ne_zero T.topFace.degree hj)
  exact hright heval.symm

/-- The top linear form in the empty-slice branch is literally longitudinal. -/
theorem linearForm_eq_longitudinalAxis_of_markedAxisFibre_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfibre :
      polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0) :
    gradientRatioLinearForm P.ratio =
      MvPolynomial.C (P.ratio (0 : Fin 4)) *
        MvPolynomial.X (0 : Fin 4) := by
  classical
  unfold gradientRatioLinearForm
  rw [Finset.sum_eq_single (0 : Fin 4)]
  · intro j _ hj
    rw [P.ratio_eq_zero_of_ne_zero_of_markedAxisFibre_eq_zero
      hfibre j hj]
    simp
  · simp

/-- The surviving longitudinal coefficient is nonzero. -/
theorem longitudinal_ratio_ne_zero_of_markedAxisFibre_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfibre :
      polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0) :
    P.ratio (0 : Fin 4) ≠ 0 := by
  intro hzero
  apply P.linearForm_ne_zero
  rw [P.linearForm_eq_longitudinalAxis_of_markedAxisFibre_eq_zero hfibre,
    hzero]
  simp

/-- **Empty marked slice = exact nonzero pure longitudinal top power.**

This is the useful E-stage form of the empty support constructor. -/
theorem pureLongitudinalTopFace_of_markedAxisFibre_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfibre :
      polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0) :
    ∃ b : K,
      b ≠ 0 ∧
      T.topFace.face =
        MvPolynomial.C b *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree ∧
      kernelCoordinate ≠ (0 : Fin 4) := by
  let b : K :=
    P.coefficient * (P.ratio (0 : Fin 4)) ^ T.topFace.degree
  have hr0 :
      P.ratio (0 : Fin 4) ≠ 0 :=
    P.longitudinal_ratio_ne_zero_of_markedAxisFibre_eq_zero hfibre
  have hb : b ≠ 0 := by
    dsimp [b]
    exact mul_ne_zero P.coefficient_ne_zero
      (pow_ne_zero T.topFace.degree hr0)
  have hface :
      T.topFace.face =
        MvPolynomial.C b *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree := by
    rw [P.eq_power,
      P.linearForm_eq_longitudinalAxis_of_markedAxisFibre_eq_zero hfibre,
      mul_pow, ← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]
  have hk : kernelCoordinate ≠ (0 : Fin 4) := by
    intro h
    have hz0 : P.ratio (0 : Fin 4) = 0 := by
      simpa only [h] using P.kernel_ratio_zero
    exact hr0 hz0
  exact ⟨b, hb, hface, hk⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
