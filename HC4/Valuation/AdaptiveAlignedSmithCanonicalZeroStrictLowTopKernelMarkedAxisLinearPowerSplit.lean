import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# E1: marked-axis support split in the actual top-kernel linear-power residual

The unresolved top-kernel branch already retains an exact normal form

    topFace = a * L^D

and a coordinate `kernelCoordinate` omitted from `L`.  The marked-axis
first-contact fibre is exactly the `d₀ = 0` slice of that top face.

There are therefore only two support geometries left before endpoint
extraction:

* if the stored top kernel is the marked coordinate itself, every top-face
  monomial already has `d₀ = 0`, so the marked fibre is literally the whole
  singular top face;
* if the stored kernel is different from the marked coordinate, every marked
  monomial has zero exponent in two distinct coordinates, hence the marked
  fibre is genuinely binary-supported.

This is a support/refinement theorem only.  No torus balance, repair progress,
or terminal endpoint certificate is manufactured here.
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

/-- The retained linear-power normal form really is independent of its stored
kernel coordinate. -/
theorem topFace_pderiv_kernel_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    MvPolynomial.pderiv kernelCoordinate T.topFace.face = 0 := by
  rw [P.eq_power, MvPolynomial.pderiv_C_mul]
  have hformula :=
    pderiv_gradientRatioLinearForm_pow_succ
      P.ratio kernelCoordinate (T.topFace.degree - 1)
  have hrepr :
      T.topFace.degree - 1 + 1 = T.topFace.degree := by
    have hdeg := T.topFace.degree_ge_three
    omega
  rw [hrepr] at hformula
  rw [hformula, P.kernel_ratio_zero]
  simp

/-- The marked first-contact fibre inherits the stored top-face coordinate
kernel. -/
theorem markedAxisFirstContact_pderiv_kernel_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    MvPolynomial.pderiv kernelCoordinate
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) = 0 := by
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hd
  have htop :
      d ∈ T.topFace.face.support :=
    (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
      d).1 hd |>.1
  exact
    exponent_eq_zero_of_pderiv_eq_zero
      kernelCoordinate T.topFace.face P.topFace_pderiv_kernel_eq_zero d
      (MvPolynomial.mem_support_iff.mp htop)

/-- If the actual top face is already independent of the marked coordinate,
the marked-axis first-contact operation loses no term at all: its special
fibre is literally the retained singular top face. -/
theorem markedAxisFirstContact_specialFiber_eq_topFace_of_pderiv_zero
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hzero :
      MvPolynomial.pderiv (0 : Fin 4) T.topFace.face = 0) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily =
      T.topFace.face := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ T.topFace.face.support
  · have hd0 : d (0 : Fin 4) = 0 :=
      exponent_eq_zero_of_pderiv_eq_zero
        (0 : Fin 4) T.topFace.face hzero d
        (MvPolynomial.mem_support_iff.mp hd)
    have hdeg :
        HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree :=
      T.topFace.ordinaryDegree_eq_of_mem_support hd
    have htrans :
        d 1 + d 2 + d 3 = T.topFace.degree := by
      unfold HC4.Polynomial.ordinaryDegree4 at hdeg
      omega
    have hw :
        Finsupp.weight
            (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
          (T.topFace.degree : ℤ) := by
      rw [weight_topKernelMarkedAxisIntWeight]
      exact_mod_cast htrans
    rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
      HC4.Polynomial.coeff_initialForm, if_pos hw,
      T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    rfl
  · have hnotMarked :
        d ∉ (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support := by
      intro hmarked
      apply hd
      exact
        (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
          d).1 hmarked |>.1
    rw [MvPolynomial.notMem_support_iff.mp hnotMarked,
      MvPolynomial.notMem_support_iff.mp hd]

/-- In the branch where the stored top kernel is the marked coordinate, the
collision-bearing marked fibre is exactly the whole linear-power top face. -/
theorem markedAxisFirstContact_specialFiber_eq_topFace_of_kernel_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hk : kernelCoordinate = (0 : Fin 4)) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily =
      T.topFace.face := by
  subst kernelCoordinate
  exact
    markedAxisFirstContact_specialFiber_eq_topFace_of_pderiv_zero
      T P.topFace_pderiv_kernel_eq_zero

/-- Exact E1 support split for the true top-kernel linear-power residual. -/
inductive TopKernelMarkedAxisLinearPowerSupportSplit
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | markedKernel
      (kernel_eq_zero : kernelCoordinate = (0 : Fin 4))
      (fibre_eq_topFace :
        polynomialFamilySpecialFiber
            T.topKernelMarkedAxisFirstContactFamily =
          T.topFace.face)
  | binarySupported
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
      (markedKernel :
        MvPolynomial.pderiv kernelCoordinate
            (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily) = 0)
      (support_two_zero :
        ∀ d ∈ (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily).support,
          d (0 : Fin 4) = 0 ∧ d kernelCoordinate = 0)

/-- Every top-kernel linear-power residual reaches the finite E1 split:
either the marked fibre equals the whole top face, or it is supported in the
two-coordinate plane complementary to two distinct zero coordinates. -/
theorem markedAxisLinearPowerSupportSplit
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelMarkedAxisLinearPowerSupportSplit := by
  by_cases hk : kernelCoordinate = (0 : Fin 4)
  · exact ⟨.markedKernel hk
      (P.markedAxisFirstContact_specialFiber_eq_topFace_of_kernel_zero hk)⟩
  · refine ⟨.binarySupported hk
      P.markedAxisFirstContact_pderiv_kernel_eq_zero ?_⟩
    intro d hd
    have hslice :=
      (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
        d).1 hd
    have hkzero :=
      exponent_eq_zero_of_pderiv_eq_zero
        kernelCoordinate T.topFace.face P.topFace_pderiv_kernel_eq_zero d
        (MvPolynomial.mem_support_iff.mp hslice.1)
    exact ⟨hslice.2, hkzero⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
