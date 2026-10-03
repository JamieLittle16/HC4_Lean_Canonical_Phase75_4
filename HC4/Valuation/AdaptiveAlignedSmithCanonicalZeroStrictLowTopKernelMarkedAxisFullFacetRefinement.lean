import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisLinearPowerBoundaryFrontier
import Mathlib.Tactic

/-!
# E2: rigidity of the full marked-facet linear-power branch

In the full marked-facet branch every exponent of the singular maximal
ordinary top face has longitudinal exponent zero.  The exact marked-axis
support identity therefore loses no coefficient at all: the collision-bearing
marked fibre is literally the retained top face.

For a top face which is a scalar power of one linear form this confinement has
a further concrete consequence.  The coefficient of coordinate zero in that
linear form must vanish.  Hence, unless the already-retained top-face kernel is
coordinate zero itself, the linear form omits two distinct source coordinates:
the marked coordinate and the stored kernel coordinate.

This is still support/rigidity data only.  No singular face is promoted to a
terminal endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- If the whole top face lies on the marked facet, the exact marked-axis
initial form is literally that top face, coefficient for coefficient. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_eq_topFace_of_onMarkedFacet
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily =
      T.topFace.face := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ T.topFace.face.support
  · have hon := hfacet d hd
    have hzero : d (0 : Fin 4) = 0 := by
      have htoric :=
        (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).1 hon
      simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric
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
      have hs :=
        (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
          d).1 hmarked
      exact hd hs.1
    rw [MvPolynomial.notMem_support_iff.mp hnotMarked,
      MvPolynomial.notMem_support_iff.mp hd]

namespace TopFaceLinearPowerKernelData

variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Marked-facet confinement kills the longitudinal coefficient of the
top-face linear form. -/
theorem ratio_zero_of_topFaceOnMarkedFacet
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    P.ratio (0 : Fin 4) = 0 := by
  have hderiv :
      MvPolynomial.pderiv (0 : Fin 4) T.topFace.face = 0 := by
    apply pderiv_eq_zero_of_all_supported_exponents_zero
    intro d hdcoeff
    have hd : d ∈ T.topFace.face.support :=
      MvPolynomial.mem_support_iff.mpr hdcoeff
    have hon := hfacet d hd
    have htoric :=
      (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).1 hon
    simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric

  have hm3 : 3 ≤ T.topFace.degree :=
    T.topFace.degree_ge_three
  have hmne : T.topFace.degree ≠ 0 := by omega
  have hmK : (T.topFace.degree : K) ≠ 0 := by
    exact_mod_cast hmne
  have hL_ne : gradientRatioLinearForm P.ratio ≠ 0 :=
    P.linearForm_ne_zero
  have hpow :
      (gradientRatioLinearForm P.ratio) ^ (T.topFace.degree - 1) ≠ 0 :=
    pow_ne_zero _ hL_ne
  have hpowderiv :=
    pderiv_gradientRatioLinearForm_pow_succ
      P.ratio (0 : Fin 4) (T.topFace.degree - 1)
  have hmrepr :
      T.topFace.degree - 1 + 1 = T.topFace.degree := by
    omega
  rw [hmrepr] at hpowderiv
  rw [P.eq_power, MvPolynomial.pderiv_C_mul, hpowderiv] at hderiv
  have hCa :
      (MvPolynomial.C P.coefficient : MvPolynomial (Fin 4) K) ≠ 0 := by
    simpa using P.coefficient_ne_zero
  have hrest :
      MvPolynomial.C
            ((T.topFace.degree : K) * P.ratio (0 : Fin 4)) *
          (gradientRatioLinearForm P.ratio) ^ (T.topFace.degree - 1) = 0 :=
    (mul_eq_zero.mp hderiv).resolve_left hCa
  have hCscalar :
      MvPolynomial.C
          ((T.topFace.degree : K) * P.ratio (0 : Fin 4)) = 0 :=
    (mul_eq_zero.mp hrest).resolve_right hpow
  have hscalar :
      (T.topFace.degree : K) * P.ratio (0 : Fin 4) = 0 := by
    simpa using hCscalar
  exact (mul_eq_zero.mp hscalar).resolve_left hmK

/-- Exact kernel split retained by the full marked-facet branch. -/
inductive TopKernelMarkedAxisFullFacetKernelSplit
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | markedKernel
      (kernel_eq_zero : kernelCoordinate = (0 : Fin 4))
  | twoCoordinateKernel
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
      (marked_ratio_zero : P.ratio (0 : Fin 4) = 0)
      (kernel_ratio_zero : P.ratio kernelCoordinate = 0)

/-- A full marked-facet linear-power branch either has the marked coordinate
as its stored kernel, or the top linear form omits two distinct coordinates. -/
theorem fullMarkedFacetKernelSplit
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    Nonempty P.TopKernelMarkedAxisFullFacetKernelSplit := by
  by_cases hk : kernelCoordinate = (0 : Fin 4)
  · exact ⟨.markedKernel hk⟩
  · exact ⟨.twoCoordinateKernel hk
      (P.ratio_zero_of_topFaceOnMarkedFacet hfacet)
      P.kernel_ratio_zero⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
