import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRankSplit
import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# Honest ordinary reverse Rees for the A19.55 top-kernel branch

The rank-one residual of the top-kernel split lives on the *actual maximal
ordinary top face* of the represented determinant-one special fibre.  This
file attaches the standard bounded reverse weighted Rees family for ordinary
degree.

Parameter `0` is exactly the stored A19 top face and parameter `1` is exactly
the represented source special fibre.  This is an auxiliary interpolation
only: its parameter order is never identified with the zero blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural ordinary-degree weight in four variables. -/
def ordinaryTopNatWeight : Fin 4 → ℕ := fun _ => 1

@[simp] theorem weight_ordinaryTopNatWeight
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight ordinaryTopNatWeight d = ordinaryDegree4 d := by
  have hweight :
      Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  rw [ordinaryTopNatWeight, hweight]
  exact HC4.Valuation.finsuppDegree_eq_ordinaryDegree4 d

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state)

/-- Literal represented determinant-one source whose maximal ordinary face is
`T.topFace.face`. -/
def topKernelReesSource : MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber T.terminal.blocker.presented.family

/-- The stored maximality theorem is exactly the natural reverse-Rees support
bound for ordinary degree. -/
theorem topKernelReesSource_hasReverseWeightBound :
    HasReverseWeightBound ordinaryTopNatWeight T.topFace.degree
      T.topKernelReesSource := by
  intro d hd
  rw [weight_ordinaryTopNatWeight]
  exact T.topFace.maximal d (by simpa [topKernelReesSource] using hd)

/-- Honest auxiliary ordinary reverse-Rees family from the actual represented
source down to its selected maximal top face. -/
noncomputable def topKernelReverseReesFamily :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily ordinaryTopNatWeight T.topFace.degree
    T.topKernelReesSource T.topKernelReesSource_hasReverseWeightBound

/-- Parameter `0` is literally the stored singular top face. -/
theorem topKernelReverseRees_specialFiber_eq_topFace :
    polynomialFamilySpecialFiber T.topKernelReverseReesFamily =
      T.topFace.face := by
  rw [topKernelReverseReesFamily]
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
  rw [T.topFace.face_eq]
  congr 2
  funext i
  rfl

/-- Parameter `1` recovers the represented source special fibre exactly. -/
theorem topKernelReverseRees_evalOne_eq_source :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K))
        T.topKernelReverseReesFamily =
      T.topKernelReesSource := by
  ext d
  rw [MvPolynomial.coeff_map]
  rw [topKernelReverseReesFamily, reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ T.topKernelReesSource.support
  · simp [hd]
  · have hc : MvPolynomial.coeff d T.topKernelReesSource = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hc]

/-- The represented source endpoint of this auxiliary interpolation still has
literal Hessian determinant one. -/
theorem topKernelReesSource_hessianDeterminant_eq_one :
    HC4.Polynomial.hessianDeterminant T.topKernelReesSource = 1 := by
  simpa [topKernelReesSource] using
    T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
