import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerDirectTest
import Mathlib.Tactic

/-!
# Potential-level timing on the marked-axis first-contact family

The marked-axis first-contact construction is an honest polynomial potential
family carrying the constant marked collision `0 ~ e₀`.  Its pure Hessian
clock is already known exactly:

    det Hess(P) = X^(4D - 6).

This file applies the generic first-actual-layer causality and direct-closing
quadratic test directly to that *potential family*.  Thus no Schur polynomial
is identified with a potential.

The canonical first positive actual parameter layer occurs no later than the
marked-axis Hessian closing exponent.  At equality, the actual potential layer
already contains a genuine quadratic source coefficient.

No terminal cocharacter and no JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The honest marked-axis first-contact potential family necessarily has a
positive actual source layer because its exact Hessian defect is positive. -/
theorem topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasPositiveActualParameterLayer T.topKernelMarkedAxisFirstContactFamily := by
  exact
    hasPositiveActualParameterLayer_of_hessianDefect_pos
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
      T.topKernelMarkedAxisFirstContact_defect_pos

/-- Canonical least positive actual layer of the collision-bearing marked-axis
first-contact potential family. -/
noncomputable def topKernelMarkedAxisFirstActualLayerOrder
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : ℕ :=
  firstPositiveActualParameterOrder
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer

/-- The marked-axis first actual layer is genuinely positive. -/
theorem topKernelMarkedAxisFirstActualLayerOrder_pos
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    0 < T.topKernelMarkedAxisFirstActualLayerOrder := by
  exact
    firstPositiveActualParameterOrder_pos
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer

/-- Causality for the honest marked-axis potential family: its first actual
source deformation occurs no later than its exact pure Hessian closing clock. -/
theorem topKernelMarkedAxisFirstActualLayerOrder_le_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.topKernelMarkedAxisFirstActualLayerOrder ≤
      4 * T.topFace.degree - 6 := by
  simpa [topKernelMarkedAxisFirstActualLayerOrder] using
    firstPositiveActualParameterOrder_le_hessianDefect
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
      T.topKernelMarkedAxisFirstContact_defect_pos

/-- If the first actual potential layer occurs exactly at determinant closure,
its source-origin Hessian is already nonzero. -/
theorem topKernelMarkedAxisFirstActualLayer_originHessian_ne_zero_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    quadraticFamilyHessianMatrix
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) ≠ 0 := by
  simpa [topKernelMarkedAxisFirstActualLayerOrder] using
    firstPositiveActualParameterLayer_originHessian_ne_zero_of_eq_hessianDefect
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
      (by simpa [topKernelMarkedAxisFirstActualLayerOrder] using heq)

/-- Therefore exact marked-axis closing is visible in an actual quadratic
coefficient of the original collision-bearing potential family. -/
theorem topKernelMarkedAxisFirstActualLayer_hasQuadraticCoefficient_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    ∃ i k : Fin 4,
      (MvPolynomial.coeff
          (Finsupp.single k 1 + Finsupp.single i 1)
          T.topKernelMarkedAxisFirstContactFamily).coeff
        T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0 := by
  have hH :=
    T.topKernelMarkedAxisFirstActualLayer_originHessian_ne_zero_of_eq_defect heq
  by_contra hnot
  push_neg at hnot
  apply hH
  apply Matrix.ext
  intro i k
  have hqcoeff :
      MvPolynomial.coeff
          (Finsupp.single k 1 + Finsupp.single i 1)
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) = 0 := by
    rw [familyParameterLayer_coeff]
    exact hnot i k
  rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
  rw [hqcoeff]
  simp

/-- No quadratic source exponent occurs on the marked-axis special fibre:
that fibre is exactly a zero-longitudinal slice of the maximal ordinary
degree-`D` top face, and `D ≥ 3`. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_no_quadratic
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i k : Fin 4) :
    Finsupp.single k 1 + Finsupp.single i 1 ∉
      (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support := by
  intro hmem
  have hslice :=
    (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
      (Finsupp.single k 1 + Finsupp.single i 1)).1 hmem
  have hdeg :=
    T.topFace.ordinaryDegree_eq_of_mem_support hslice.1
  have hquad :
      HC4.Polynomial.ordinaryDegree4
        (Finsupp.single k 1 + Finsupp.single i 1) = 2 := by
    unfold HC4.Polynomial.ordinaryDegree4
    fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_four]
  rw [hquad] at hdeg
  have hD := T.topFace.degree_ge_three
  omega

/-- Hence the exact-closing quadratic coefficient is genuinely fresh and its
whole-family coefficient has exact positive parameter order equal to the
marked-axis determinant closing exponent. -/
theorem topKernelMarkedAxisFirstActualLayer_freshQuadratic_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    ∃ i k : Fin 4,
      ∃ hd :
        Finsupp.single k 1 + Finsupp.single i 1 ∈
          T.topKernelMarkedAxisFirstContactFamily.support,
        Finsupp.single k 1 + Finsupp.single i 1 ∉
            (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily).support ∧
          smithFamilyCoefficientParameterOrder
              T.topKernelMarkedAxisFirstContactFamily
              (Finsupp.single k 1 + Finsupp.single i 1) hd =
            T.topKernelMarkedAxisFirstActualLayerOrder := by
  rcases T.topKernelMarkedAxisFirstActualLayer_hasQuadraticCoefficient_of_eq_defect
      heq with ⟨i, k, hcoeff⟩
  let d := Finsupp.single k 1 + Finsupp.single i 1
  have hd : d ∈ T.topKernelMarkedAxisFirstContactFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply hcoeff
    have hzj := congrArg
      (fun p : Polynomial K => p.coeff
        T.topKernelMarkedAxisFirstActualLayerOrder) hz
    simpa [d] using hzj
  have hfresh :
      d ∉ (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support := by
    simpa [d] using
      T.topKernelMarkedAxisFirstContact_specialFiber_no_quadratic i k
  have hsplit :=
    smithFamilyCoefficientParameterOrder_zero_or_firstPositiveActual
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
      hd hcoeff
  have horder :
      smithFamilyCoefficientParameterOrder
          T.topKernelMarkedAxisFirstContactFamily d hd =
        T.topKernelMarkedAxisFirstActualLayerOrder := by
    rcases hsplit with hzero | hfirst
    · exfalso
      apply hfresh
      apply
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          T.topKernelMarkedAxisFirstContactFamily hd).1
      rw [smithFamilyCoefficientOrder_eq
        T.topKernelMarkedAxisFirstContactFamily hd]
      exact hzero
    · simpa [topKernelMarkedAxisFirstActualLayerOrder, d] using hfirst
  exact ⟨i, k, hd, by simpa [d] using hfresh, by simpa [d] using horder⟩

/-- Honest potential-level timing frontier for the marked-axis first-contact
family.  The equality branch retains a genuine quadratic source coefficient,
not merely a nonzero Schur entry. -/
inductive TopKernelMarkedAxisPotentialTimingFrontier
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | preclosing
      (order_lt :
        T.topKernelMarkedAxisFirstActualLayerOrder <
          4 * T.topFace.degree - 6)
  | exactClosingQuadratic
      (order_eq :
        T.topKernelMarkedAxisFirstActualLayerOrder =
          4 * T.topFace.degree - 6)
      (i k : Fin 4)
      (coefficient_ne_zero :
        (MvPolynomial.coeff
            (Finsupp.single k 1 + Finsupp.single i 1)
            T.topKernelMarkedAxisFirstContactFamily).coeff
          T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0)

/-- The marked-axis collision-bearing potential always reaches the finite
preclosing/direct-quadratic timing split. -/
theorem topKernelMarkedAxisPotentialTimingFrontier_nonempty
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.TopKernelMarkedAxisPotentialTimingFrontier := by
  rcases Nat.lt_or_eq_of_le T.topKernelMarkedAxisFirstActualLayerOrder_le_defect with
    hlt | heq
  · exact ⟨.preclosing hlt⟩
  · rcases T.topKernelMarkedAxisFirstActualLayer_hasQuadraticCoefficient_of_eq_defect
      heq with ⟨i, k, hcoeff⟩
    exact ⟨.exactClosingQuadratic heq i k hcoeff⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
