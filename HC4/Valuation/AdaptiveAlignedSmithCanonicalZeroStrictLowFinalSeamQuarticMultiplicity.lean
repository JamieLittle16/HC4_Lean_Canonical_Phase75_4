import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticAxisFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamExactHessianOrder
import Mathlib.Tactic

/-!
# G19: quartic strict-low endpoint multiplicity is at most one

The three final strict-low residuals have the honest two-endpoint forms

* pure longitudinal: A' = X (X-1) C;
* low-negative-first: A = X (X-1) B;
* low-negative-second: A = X (X-1) B.

G18 proves that, under maximal ordinary source degree at most four, the
corresponding represented axis-gradient polynomial has degree at most three.
Therefore C or B has degree at most one.

The endpoint normal form used by G3 writes that residual as

    (X-1)^m * terminal,

with

    degree terminal + m = degree residual.

Hence m <= 1.  The arbitrary endpoint-stripping recursion has collapsed to a
literal binary case in the quartic seam.

No terminal weight, progress theorem, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Quartic strict-low endpoint residual together with the exact endpoint
normal form whose multiplicity is now bounded by one. -/
inductive FinalSeamQuarticEndpointMultiplicityData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | pureLongitudinal
      (C : Polynomial K)
      (hpattern : IsPureLongitudinalSmithPattern T.terminal.exponent)
      (C_ne_zero : C ≠ 0)
      (C_natDegree_le_one : C.natDegree ≤ 1)
      (normal : EndpointResidualNormalForm C)
      (multiplicity_le_one : normal.multiplicity ≤ 1)
  | lowNegativeFirst
      (B : Polynomial K)
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (B_ne_zero : B ≠ 0)
      (B_natDegree_le_one : B.natDegree ≤ 1)
      (normal : EndpointResidualNormalForm B)
      (multiplicity_le_one : normal.multiplicity ≤ 1)
  | lowNegativeSecond
      (B : Polynomial K)
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (B_ne_zero : B ≠ 0)
      (B_natDegree_le_one : B.natDegree ≤ 1)
      (normal : EndpointResidualNormalForm B)
      (multiplicity_le_one : normal.multiplicity ≤ 1)

/-- **Quartic multiplicity collapse.**

If the final seam has ordinary degree at most four, the endpoint residual
normal form in each strict-low branch has multiplicity zero or one. -/
theorem finalSeamQuarticEndpointMultiplicityData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4) :
    T.FinalSeamQuarticEndpointMultiplicityData := by
  let F := T.representedSpecialFiber
  have hres := T.finalSeamData.residualNormalForm
  cases hres with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      have haxisDegree :
          A.derivative.natDegree ≤ 3 := by
        have h :=
          T.representedAxisGradientComponent_natDegree_le_three
            hD (0 : Fin 4)
        rw [representedAxisGradientComponent,
          longitudinalAxisRestriction_pderiv_zero] at h
        rw [← hAeq] at h
        exact h
      have hfactorNe :
          Polynomial.X *
              (Polynomial.X - Polynomial.C (1 : K)) ≠ 0 :=
        mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)
      have hCdeg : C.natDegree ≤ 1 := by
        rw [hfactor,
          Polynomial.natDegree_mul hfactorNe hC,
          Polynomial.natDegree_mul
            (by simp : (Polynomial.X : Polynomial K) ≠ 0)
            (Polynomial.X_sub_C_ne_zero 1),
          Polynomial.natDegree_X,
          Polynomial.natDegree_X_sub_C] at haxisDegree
        omega
      let N := Classical.choice (exists_endpointResidualNormalForm C hC)
      have hm : N.multiplicity ≤ 1 := by
        have hdeq := N.degree_eq
        omega
      exact .pureLongitudinal C hpure hC hCdeg N hm

  | lowNegativeFirst A B hfirst hA hAeq hB hfactor hdegree =>
      have htrans :
          smithTransverseExponent
              T.terminal.exponent.b
              T.terminal.exponent.c
              T.terminal.exponent.d =
            Finsupp.single (1 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_one_of_lowNegativeFirst
          T.terminal.exponent hfirst
      have hAdeg : A.natDegree ≤ 3 := by
        have h :=
          T.representedAxisGradientComponent_natDegree_le_three
            hD (2 : Fin 4)
        rw [representedAxisGradientComponent,
          ← longitudinalCoefficient_single_eq_axisRestriction_pderiv
            (j := (1 : Fin 3))] at h
        have hAeq' :
            A =
              longitudinalCoefficientPolynomialAt
                (Finsupp.single (1 : Fin 3) 1) F := by
          rw [hAeq]
          unfold longitudinalCoefficientPolynomial
          rw [htrans]
        rw [← hAeq'] at h
        exact h
      have hBdeg : B.natDegree ≤ 1 := by
        omega
      let N := Classical.choice (exists_endpointResidualNormalForm B hB)
      have hm : N.multiplicity ≤ 1 := by
        have hdeq := N.degree_eq
        omega
      exact .lowNegativeFirst B hfirst hB hBdeg N hm

  | lowNegativeSecond A B hsecond hA hAeq hB hfactor hdegree =>
      have htrans :
          smithTransverseExponent
              T.terminal.exponent.b
              T.terminal.exponent.c
              T.terminal.exponent.d =
            Finsupp.single (0 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
          T.terminal.exponent hsecond
      have hAdeg : A.natDegree ≤ 3 := by
        have h :=
          T.representedAxisGradientComponent_natDegree_le_three
            hD (1 : Fin 4)
        rw [representedAxisGradientComponent,
          ← longitudinalCoefficient_single_eq_axisRestriction_pderiv
            (j := (0 : Fin 3))] at h
        have hAeq' :
            A =
              longitudinalCoefficientPolynomialAt
                (Finsupp.single (0 : Fin 3) 1) F := by
          rw [hAeq]
          unfold longitudinalCoefficientPolynomial
          rw [htrans]
        rw [← hAeq'] at h
        exact h
      have hBdeg : B.natDegree ≤ 1 := by
        omega
      let N := Classical.choice (exists_endpointResidualNormalForm B hB)
      have hm : N.multiplicity ≤ 1 := by
        have hdeq := N.degree_eq
        omega
      exact .lowNegativeSecond B hsecond hB hBdeg N hm

/-- There is no hidden higher endpoint multiplicity in the quartic case:
the normal-form multiplicity is literally zero or one. -/
theorem finalSeamQuartic_endpointMultiplicity_eq_zero_or_one
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4) :
    ∃ m : ℕ, (m = 0 ∨ m = 1) ∧
      match T.finalSeamQuarticEndpointMultiplicityData hD with
      | .pureLongitudinal _ _ _ _ N _ => m = N.multiplicity
      | .lowNegativeFirst _ _ _ _ N _ => m = N.multiplicity
      | .lowNegativeSecond _ _ _ _ N _ => m = N.multiplicity := by
  let Q := T.finalSeamQuarticEndpointMultiplicityData hD
  cases Q with
  | pureLongitudinal C hpure hC hCdeg N hm =>
      refine ⟨N.multiplicity, ?_, rfl⟩
      omega
  | lowNegativeFirst B hfirst hB hBdeg N hm =>
      refine ⟨N.multiplicity, ?_, rfl⟩
      omega
  | lowNegativeSecond B hsecond hB hBdeg N hm =>
      refine ⟨N.multiplicity, ?_, rfl⟩
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
