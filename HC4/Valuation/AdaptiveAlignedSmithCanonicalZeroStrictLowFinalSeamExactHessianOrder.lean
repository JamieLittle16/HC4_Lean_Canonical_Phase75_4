import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamFirstContactSignature
import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHomogeneousRigidity
import Mathlib.Tactic

/-!
# G3: exact longitudinal order of the strict-low Hessian entry

Each concrete strict-low residual has the two-endpoint factor X (X - 1) R,
or in the pure-longitudinal case this factor for the axis derivative.
The existing finite endpoint recursion writes R as (X - 1)^m times a
terminal residual which is nonzero at 1.  After moving the right endpoint to
the origin, the relevant coefficient fibre therefore has exact initial order
m + 1.  Differentiating once gives an exact Hessian-axis order m.

Thus pure longitudinal gives exact order m for H_00, low-negative-first gives
exact order m for H_02, and low-negative-second gives exact order m for H_01.

No positive determinant clock, repair progress, homogeneity, cocharacter, or
JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

def HasExactPolynomialInitialOrder
    (P : Polynomial K) (n : ℕ) : Prop :=
  (∀ k < n, P.coeff k = 0) ∧ P.coeff n ≠ 0

namespace HasExactPolynomialInitialOrder

theorem derivative_of_succ
    {P : Polynomial K} {n : ℕ}
    (h : HasExactPolynomialInitialOrder P (n + 1)) :
    HasExactPolynomialInitialOrder P.derivative n := by
  constructor
  · intro k hk
    rw [Polynomial.coeff_derivative]
    have hk' : k + 1 < n + 1 := by omega
    rw [h.1 (k + 1) hk']
    simp
  · rw [Polynomial.coeff_derivative]
    exact mul_ne_zero h.2 (by
      exact_mod_cast Nat.succ_ne_zero n)

end HasExactPolynomialInitialOrder

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

inductive FinalSeamExactHessianAxisOrder
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | pureLongitudinal
      (m : ℕ)
      (hpattern : IsPureLongitudinalSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
              (0 : Fin 4) (0 : Fin 4))) m)
  | lowNegativeFirst
      (m : ℕ)
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
              (0 : Fin 4) (2 : Fin 4))) m)
  | lowNegativeSecond
      (m : ℕ)
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
              (0 : Fin 4) (1 : Fin 4))) m)

theorem finalSeamExactHessianAxisOrder
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalSeamExactHessianAxisOrder := by
  let F := T.representedSpecialFiber
  let G := T.rightRecenteredSpecialFiber
  let e := T.terminal.exponent
  have hres := T.zeroClockFirstContactPacket.2.2.1
  cases hres with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      let N := Classical.choice (exists_endpointResidualNormalForm C hC)
      let Q := longitudinalAxisRestriction G
      have hQ :
          Q = Polynomial.taylor 1 A := by
        dsimp [Q, G, F, rightRecenteredSpecialFiber, representedSpecialFiber]
        rw [longitudinalAxisRestriction_longitudinalRightRecenterHom]
        rw [← hAeq]
      have hQder :
          Q.derivative =
            Polynomial.taylor 1
              (Polynomial.X * (Polynomial.X - Polynomial.C 1) * C) := by
        rw [hQ, derivative_taylor_one, hfactor]
      have hlayer := N.exactRecenteredLayer
      have hfirst :
          HasExactPolynomialInitialOrder
            Q.derivative (N.multiplicity + 1) := by
        constructor
        · intro k hk
          rw [hQder]
          exact hlayer.1 k hk
        · rw [hQder]
          exact hlayer.2.2
      have hsecond :
          HasExactPolynomialInitialOrder
            Q.derivative.derivative N.multiplicity :=
        hfirst.derivative_of_succ
      have haxis :
          longitudinalAxisRestriction
              (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) =
            Q.derivative.derivative := by
        dsimp [Q]
        rw [longitudinalAxisRestriction_pderiv_zero,
          longitudinalAxisRestriction_pderiv_zero]
      exact .pureLongitudinal N.multiplicity hpure (by
        rw [haxis]
        exact hsecond)

  | lowNegativeFirst A B hfirst hA hAeq hB hfactor hdegree =>
      let N := Classical.choice (exists_endpointResidualNormalForm B hB)
      let Q :=
        longitudinalCoefficientPolynomial
          e.b e.c e.d G
      have hQ :
          Q =
            Polynomial.taylor 1
              (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B) := by
        dsimp [Q, G, F, rightRecenteredSpecialFiber, representedSpecialFiber]
        rw [longitudinalCoefficientPolynomial_longitudinalRightRecenterHom]
        rw [← hAeq, hfactor]
      have hlayer := N.exactRecenteredLayer
      have hQorder :
          HasExactPolynomialInitialOrder Q (N.multiplicity + 1) := by
        constructor
        · intro k hk
          rw [hQ]
          exact hlayer.1 k hk
        · rw [hQ]
          exact hlayer.2.2
      have hQder :
          HasExactPolynomialInitialOrder Q.derivative N.multiplicity :=
        hQorder.derivative_of_succ
      have htrans :
          smithTransverseExponent e.b e.c e.d =
            Finsupp.single (1 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_one_of_lowNegativeFirst e hfirst
      have hQsingle :
          longitudinalCoefficientPolynomialAt
              (Finsupp.single (1 : Fin 3) 1) G = Q := by
        dsimp [Q, longitudinalCoefficientPolynomial]
        rw [htrans]
      have haxis :
          longitudinalAxisRestriction
              (HC4.Polynomial.hessian G (0 : Fin 4) (2 : Fin 4)) =
            Q.derivative := by
        have hh :=
          longitudinalAxisRestriction_hessian_zero_succ
            (K := K) (1 : Fin 3) G
        simpa [hQsingle] using hh
      exact .lowNegativeFirst N.multiplicity hfirst (by
        rw [haxis]
        exact hQder)

  | lowNegativeSecond A B hsecond hA hAeq hB hfactor hdegree =>
      let N := Classical.choice (exists_endpointResidualNormalForm B hB)
      let Q :=
        longitudinalCoefficientPolynomial
          e.b e.c e.d G
      have hQ :
          Q =
            Polynomial.taylor 1
              (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B) := by
        dsimp [Q, G, F, rightRecenteredSpecialFiber, representedSpecialFiber]
        rw [longitudinalCoefficientPolynomial_longitudinalRightRecenterHom]
        rw [← hAeq, hfactor]
      have hlayer := N.exactRecenteredLayer
      have hQorder :
          HasExactPolynomialInitialOrder Q (N.multiplicity + 1) := by
        constructor
        · intro k hk
          rw [hQ]
          exact hlayer.1 k hk
        · rw [hQ]
          exact hlayer.2.2
      have hQder :
          HasExactPolynomialInitialOrder Q.derivative N.multiplicity :=
        hQorder.derivative_of_succ
      have htrans :
          smithTransverseExponent e.b e.c e.d =
            Finsupp.single (0 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_zero_of_lowNegativeSecond e hsecond
      have hQsingle :
          longitudinalCoefficientPolynomialAt
              (Finsupp.single (0 : Fin 3) 1) G = Q := by
        dsimp [Q, longitudinalCoefficientPolynomial]
        rw [htrans]
      have haxis :
          longitudinalAxisRestriction
              (HC4.Polynomial.hessian G (0 : Fin 4) (1 : Fin 4)) =
            Q.derivative := by
        have hh :=
          longitudinalAxisRestriction_hessian_zero_succ
            (K := K) (0 : Fin 3) G
        simpa [hQsingle] using hh
      exact .lowNegativeSecond N.multiplicity hsecond (by
        rw [haxis]
        exact hQder)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
