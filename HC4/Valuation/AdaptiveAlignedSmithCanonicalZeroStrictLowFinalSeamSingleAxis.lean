import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamLongitudinalConfinement
import Mathlib.Tactic

/-!
# G9: no one-axis nonlinear support at the final seam

G8 eliminates the case in which every nonlinear represented-source monomial is
confined to the distinguished longitudinal coordinate.  The strict-low
residual itself upgrades this to an arbitrary single-axis statement.

Suppose every represented monomial of ordinary degree at least three is
supported on one coordinate `r`.

* In the pure-longitudinal branch, the nonzero identity
  `A' = X (X - 1) C` produces an actual pure-`X₀` source monomial of
  degree at least three.  Hence `r = 0`, so G8 applies.
* In either low-negative branch, the nonzero coefficient polynomial
  `A = X (X - 1) B` has longitudinal degree at least two, while its strict-low
  transverse exponent is exactly one in coordinate `2` or `1`.
  Therefore the represented source contains an actual degree-at-least-three
  monomial using two distinct coordinates, contradicting one-axis support.

Thus every surviving zero-clock strict-low seam has genuinely multi-axis
nonlinear represented support.

No progress theorem, repair transition, source-complexity interpretation,
cocharacter, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- All represented nonlinear source support lies on one (a priori arbitrary)
source coordinate. -/
def RepresentedNonlinearSupportOnSingleAxis
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∃ r : Fin 4,
    ∀ d ∈ T.representedSpecialFiber.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d →
        ∀ i : Fin 4, i ≠ r → d i = 0

/-- **G9 single-axis contradiction.**

The exact strict-low residual witnesses rule out nonlinear confinement to any
single represented source coordinate. -/
theorem impossible_of_representedNonlinearSupportOnSingleAxis
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hsingle : T.RepresentedNonlinearSupportOnSingleAxis) :
    False := by
  rcases hsingle with ⟨r, haxis⟩
  have hres := T.zeroClockFirstContactPacket.2.2.1
  cases hres with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      let P := A.derivative
      have hP : P ≠ 0 := by
        dsimp [P]
        rw [hfactor]
        exact
          mul_ne_zero
            (mul_ne_zero
              (by simp)
              (Polynomial.X_sub_C_ne_zero (1 : K)))
            hC
      let n := P.natDegree
      have hn2 : 2 ≤ n := by
        dsimp [n, P]
        rw [hfactor,
          Polynomial.natDegree_mul
            (mul_ne_zero
              (by simp : (Polynomial.X : Polynomial K) ≠ 0)
              (Polynomial.X_sub_C_ne_zero (1 : K)))
            hC,
          Polynomial.natDegree_mul
            (by simp : (Polynomial.X : Polynomial K) ≠ 0)
            (Polynomial.X_sub_C_ne_zero (1 : K)),
          Polynomial.natDegree_X,
          Polynomial.natDegree_X_sub_C]
        omega
      have hPcoeff : P.coeff n ≠ 0 := by
        exact Polynomial.leadingCoeff_ne_zero.mpr hP
      have hAcoeff : A.coeff (n + 1) ≠ 0 := by
        intro hz
        apply hPcoeff
        dsimp [P]
        rw [Polynomial.coeff_derivative, hz]
        simp
      let d : Fin 4 →₀ ℕ := (0 : Fin 3 →₀ ℕ).cons (n + 1)
      have hsource :
          MvPolynomial.coeff d T.representedSpecialFiber ≠ 0 := by
        dsimp [d]
        rw [← coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
        rw [← longitudinalAxisRestriction_eq_coefficient_zero]
        rw [← hAeq]
        exact hAcoeff
      have hd : d ∈ T.representedSpecialFiber.support :=
        MvPolynomial.mem_support_iff.mpr hsource
      have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
        dsimp [d]
        simp [HC4.Polynomial.ordinaryDegree4]
        omega
      have hd0 : d (0 : Fin 4) = n + 1 := by
        simp [d]
      have hr0 : r = 0 := by
        by_contra hr
        have hz := haxis d hd hdeg (0 : Fin 4) (Ne.symm hr)
        omega
      have hlong : T.RepresentedNonlinearSupportLongitudinal := by
        intro d' hd' hdeg'
        have h := haxis d' hd' hdeg'
        constructor
        · exact h (1 : Fin 4) (by simpa [hr0])
        constructor
        · exact h (2 : Fin 4) (by simpa [hr0])
        · exact h (3 : Fin 4) (by simpa [hr0])
      exact T.impossible_of_representedNonlinearSupportLongitudinal hlong

  | lowNegativeFirst A B hfirst hA hAeq hB hfactor hdegree =>
      let n := A.natDegree
      have hn2 : 2 ≤ n := by
        dsimp [n]
        omega
      have hcoeff : A.coeff n ≠ 0 := by
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      let e := T.terminal.exponent
      let d : Fin 4 →₀ ℕ :=
        (smithTransverseExponent e.b e.c e.d).cons n
      have hsource :
          MvPolynomial.coeff d T.representedSpecialFiber ≠ 0 := by
        dsimp [d, e]
        rw [← coeff_longitudinalCoefficientPolynomial]
        rw [← hAeq]
        exact hcoeff
      have hd : d ∈ T.representedSpecialFiber.support :=
        MvPolynomial.mem_support_iff.mpr hsource
      have htrans :
          smithTransverseExponent e.b e.c e.d =
            Finsupp.single (1 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_one_of_lowNegativeFirst e hfirst
      have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
        dsimp [d]
        rw [htrans]
        simp [HC4.Polynomial.ordinaryDegree4]
        omega
      have hd0 : d (0 : Fin 4) = n := by
        simp [d]
      have hd2 : d (2 : Fin 4) = 1 := by
        dsimp [d]
        rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
          Finsupp.cons_succ, htrans]
        simp
      have hr0 : r = 0 := by
        by_contra hr
        have hz := haxis d hd hdeg (0 : Fin 4) (Ne.symm hr)
        omega
      have hz2 := haxis d hd hdeg (2 : Fin 4) (by simpa [hr0])
      omega

  | lowNegativeSecond A B hsecond hA hAeq hB hfactor hdegree =>
      let n := A.natDegree
      have hn2 : 2 ≤ n := by
        dsimp [n]
        omega
      have hcoeff : A.coeff n ≠ 0 := by
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      let e := T.terminal.exponent
      let d : Fin 4 →₀ ℕ :=
        (smithTransverseExponent e.b e.c e.d).cons n
      have hsource :
          MvPolynomial.coeff d T.representedSpecialFiber ≠ 0 := by
        dsimp [d, e]
        rw [← coeff_longitudinalCoefficientPolynomial]
        rw [← hAeq]
        exact hcoeff
      have hd : d ∈ T.representedSpecialFiber.support :=
        MvPolynomial.mem_support_iff.mpr hsource
      have htrans :
          smithTransverseExponent e.b e.c e.d =
            Finsupp.single (0 : Fin 3) 1 :=
        smithTransverseExponent_eq_single_zero_of_lowNegativeSecond e hsecond
      have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
        dsimp [d]
        rw [htrans]
        simp [HC4.Polynomial.ordinaryDegree4]
        omega
      have hd0 : d (0 : Fin 4) = n := by
        simp [d]
      have hd1 : d (1 : Fin 4) = 1 := by
        dsimp [d]
        rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
          Finsupp.cons_succ, htrans]
        simp
      have hr0 : r = 0 := by
        by_contra hr
        have hz := haxis d hd hdeg (0 : Fin 4) (Ne.symm hr)
        omega
      have hz1 := haxis d hd hdeg (1 : Fin 4) (by simpa [hr0])
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
