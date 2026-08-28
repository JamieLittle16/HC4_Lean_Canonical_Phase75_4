import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeSourceSplit
import Mathlib.Tactic

/-!
# A19.61: strict-low residual factors give actual nonlinear source support

The A19.49 low-negative residuals are not merely pattern labels.  Their fixed
transverse coefficient polynomial has the exact factorisation

  A = X (X - 1) B,   B != 0.

Hence `natDegree A >= 2`, and the leading coefficient of `A` reconstructs an
actual supported four-variable monomial.  In the low-negative-first pattern
that monomial has transverse coordinate `2` equal to one; in the
low-negative-second pattern it has coordinate `1` equal to one.  Together
with longitudinal degree at least two, both witnesses are genuinely nonlinear.

These are source-support facts on the unrecentered represented special fibre.
No torus balance, first-contact grading, or top-face membership is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

/-- A low-negative-first residual contains an actual nonlinear source monomial
with positive longitudinal coordinate and source coordinate `2` equal to one. -/
theorem lowNegativeFirst_sourceSupport
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeFirstSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      d (2 : Fin 4) = 1 := by
  cases R with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      exfalso
      have hc0 : e.c = 0 := hpure.2.1
      have hc1 : e.c = 1 := hpat.2.1
      omega
  | lowNegativeFirst A B hp hA hAeq hB hfactor hdegree =>
      let n := A.natDegree
      let d : Fin 4 →₀ ℕ :=
        (smithTransverseExponent e.b e.c e.d).cons n
      have hn : 2 ≤ n := by
        dsimp [n]
        omega
      have hlead : A.coeff n ≠ 0 := by
        dsimp [n]
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have hsourceCoeff : MvPolynomial.coeff d F ≠ 0 := by
        rw [← coeff_longitudinalCoefficientPolynomial
          e.b e.c e.d F n]
        rw [← hAeq]
        exact hlead
      have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hsourceCoeff
      refine ⟨d, hd, ?_, ?_, ?_⟩
      · rcases hp with ⟨hb, hc, hdpat⟩
        have hdegD :
            HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
          simpa [d] using
            (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
        rw [hdegD, hb, hc, hdpat]
        omega
      · change 0 < n
        omega
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = 1
        exact (cons_smithTransverseExponent_has_projection e n).2.1.trans hc
  | lowNegativeSecond A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hb0 : e.b = 0 := hpat.1
      have hb1 : e.b = 1 := hp.1
      omega

/-- A low-negative-second residual contains an actual nonlinear source monomial
with positive longitudinal coordinate and source coordinate `1` equal to one. -/
theorem lowNegativeSecond_sourceSupport
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeSecondSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      d (1 : Fin 4) = 1 := by
  cases R with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      exfalso
      have hb0 : e.b = 0 := hpure.1
      have hb1 : e.b = 1 := hpat.1
      omega
  | lowNegativeFirst A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hb0 : e.b = 0 := hp.1
      have hb1 : e.b = 1 := hpat.1
      omega
  | lowNegativeSecond A B hp hA hAeq hB hfactor hdegree =>
      let n := A.natDegree
      let d : Fin 4 →₀ ℕ :=
        (smithTransverseExponent e.b e.c e.d).cons n
      have hn : 2 ≤ n := by
        dsimp [n]
        omega
      have hlead : A.coeff n ≠ 0 := by
        dsimp [n]
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have hsourceCoeff : MvPolynomial.coeff d F ≠ 0 := by
        rw [← coeff_longitudinalCoefficientPolynomial
          e.b e.c e.d F n]
        rw [← hAeq]
        exact hlead
      have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hsourceCoeff
      refine ⟨d, hd, ?_, ?_, ?_⟩
      · rcases hp with ⟨hb, hc, hdpat⟩
        have hdegD :
            HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
          simpa [d] using
            (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
        rw [hdegD, hb, hc, hdpat]
        omega
      · change 0 < n
        omega
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = 1
        exact (cons_smithTransverseExponent_has_projection e n).1.trans hb

end AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The retained low-negative-first terminal itself exposes the source witness
without unpacking A19.49 manually. -/
theorem lowNegativeFirst_sourceSupport
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hpat : IsLowNegativeFirstSmithPattern T.terminal.exponent) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧ d (2 : Fin 4) = 1 :=
  T.zeroClockFirstContactPacket.2.2.1.lowNegativeFirst_sourceSupport hpat

/-- Symmetric low-negative-second source witness. -/
theorem lowNegativeSecond_sourceSupport
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hpat : IsLowNegativeSecondSmithPattern T.terminal.exponent) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧ d (1 : Fin 4) = 1 :=
  T.zeroClockFirstContactPacket.2.2.1.lowNegativeSecond_sourceSupport hpat

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
