import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.87: every strict-low residual already contains codimension-two source support

The exact `X (X - 1)` residual normal forms are more rigid than the coarse
nonlinear support witnesses recorded in A19.61/A19.63.  In each of the three
strict-low Smith patterns their leading source monomial has longitudinal
exponent at least two and at least two transverse coordinates equal to zero:

* pure longitudinal: `(n,0,0,0)`;
* low-negative-first: `(n,0,1,0)`;
* low-negative-second: `(n,1,0,0)`.

Thus every zero-strict-low singular terminal already carries an actual
nonlinear represented-source exponent on a codimension-two coordinate
boundary.  This is still only source support: no planar/two-zero terminal is
inferred without the additional homogeneous carrier required by the doubling
machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

/-- The low-negative-first residual has an actual source monomial of shape
`(n,0,1,0)` with `n >= 2`. -/
theorem lowNegativeFirst_sourceSupport_codimensionTwo
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeFirstSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
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
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have hsourceCoeff : MvPolynomial.coeff d F ≠ 0 := by
        rw [← coeff_longitudinalCoefficientPolynomial
          e.b e.c e.d F n]
        rw [← hAeq]
        exact hlead
      have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hsourceCoeff
      rcases hp with ⟨hb, hc, hdpat⟩
      have hdegD :
          HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
        simpa [d] using
          (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
      have hd1 : d (1 : Fin 4) = 0 := by
        change ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).1.trans hb
      have hd3 : d (3 : Fin 4) = 0 := by
        change ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.2.trans hdpat
      refine ⟨d, hd, ?_, ?_, ?_⟩
      · rw [hdegD, hb, hc, hdpat]
        omega
      · change 2 ≤ n
        exact hn
      · exact ⟨(1 : Fin 4), (3 : Fin 4), by decide, hd1, hd3⟩
  | lowNegativeSecond A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hb0 : e.b = 0 := hpat.1
      have hb1 : e.b = 1 := hp.1
      omega

/-- The low-negative-second residual has an actual source monomial of shape
`(n,1,0,0)` with `n >= 2`. -/
theorem lowNegativeSecond_sourceSupport_codimensionTwo
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeSecondSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
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
        exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have hsourceCoeff : MvPolynomial.coeff d F ≠ 0 := by
        rw [← coeff_longitudinalCoefficientPolynomial
          e.b e.c e.d F n]
        rw [← hAeq]
        exact hlead
      have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hsourceCoeff
      rcases hp with ⟨hb, hc, hdpat⟩
      have hdegD :
          HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
        simpa [d] using
          (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
      have hd2 : d (2 : Fin 4) = 0 := by
        change ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.1.trans hc
      have hd3 : d (3 : Fin 4) = 0 := by
        change ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.2.trans hdpat
      refine ⟨d, hd, ?_, ?_, ?_⟩
      · rw [hdegD, hb, hc, hdpat]
        omega
      · change 2 ≤ n
        exact hn
      · exact ⟨(2 : Fin 4), (3 : Fin 4), by decide, hd2, hd3⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.87 strict-low source compression.**  Every retained strict-low
terminal carries an actual nonlinear represented-source exponent with
longitudinal multiplicity at least two and two distinct zero coordinates. -/
theorem strictLow_sourceSupport_codimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · rcases T.pureLongitudinal_sourceSupport hpure with
      ⟨d, hd, hdeg, hd0, hd1, hd2, hd3⟩
    have htwo : 2 ≤ d (0 : Fin 4) := by
      simp [HC4.Polynomial.ordinaryDegree4, hd1, hd2, hd3] at hdeg
      omega
    exact ⟨d, hd, hdeg, htwo,
      ⟨(1 : Fin 4), (2 : Fin 4), by decide, hd1, hd2⟩⟩
  · exact T.zeroClockFirstContactPacket.2.2.1
      |>.lowNegativeFirst_sourceSupport_codimensionTwo hfirst
  · exact T.zeroClockFirstContactPacket.2.2.1
      |>.lowNegativeSecond_sourceSupport_codimensionTwo hsecond

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
