import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.87: every strict-low residual already contains codimension-two source support

The three strict-low Smith patterns are much sparser than the later boundary
construction needs:

* pure longitudinal has transverse exponent `(0,0,0)`;
* low-negative-first has transverse exponent `(0,1,0)`;
* low-negative-second has transverse exponent `(1,0,0)`.

A19.61/A19.63 reconstruct actual nonlinear source monomials from the exact
`X (X - 1)` residual factors.  Retaining the two zero transverse coordinates
in that reconstruction shows that every zero-clock strict-low terminal already
contains an actual nonlinear codimension-two source exponent.

This is a source-support theorem only.  It deliberately does not identify one
codimension-two monomial with the full weighted-homogeneous two-zero terminal
required by the planar/doubling machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

/-- The low-negative-first residual reconstructs a source monomial of the
literal sparse shape `(n,0,1,0)`, with `n ≥ 2`. -/
theorem lowNegativeFirst_sourceSupport_sparse
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeFirstSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      d (1 : Fin 4) = 0 ∧
      d (2 : Fin 4) = 1 ∧
      d (3 : Fin 4) = 0 := by
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
      refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hp with ⟨hb, hc, hdpat⟩
        have hdegD :
            HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
          simpa [d] using
            (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
        rw [hdegD, hb, hc, hdpat]
        omega
      · change 2 ≤ n
        exact hn
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).1.trans hb
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = 1
        exact (cons_smithTransverseExponent_has_projection e n).2.1.trans hc
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.2.trans hdpat
  | lowNegativeSecond A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hb0 : e.b = 0 := hpat.1
      have hb1 : e.b = 1 := hp.1
      omega

/-- The low-negative-second residual reconstructs the cyclic sparse source
monomial `(n,1,0,0)`, again with `n ≥ 2`. -/
theorem lowNegativeSecond_sourceSupport_sparse
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsLowNegativeSecondSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      d (1 : Fin 4) = 1 ∧
      d (2 : Fin 4) = 0 ∧
      d (3 : Fin 4) = 0 := by
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
      refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hp with ⟨hb, hc, hdpat⟩
        have hdegD :
            HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
          simpa [d] using
            (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
        rw [hdegD, hb, hc, hdpat]
        omega
      · change 2 ≤ n
        exact hn
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = 1
        exact (cons_smithTransverseExponent_has_projection e n).1.trans hb
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.1.trans hc
      · rcases hp with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.2.trans hdpat

end AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.87 strict-low codimension-two source theorem.**  Every actual
producer-free zero-clock strict-low terminal already contains a nonlinear
source monomial on two coordinate boundaries. -/
theorem strictLow_sourceCodimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
  let R := T.zeroClockFirstContactPacket.2.2.1
  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · rcases T.pureLongitudinal_sourceSupport hpure with
      ⟨d, hd, hdeg, hd0, h1, h2, h3⟩
    refine ⟨d, hd, hdeg, hd0, ?_⟩
    exact ⟨(1 : Fin 4), (2 : Fin 4), by decide, h1, h2⟩
  · rcases R.lowNegativeFirst_sourceSupport_sparse hfirst with
      ⟨d, hd, hdeg, hd0, h1, h2, h3⟩
    refine ⟨d, hd, hdeg, by omega, ?_⟩
    exact ⟨(1 : Fin 4), (3 : Fin 4), by decide, h1, h3⟩
  · rcases R.lowNegativeSecond_sourceSupport_sparse hsecond with
      ⟨d, hd, hdeg, hd0, h1, h2, h3⟩
    refine ⟨d, hd, hdeg, by omega, ?_⟩
    exact ⟨(2 : Fin 4), (3 : Fin 4), by decide, h2, h3⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
