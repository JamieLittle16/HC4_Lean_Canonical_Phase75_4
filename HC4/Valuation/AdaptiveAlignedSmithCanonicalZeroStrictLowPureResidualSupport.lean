import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowResidualSupport
import Mathlib.Tactic

/-!
# A19.63: the pure-longitudinal residual gives actual nonlinear axis support

For the remaining pure strict-low pattern A19.49 gives

  A' = X (X - 1) C,   C != 0.

The derivative therefore has degree at least two.  Its leading coefficient is
nonzero, and `coeff_derivative` lifts that coefficient to a nonzero coefficient
of `A` one longitudinal degree higher.  Since `A` is exactly the distinguished
axis restriction, the mixed-degree reconstruction lemmas turn that coefficient
into an actual source monomial.

Thus the represented source contains a nonlinear monomial supported only on
coordinate `0`, with longitudinal degree at least three.  This is source-level
finite-support information; no homogeneity, balance, or terminal cocharacter is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

/-- A pure-longitudinal residual contains an actual nonlinear source monomial
supported only on the distinguished longitudinal coordinate. -/
theorem pureLongitudinal_sourceSupport
    {F : MvPolynomial (Fin 4) K} {e : SmithSupportExponent}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm F e)
    (hpat : IsPureLongitudinalSmithPattern e) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      d (1 : Fin 4) = 0 ∧
      d (2 : Fin 4) = 0 ∧
      d (3 : Fin 4) = 0 := by
  cases R with
  | pureLongitudinal A C hpure hA hAeq hC hfactor hdegree =>
      have hder : A.derivative ≠ 0 := by
        rw [hfactor]
        exact
          mul_ne_zero
            (mul_ne_zero
              (by simp)
              (Polynomial.X_sub_C_ne_zero 1))
            hC
      let m := A.derivative.natDegree
      have hm : 2 ≤ m := by
        dsimp [m]
        rw [hfactor,
          Polynomial.natDegree_mul
            (mul_ne_zero
              (by simp : (Polynomial.X : Polynomial K) ≠ 0)
              (Polynomial.X_sub_C_ne_zero 1)) hC,
          Polynomial.natDegree_mul
            (by simp : (Polynomial.X : Polynomial K) ≠ 0)
            (Polynomial.X_sub_C_ne_zero 1),
          Polynomial.natDegree_X,
          Polynomial.natDegree_X_sub_C]
        omega
      let n := m + 1
      have hcoeff : A.coeff n ≠ 0 := by
        have hlead : A.derivative.coeff m ≠ 0 := by
          dsimp [m]
          exact Polynomial.leadingCoeff_ne_zero.mpr hder
        intro hz
        apply hlead
        dsimp [n]
        rw [Polynomial.coeff_derivative, hz]
        simp
      have htransverse :=
        smithTransverseExponent_eq_zero_of_pureLongitudinal e hpure
      have haxis :
          longitudinalCoefficientPolynomial e.b e.c e.d F =
            longitudinalAxisRestriction F := by
        rw [longitudinalAxisRestriction_eq_coefficient_zero]
        simp [longitudinalCoefficientPolynomial, htransverse]
      have hAcoeff :
          A = longitudinalCoefficientPolynomial e.b e.c e.d F :=
        hAeq.trans haxis.symm
      let d : Fin 4 →₀ ℕ :=
        (smithTransverseExponent e.b e.c e.d).cons n
      have hsourceCoeff : MvPolynomial.coeff d F ≠ 0 := by
        rw [← coeff_longitudinalCoefficientPolynomial
          e.b e.c e.d F n]
        rw [← hAcoeff]
        exact hcoeff
      have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hsourceCoeff
      refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_⟩
      · rcases hpure with ⟨hb, hc, hdpat⟩
        have hdegD :
            HC4.Polynomial.ordinaryDegree4 d = n + e.b + e.c + e.d := by
          simpa [d] using
            (ordinaryDegree4_cons_smithTransverseExponent_eq e n)
        rw [hdegD, hb, hc, hdpat]
        dsimp [n]
        omega
      · change 0 < n
        dsimp [n]
        omega
      · rcases hpure with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).1.trans hb
      · rcases hpure with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.1.trans hc
      · rcases hpure with ⟨hb, hc, hdpat⟩
        change
          ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = 0
        exact (cons_smithTransverseExponent_has_projection e n).2.2.trans hdpat
  | lowNegativeFirst A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hc1 : e.c = 1 := hp.2.1
      have hc0 : e.c = 0 := hpat.2.1
      omega
  | lowNegativeSecond A B hp hA hAeq hB hfactor hdegree =>
      exfalso
      have hb1 : e.b = 1 := hp.1
      have hb0 : e.b = 0 := hpat.1
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Dispatcher-facing pure-longitudinal nonlinear source witness. -/
theorem pureLongitudinal_sourceSupport
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hpat : IsPureLongitudinalSmithPattern T.terminal.exponent) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      d (1 : Fin 4) = 0 ∧
      d (2 : Fin 4) = 0 ∧
      d (3 : Fin 4) = 0 :=
  T.zeroClockFirstContactPacket.2.2.1.pureLongitudinal_sourceSupport hpat

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
