import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamRightRecentered
import Mathlib.Tactic

/-!
# G2: exact strict-low Hessian signature at the final seam

G1 puts the final local problem on the honest right-recentered determinant-one
fibre.  The retained first longitudinal departure still lies over the exact
strict-low Smith exponent.  Consequently its transverse coordinates are no
longer arbitrary:

* pure longitudinal: all three transverse coordinates are zero;
* low-negative-first: only source coordinate 2 occurs, with exponent one;
* low-negative-second: only source coordinate 1 occurs, with exponent one.

Combining one actual later support monomial with the zero linear source jet
therefore collapses the generic first-contact Hessian alternative to five
literal signatures.  In the pure case the later support cannot be linear, so
the longitudinal diagonal Hessian entry is nonzero.  In either low-negative
case the longitudinal exponent is either at least two, giving the same
diagonal entry, or exactly one, giving the unique possible mixed entry.

This is finite characteristic-zero coefficient algebra only.  No progress,
repair relabelling, homogeneity, cocharacter, or JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Pattern-specific Hessian signatures left by the exact strict-low first
departure on the right-recentered determinant-one fibre. -/
inductive FinalSeamStrictLowHessianSignature
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | pureLongitudinal
      (hpattern : IsPureLongitudinalSmithPattern T.terminal.exponent)
      (hne :
        MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            T.rightRecenteredSpecialFiber) ≠ 0)
  | lowNegativeFirstDiagonal
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (hne :
        MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            T.rightRecenteredSpecialFiber) ≠ 0)
  | lowNegativeFirstMixed
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (hne :
        MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            T.rightRecenteredSpecialFiber) ≠ 0)
  | lowNegativeSecondDiagonal
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (hne :
        MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            T.rightRecenteredSpecialFiber) ≠ 0)
  | lowNegativeSecondMixed
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (hne :
        MvPolynomial.pderiv (1 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            T.rightRecenteredSpecialFiber) ≠ 0)

/-- **G2 exact first-contact signature.**

The proof reconstructs one actual later support monomial from the retained
first-departure certificate, so its transverse coordinates remain tied to the
actual strict-low exponent. -/
theorem finalSeamStrictLowHessianSignature
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalSeamStrictLowHessianSignature := by
  let R := T.finalSeamRightRecenteredData
  let e := T.terminal.exponent
  let G := T.rightRecenteredSpecialFiber
  rcases R.firstDeparture.support_pair with ⟨n, q, hq, _hn, hnq⟩
  let d : Fin 4 →₀ ℕ :=
    (smithTransverseExponent e.b e.c e.d).cons (n + q)
  have hd : d ∈ G.support := by
    simpa [d, G, e] using hnq
  have hd0 : 0 < d (0 : Fin 4) := by
    change 0 < n + q
    omega
  have hcoords :=
    smithSupportExponentOf_cons_smithTransverseExponent e (n + q)

  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · have hd1 : d (1 : Fin 4) = 0 := by
      change
        ((smithTransverseExponent e.b e.c e.d).cons (n + q))
          (1 : Fin 4) = 0
      exact hcoords.1.trans hpure.1
    have hd2 : d (2 : Fin 4) = 0 := by
      change
        ((smithTransverseExponent e.b e.c e.d).cons (n + q))
          (2 : Fin 4) = 0
      exact hcoords.2.1.trans hpure.2.1
    have hd3 : d (3 : Fin 4) = 0 := by
      change
        ((smithTransverseExponent e.b e.c e.d).cons (n + q))
          (3 : Fin 4) = 0
      exact hcoords.2.2.trans hpure.2.2
    have hd0two : 2 ≤ d (0 : Fin 4) := by
      by_contra hnot
      have hd0one : d (0 : Fin 4) = 1 := by omega
      have hdsingle : d = Finsupp.single (0 : Fin 4) 1 := by
        ext i
        fin_cases i <;>
          simp [hd0one, hd1, hd2, hd3, Finsupp.single_apply]
      have hcoeff : MvPolynomial.coeff d G ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hd
      rw [hdsingle] at hcoeff
      exact (hcoeff (R.linearCoeff_zero (0 : Fin 4))).elim
    exact .pureLongitudinal hpure
      (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (K := K) (0 : Fin 4) G d hd hd0two)

  · have hd2eq : d (2 : Fin 4) = 1 := by
      change
        ((smithTransverseExponent e.b e.c e.d).cons (n + q))
          (2 : Fin 4) = 1
      exact hcoords.2.1.trans hfirst.2.1
    by_cases hd0one : d (0 : Fin 4) = 1
    · have hd2pos : 0 < d (2 : Fin 4) := by omega
      exact .lowNegativeFirstMixed hfirst
        (pderiv_pderiv_ne_zero_of_support_exponents_pos
          (K := K) (0 : Fin 4) (2 : Fin 4) (by decide)
          G d hd hd0 hd2pos)
    · have hd0two : 2 ≤ d (0 : Fin 4) := by omega
      exact .lowNegativeFirstDiagonal hfirst
        (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
          (K := K) (0 : Fin 4) G d hd hd0two)

  · have hd1eq : d (1 : Fin 4) = 1 := by
      change
        ((smithTransverseExponent e.b e.c e.d).cons (n + q))
          (1 : Fin 4) = 1
      exact hcoords.1.trans hsecond.1
    by_cases hd0one : d (0 : Fin 4) = 1
    · have hd1pos : 0 < d (1 : Fin 4) := by omega
      exact .lowNegativeSecondMixed hsecond
        (pderiv_pderiv_ne_zero_of_support_exponents_pos
          (K := K) (0 : Fin 4) (1 : Fin 4) (by decide)
          G d hd hd0 hd1pos)
    · have hd0two : 2 ≤ d (0 : Fin 4) := by omega
      exact .lowNegativeSecondDiagonal hsecond
        (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
          (K := K) (0 : Fin 4) G d hd hd0two)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
