import HC4.Valuation.CoordinateMaxKernelOpeningLinearPowerAxis
import Mathlib.Tactic

/-!
# Pure-axis rigidity for the degenerate coordinate-max child

The previous stage proves that the linear form `L` of a low-rank first-opening
child genuinely uses the extraction coordinate and omits the newly appearing
kernel coordinate.

There is in fact no room for any second coordinate in `L`.  Every monomial of
the exact coordinate-max child has one fixed extraction exponent.  Therefore

* the extraction partial of the child is supported at extraction exponent
  `level - 1`;
* any different coordinate partial is supported at extraction exponent
  `level`.

For a power `a * L^m`, two nonzero coefficients of `L` make those two partials
nonzero scalar multiples of the same `L^(m-1)`, hence they have the same
support.  The two support degrees are incompatible.  Thus every coefficient
other than the extraction coefficient is zero.

This identifies the entire degenerate child as a pure coordinate-axis power at
the level of its linear-form coefficients, still without introducing repair
or comparing any auxiliary clock to the zero blocker.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

/-- A monomial occurring in the extraction-coordinate partial lies exactly
one extraction unit below the child level. -/
theorem pderiv_extraction_support_coordinate
    {q : Fin 4 →₀ ℕ}
    (hq : q ∈
      (MvPolynomial.pderiv D.extractionCoordinate D.child).support) :
    q D.extractionCoordinate + 1 = D.extractionLevel := by
  have hqcoeff :
      MvPolynomial.coeff q
        (MvPolynomial.pderiv D.extractionCoordinate D.child) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hq
  rw [coeff_pderiv_backport] at hqcoeff
  have hsourceCoeff :
      MvPolynomial.coeff
        (q + Finsupp.single D.extractionCoordinate 1) D.child ≠ 0 := by
    intro hz
    simp [hz] at hqcoeff
  have hmem :
      q + Finsupp.single D.extractionCoordinate 1 ∈ D.child.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hcoord := D.child_extractionCoordinate_eq hmem
  simpa [Finsupp.single_apply] using hcoord

/-- A different coordinate partial preserves the exact extraction level. -/
theorem pderiv_other_support_extraction_coordinate
    (j : Fin 4)
    (hje : j ≠ D.extractionCoordinate)
    {q : Fin 4 →₀ ℕ}
    (hq : q ∈ (MvPolynomial.pderiv j D.child).support) :
    q D.extractionCoordinate = D.extractionLevel := by
  have hqcoeff :
      MvPolynomial.coeff q (MvPolynomial.pderiv j D.child) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hq
  rw [coeff_pderiv_backport] at hqcoeff
  have hsourceCoeff :
      MvPolynomial.coeff (q + Finsupp.single j 1) D.child ≠ 0 := by
    intro hz
    simp [hz] at hqcoeff
  have hmem : q + Finsupp.single j 1 ∈ D.child.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hcoord := D.child_extractionCoordinate_eq hmem
  have hej : D.extractionCoordinate ≠ j := Ne.symm hje
  simpa [Finsupp.single_apply, hej] using hcoord

namespace ChildLinearPowerData

variable {m : ℕ}
variable (P : D.ChildLinearPowerData m)

/-- Coordinate partials of the same linear power satisfy the exact constant
cross-ratio relation. -/
theorem pderiv_ratio_cross
    (hm : 2 ≤ m)
    (i j : Fin 4) :
    MvPolynomial.C (P.ratio j) * MvPolynomial.pderiv i D.child =
      MvPolynomial.C (P.ratio i) * MvPolynomial.pderiv j D.child := by
  have hmrepr : m = (m - 1) + 1 := by omega
  rw [P.eq_power]
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C_mul]
  conv_lhs =>
    rhs
    rw [hmrepr]
  conv_rhs =>
    rhs
    rw [hmrepr]
  rw [pderiv_gradientRatioLinearForm_pow_succ]
  rw [pderiv_gradientRatioLinearForm_pow_succ]
  push_cast
  ring

/-- The extraction partial of the nonzero linear-power child is nonzero. -/
theorem extraction_pderiv_ne_zero
    (hm : 2 ≤ m) :
    MvPolynomial.pderiv D.extractionCoordinate D.child ≠ 0 := by
  have hmpos : 0 < m := by omega
  have ha : P.coefficient ≠ 0 := P.coefficient_ne_zero
  have hc : P.ratio D.extractionCoordinate ≠ 0 :=
    P.extraction_ratio_ne_zero hm
  have hL : gradientRatioLinearForm P.ratio ≠ 0 :=
    P.linearForm_ne_zero hmpos
  have hpow : (gradientRatioLinearForm P.ratio) ^ (m - 1) ≠ 0 :=
    pow_ne_zero _ hL
  rw [P.eq_power, MvPolynomial.pderiv_C_mul]
  have hmrepr : m = (m - 1) + 1 := by omega
  conv_lhs =>
    rhs
    rw [hmrepr]
  rw [pderiv_gradientRatioLinearForm_pow_succ]
  apply mul_ne_zero
  · simpa using ha
  · apply mul_ne_zero
    · have hmK : (m : K) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hmpos)
      have hmc : (m : K) * P.ratio D.extractionCoordinate ≠ 0 :=
        mul_ne_zero hmK hc
      simpa using hmc
    · exact hpow

/-- **Pure-axis classification.**  Every coefficient of the exact linear form
away from the extraction coordinate vanishes. -/
theorem ratio_eq_zero_of_ne_extraction
    (hm : 2 ≤ m)
    (j : Fin 4)
    (hje : j ≠ D.extractionCoordinate) :
    P.ratio j = 0 := by
  by_contra hj
  have he : P.ratio D.extractionCoordinate ≠ 0 :=
    P.extraction_ratio_ne_zero hm
  have hde :
      MvPolynomial.pderiv D.extractionCoordinate D.child ≠ 0 :=
    P.extraction_pderiv_ne_zero hm
  have hsupp :
      (MvPolynomial.pderiv D.extractionCoordinate D.child).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hde
  rcases hsupp with ⟨q, hqE⟩
  have hqEcoeff :
      MvPolynomial.coeff q
        (MvPolynomial.pderiv D.extractionCoordinate D.child) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hqE

  have hcross := P.pderiv_ratio_cross hm D.extractionCoordinate j
  have hcoeff := congrArg (MvPolynomial.coeff q) hcross
  have hqJcoeff :
      MvPolynomial.coeff q (MvPolynomial.pderiv j D.child) ≠ 0 := by
    intro hzero
    have hleft :
        P.ratio j *
          MvPolynomial.coeff q
            (MvPolynomial.pderiv D.extractionCoordinate D.child) ≠ 0 :=
      mul_ne_zero hj hqEcoeff
    apply hleft
    simpa [hzero] using hcoeff
  have hqJ : q ∈ (MvPolynomial.pderiv j D.child).support :=
    MvPolynomial.mem_support_iff.mpr hqJcoeff

  have hEcoord := D.pderiv_extraction_support_coordinate hqE
  have hJcoord := D.pderiv_other_support_extraction_coordinate j hje hqJ
  omega

/-- In particular the already stored kernel-coordinate vanishing is a special
case of the full pure-axis statement. -/
theorem kernel_ratio_eq_zero_from_pureAxis
    (hm : 2 ≤ m) :
    P.ratio D.kernelCoordinate = 0 := by
  exact P.ratio_eq_zero_of_ne_extraction hm D.kernelCoordinate
    (Ne.symm (P.extractionCoordinate_ne_kernelCoordinate hm))

end ChildLinearPowerData

end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
