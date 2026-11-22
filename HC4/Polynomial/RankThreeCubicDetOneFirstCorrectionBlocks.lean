import HC4.Polynomial.RankThreeCubicDetOneRepairSecondLayer

/-!
# Source-honest 3+2+lower Hessian decomposition

The source is separated into the ACTUAL transverse weight-three
and weight-two components, with a remainder of weight strictly
below two. This is not an assumed abstract 4x4 Hessian splitting.

The remainder's transverse-transverse block vanishes exactly.
Its longitudinal-transverse block has zero transverse derivative.
These are the blockwise facts needed for the first-lower-weight
determinant coefficient, where only the weight-two source layer
can contribute.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
noncomputable section

variable {K : Type*} [Field K]
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A source polynomial of transverse weight below two has a mixed
Hessian block independent of all transverse coordinates. -/
theorem transverseCubicWeight_belowTwo_mixedHessian_pderiv_zero
    (P : SB K)
    (hP : IsWeightLT transverseCubicWeight 2 P)
    (i k : Fin 3) :
    pderiv (.inr k) (hessian P (.inl ()) (.inr i)) = 0 := by
  have hH := hP.hessian_entry (.inl ()) (.inr i)
  have hw :
      (2 : ℤ) - transverseCubicWeight (.inl ()) -
        transverseCubicWeight (.inr i) = 1 := by
    simp [transverseCubicWeight]
  rw [hw] at hH
  exact transverseCubicWeight_pderiv_eq_zero_of_lt_one _ hH k

/-- The source remainder after removing both the cubic and
quadratic transverse components has no variable mixed-Hessian
correction: the mixed block is transverse-constant. -/
theorem sourceCubic_subTwo_mixedHessian_pderiv_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i k : Fin 3) :
    pderiv (.inr k)
      (hessian
        ((F - initialForm transverseCubicWeight 3 F) -
          initialForm transverseCubicWeight 2 F)
        (.inl ()) (.inr i)) = 0 := by
  have hR : IsWeightLT transverseCubicWeight 2
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F) := by
    rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
    exact sourceCubic_belowTwo_strictWeight F hcap
  exact transverseCubicWeight_belowTwo_mixedHessian_pderiv_zero _ hR i k

/-- The original four-variable source Hessian is the sum of the
source-derived cubic and quadratic Hessians and the Hessian of
the strict-below-two remainder. -/
theorem sourceCubic_hessian_three_two_lower_decomposition
    (F : SB K) :
    hessian F =
      hessian (initialForm transverseCubicWeight 3 F) +
      hessian (initialForm transverseCubicWeight 2 F) +
      hessian
        ((F - initialForm transverseCubicWeight 3 F) -
          initialForm transverseCubicWeight 2 F) := by
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let R : SB K := (F - L3) - L2
  have hF : L3 + L2 + R = F := by
    dsimp [R]
    ring
  ext i j
  have hf := congrArg (fun P : SB K => hessian P i j) hF
  simpa only [hessian_apply, map_add] using hf.symm

/-- The weight-five component of the original Hessian determinant
is zero whenever the original determinant is one. This is the
source side of the forthcoming first-correction coefficient identity. -/
theorem sourceCubic_detOne_weightFive_initialForm_zero
    (F : SB K) (hdetOne : hessianDeterminant F = 1) :
    initialForm transverseCubicWeight 5 (hessianDeterminant F) = 0 := by
  rw [hdetOne]
  have hz :=
    initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C
        transverseCubicWeight (1 : K))
      5 (by norm_num)
  simpa only [map_one] using hz

end
end HC4.Polynomial.RankThreeCubic
