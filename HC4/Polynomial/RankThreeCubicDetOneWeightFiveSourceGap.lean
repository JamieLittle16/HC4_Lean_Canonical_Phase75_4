import HC4.Polynomial.RankThreeCubicDetOneWeightFiveDeterminantGap

/-!
# No strictly subquadratic source contribution at Hessian weight five

For a source F with transverse weight at most 3, write
  L3 = initialForm weight 3 F
  L2 = initialForm weight 2 F
  R = F - L3 - L2.

The actual R has strict weight below 2. Hence its Hessian is two
weights below the nominal cubic Hessian entry bounds and does not
contribute to the first lower determinant component (weight 5).

This theorem uses the verified general determinant entry-gap lemma
and the exact decomposition of the ORIGINAL source F. It does not
yet identify that coefficient as the adjugate-trace pairing.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The weight-five Hessian determinant of the full source depends
only on the original source's true cubic and quadratic layers. -/
theorem sourceCubic_weightFive_det_eq_cubic_plus_quadratic
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F) :
    initialForm transverseCubicWeight 5 (hessianDeterminant F) =
      initialForm transverseCubicWeight 5
        (hessianDeterminant
          (initialForm transverseCubicWeight 3 F +
           initialForm transverseCubicWeight 2 F)) := by
  classical
  let w := transverseCubicWeight
  let L3 : SB K := initialForm w 3 F
  let L2 : SB K := initialForm w 2 F
  let R : SB K := (F - L3) - L2
  have hR : IsWeightLT w 2 R := by
    change IsWeightLT w 2
      ((F - initialForm w 3 F) - initialForm w 2 F)
    rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
    exact sourceCubic_belowTwo_strictWeight F hcap
  have hL3 : IsWeightLE w 3 L3 :=
    isWeightLE_of_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous w 3 F)
  have hL2 : IsWeightLE w 3 L2 := by
    intro d hd
    have h2 : Finsupp.weight w d ≤ 2 :=
      (isWeightLE_of_isWeightedHomogeneous
        (initialForm_isWeightedHomogeneous w 2 F)) hd
    omega
  have hN : IsWeightLE w 3 (L3 + L2) :=
    hL3.add hL2
  have hF : F = L3 + L2 + R := by
    dsimp [R]
    ring
  have hdifference (i j : Unit ⊕ Fin 3) :
      hessian F i j - hessian (L3 + L2) i j =
        hessian R i j := by
    rw [hF]
    simp only [hessian_apply, map_add, add_sub_cancel_left]
  have hweights (π : Equiv.Perm (Unit ⊕ Fin 3)) :
      (∑ i : Unit ⊕ Fin 3,
        (3 - w (π i) - w i : ℤ)) = 6 := by
    have h := hessianTermWeight_eq w 3 π
    have hd :
        (Fintype.card (Unit ⊕ Fin 3) : ℤ) * 3 -
          2 * ∑ i : Unit ⊕ Fin 3, w i = 6 := by
      decide
    exact h.trans hd
  have hsource := initialForm_det_eq_of_entry_gapOne
    (ι := Unit ⊕ Fin 3) w 6
    (fun i j : Unit ⊕ Fin 3 => 3 - w i - w j)
    (hessian F) (hessian (L3 + L2))
    hweights
    (fun i j => hcap.hessian_entry i j)
    (fun i j => hN.hessian_entry i j)
    (by
      intro i j
      have hb := hR.hessian_entry i j
      have hw : (2 : ℤ) - w i - w j =
          (3 - w i - w j) - 1 := by ring
      rw [hw] at hb
      rw [hdifference i j]
      exact hb)
  change initialForm w 5 (hessian F).det =
    initialForm w 5 (hessian (L3 + L2)).det
  simpa only [show (6 : ℤ) - 1 = 5 by norm_num] using hsource

/-- Determinant one forces the weight-five determinant component
of the ACTUAL cubic-plus-quadratic source to vanish.
No separate polynomial determinant-zero assumption is introduced. -/
theorem sourceCubic_detOne_cubic_plus_quadratic_weightFive_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    initialForm transverseCubicWeight 5
      (hessianDeterminant
        (initialForm transverseCubicWeight 3 F +
         initialForm transverseCubicWeight 2 F)) = 0 := by
  have hsource :=
    sourceCubic_weightFive_det_eq_cubic_plus_quadratic F hcap
  rw [sourceCubic_detOne_weightFive_initialForm_zero F hdetOne] at hsource
  exact hsource.symm

end
end HC4.Polynomial.RankThreeCubic
