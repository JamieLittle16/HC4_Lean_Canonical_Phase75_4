import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.AdaptiveSmithFourBlockCovariance
import HC4.Polynomial.DerivativeWeight
import Mathlib.Tactic

/-!
# Associated graded layers of the bounded reverse Rees family

The bounded reverse-Rees construction is already coefficientwise exact.  This
file records the corresponding state-free associated-graded identities: its
parameter layer of order `n` is literally the weighted initial form of the
original source at weight `D - n`, and its Hessian coefficient is the
corresponding shifted initial form of the actual source Hessian.

For the final ray argument we also record an exact normalization equation for
all three denominator-cleared Schur entries.  These equations are obtained
without expanding the Schur cubics: source inflation is diagonal congruence,
and the reverse-Rees family inflates to one common parameter monomial times the
original source.

This is the provenance bridge needed by the final zero-defect ray argument.
It introduces no terminal state, clock comparison, or repair step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

variable {K : Type*} [Field K]

/-- Generic associated-graded extraction from an exact adaptive normalization.
If inflating a polynomial family by `w` gives exactly `X^E` times a constant
source, then every in-range parameter layer is the corresponding weighted
initial form of that source. -/
theorem familyParameterLayer_eq_initialForm_of_adaptiveSmithInflate_eq
    (w : Fin 4 → ℕ) (E n : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (G : MvPolynomial (Fin 4) K)
    (hEq : adaptiveSmithInflateHom w P =
      MvPolynomial.C (Polynomial.X ^ E) * constantPolynomialFamily G)
    (hn : n ≤ E) :
    familyParameterLayer P n =
      initialForm (fun i => (w i : ℤ)) ((E - n : ℕ) : ℤ) G := by
  ext d
  rw [familyParameterLayer_coeff, HC4.Polynomial.coeff_initialForm]
  have heq := congrArg (MvPolynomial.coeff d) hEq
  rw [coeff_adaptiveSmithInflateHom,
    MvPolynomial.coeff_C_mul, coeff_constantPolynomialFamily] at heq
  have hcoeff := congrArg
    (fun c : Polynomial K => c.coeff (Finsupp.weight w d + n)) heq
  change
    (Polynomial.X ^ Finsupp.weight w d * MvPolynomial.coeff d P).coeff
        (Finsupp.weight w d + n) =
      (Polynomial.X ^ E * Polynomial.C (MvPolynomial.coeff d G)).coeff
        (Finsupp.weight w d + n) at hcoeff
  have hleft :
      (Polynomial.X ^ Finsupp.weight w d * MvPolynomial.coeff d P).coeff
          (Finsupp.weight w d + n) =
        (MvPolynomial.coeff d P).coeff n := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  rw [hleft] at hcoeff
  have hcast :
      Finsupp.weight (fun i => (w i : ℤ)) d =
        (Finsupp.weight w d : ℤ) := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply]
    push_cast
    rfl
  rw [hcast]
  by_cases hw : Finsupp.weight w d = E - n
  · have hsum : Finsupp.weight w d + n = E := by omega
    have hwz :
        (Finsupp.weight w d : ℤ) = ((E - n : ℕ) : ℤ) := by
      exact_mod_cast hw
    rw [Polynomial.coeff_X_pow_mul'] at hcoeff
    simp [hsum] at hcoeff
    simpa [hwz] using hcoeff
  · have hwz :
        (Finsupp.weight w d : ℤ) ≠ ((E - n : ℕ) : ℤ) := by
      exact_mod_cast hw
    have hsumne : Finsupp.weight w d + n ≠ E := by
      intro hsum
      apply hw
      omega
    by_cases hle : E ≤ Finsupp.weight w d + n
    · have hpos : 0 < Finsupp.weight w d + n - E := by omega
      have hne : Finsupp.weight w d + n - E ≠ 0 := Nat.ne_of_gt hpos
      rw [Polynomial.coeff_X_pow_mul'] at hcoeff
      simp only [if_pos hle] at hcoeff
      rw [Polynomial.coeff_C] at hcoeff
      simp [hne] at hcoeff
      simpa [hwz] using hcoeff
    · rw [Polynomial.coeff_X_pow_mul'] at hcoeff
      simp [hle] at hcoeff
      simpa [hwz] using hcoeff

/-- Every in-range parameter layer of a bounded reverse Rees family is exactly
an initial form of the original source. -/
theorem reverseWeightedReesFamily_parameterLayer_eq_initialForm
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (hn : n ≤ D) :
    familyParameterLayer (reverseWeightedReesFamily w D F h) n =
      initialForm (fun i => (w i : ℤ)) ((D - n : ℕ) : ℤ) F := by
  exact familyParameterLayer_eq_initialForm_of_adaptiveSmithInflate_eq
    w D n (reverseWeightedReesFamily w D F h) F
    (adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h) hn

/-- Coefficientwise Hessian provenance for the reverse Rees family.  At
parameter order `n`, differentiation merely shifts the associated weight by
the two differentiated coordinate weights. -/
theorem reverseWeightedRees_parameterFirstHessian_coeff_eq_initialForm
    [CharZero K]
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (hn : n ≤ D)
    (i j : Fin 4) :
    (parameterFirstHessian (reverseWeightedReesFamily w D F h) i j).coeff n =
      initialForm (fun k => (w k : ℤ))
        (((D - n : ℕ) : ℤ) - (w i : ℤ) - (w j : ℤ))
        (HC4.Polynomial.hessian F i j) := by
  rw [parameterFirstHessian_coeff]
  rw [reverseWeightedReesFamily_parameterLayer_eq_initialForm w D n F h hn]
  exact HC4.Polynomial.hessian_initialForm_entry
    (fun k => (w k : ℤ)) ((D - n : ℕ) : ℤ) F i j

/-! ## Exact Schur normalization -/

/-- Exact source-normalization equation for the first cleared Schur entry of a
bounded reverse Rees family. -/
theorem reverseWeightedRees_schurA_normalization
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4)) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ w (rho 2))) ^ 2 *
      adaptiveSmithInflateHom w HQ.schurA =
        (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily HF.schurA := by
  dsimp
  let Q := reverseWeightedReesFamily w D F h
  calc
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
          MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
        (MvPolynomial.C (Polynomial.X ^ w (rho 2))) ^ 2 *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho Q).schurA =
      (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom w Q)).schurA := by
          exact (schurA_adaptiveSmithInflateHom w rho Q).symm
    _ = (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurA := by
      rw [adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h,
        schurA_C_mul, schurA_constantPolynomialFamily]

/-- Exact source-normalization equation for the off-diagonal cleared Schur
entry of a bounded reverse Rees family. -/
theorem reverseWeightedRees_schurB_normalization
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4)) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
      MvPolynomial.C (Polynomial.X ^ w (rho 2)) *
      MvPolynomial.C (Polynomial.X ^ w (rho 3)) *
      adaptiveSmithInflateHom w HQ.schurB =
        (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily HF.schurB := by
  dsimp
  let Q := reverseWeightedReesFamily w D F h
  calc
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
          MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
        MvPolynomial.C (Polynomial.X ^ w (rho 2)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 3)) *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho Q).schurB =
      (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom w Q)).schurB := by
          exact (schurB_adaptiveSmithInflateHom w rho Q).symm
    _ = (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurB := by
      rw [adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h,
        schurB_C_mul, schurB_constantPolynomialFamily]

/-- Exact source-normalization equation for the second diagonal cleared Schur
entry of a bounded reverse Rees family. -/
theorem reverseWeightedRees_schurC_normalization
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (rho : Equiv.Perm (Fin 4)) :
    let Q := reverseWeightedReesFamily w D F h
    let HQ := permutedPolynomialHessianFourBlock rho Q
    let HF := permutedPolynomialHessianFourBlock rho F
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ w (rho 3))) ^ 2 *
      adaptiveSmithInflateHom w HQ.schurC =
        (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily HF.schurC := by
  dsimp
  let Q := reverseWeightedReesFamily w D F h
  calc
    (MvPolynomial.C (Polynomial.X ^ w (rho 0)) *
          MvPolynomial.C (Polynomial.X ^ w (rho 1))) ^ 2 *
        (MvPolynomial.C (Polynomial.X ^ w (rho 3))) ^ 2 *
        adaptiveSmithInflateHom w
          (permutedPolynomialHessianFourBlock rho Q).schurC =
      (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom w Q)).schurC := by
          exact (schurC_adaptiveSmithInflateHom w rho Q).symm
    _ = (MvPolynomial.C (Polynomial.X ^ D)) ^ 3 *
          constantPolynomialFamily
            (permutedPolynomialHessianFourBlock rho F).schurC := by
      rw [adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h,
        schurC_C_mul, schurC_constantPolynomialFamily]

end

end HC4.Valuation
