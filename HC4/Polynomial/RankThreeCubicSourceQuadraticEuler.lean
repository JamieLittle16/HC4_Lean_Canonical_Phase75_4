import HC4.Polynomial.RankThreeCubicSourceDegrees
import Mathlib.Tactic

/-!
# The source quadratic transverse gradient identity

The transverse initial form of a cubic-cap source has transverse weight
three. Each transverse gradient component therefore has weight two.

Apply the transverse Euler identity twice. The result is an *exact*
source-polynomial identity expressing twice each transverse gradient
component as a quadratic form in the transverse coordinates, with
coefficients given by source third derivatives.

This is the algebraic input to the second-order gradient-transport
pole-residue calculation. It neither assumes a rational velocity nor
claims a pole contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial Finsupp
open scoped BigOperators

noncomputable section

-- Two nested weighted Euler expansions are elaboration-heavy for MvPolynomial.
set_option maxHeartbeats 500000

variable {K : Type*} [Field K] [CharZero K]

private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The source's natural transverse weight and integer transverse
weight agree on every monomial. -/
private theorem cubicNatWeight_cast (d : (Unit ⊕ Fin 3) →₀ ℕ) :
    ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) =
      Finsupp.weight transverseCubicWeight d := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases i with
  | inl u =>
    cases u
    simp [transverseCubicNatWeight, transverseCubicWeight]
  | inr j =>
    simp [transverseCubicNatWeight, transverseCubicWeight, nsmul_eq_mul]

/-- Euler identity for the three transverse variables in the source,
with the longitudinal variable treated as a coefficient parameter. -/
theorem transverseSourceEuler
    (P : SB K) (n : ℕ)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    (∑ j : Fin 3, (X (.inr j) : SB K) * pderiv (.inr j) P) = n • P := by
  have hNat : P.IsWeightedHomogeneous transverseCubicNatWeight n := by
    intro d hd
    have h : ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) =
        (n : ℤ) := by
      rw [cubicNatWeight_cast]
      exact hP hd
    exact_mod_cast h
  have hEuler := hNat.sum_weight_X_mul_pderiv
  simpa [transverseCubicNatWeight, Fintype.sum_sum_type] using hEuler

/-- Weighted-degree-two source polynomials are precisely quadratic
in the transverse variables, in the Euler-polarised sense. This is
valid even if their coefficients have arbitrary longitudinal degree. -/
theorem transverseSourceQuadraticEuler
    (P : SB K)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight 2) :
    (2 : SB K) * P =
      ∑ j : Fin 3, ∑ k : Fin 3,
        (X (.inr j) : SB K) * X (.inr k) *
          pderiv (.inr k) (pderiv (.inr j) P) := by
  have hPj (j : Fin 3) :
      (pderiv (.inr j) P).IsWeightedHomogeneous transverseCubicWeight 1 := by
    have h := pderiv_isWeightedHomogeneous hP (.inr j)
    simpa [transverseCubicWeight] using h
  have he2 :
      (∑ j : Fin 3, (X (.inr j) : SB K) * pderiv (.inr j) P) =
        (2 : ℕ) • P :=
    transverseSourceEuler P 2 hP
  have he1 (j : Fin 3) :
      pderiv (.inr j) P =
        ∑ k : Fin 3, (X (.inr k) : SB K) *
          pderiv (.inr k) (pderiv (.inr j) P) := by
    let Q : SB K := pderiv (.inr j) P
    have hQ : Q.IsWeightedHomogeneous transverseCubicWeight 1 := hPj j
    have hQe :
        (∑ k : Fin 3, (X (.inr k) : SB K) * pderiv (.inr k) Q) =
          (1 : ℕ) • Q := transverseSourceEuler Q 1 hQ
    change Q = ∑ k : Fin 3, (X (.inr k) : SB K) * pderiv (.inr k) Q
    exact (by simpa only [one_nsmul] using hQe.symm)
  calc
    (2 : SB K) * P = (2 : ℕ) • P := by simp [nsmul_eq_mul]
    _ = ∑ j : Fin 3, (X (.inr j) : SB K) * pderiv (.inr j) P :=
      he2.symm
    _ = ∑ j : Fin 3, ∑ k : Fin 3,
          (X (.inr j) : SB K) * X (.inr k) *
            pderiv (.inr k) (pderiv (.inr j) P) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (X (.inr j) : SB K) * pderiv (.inr j) P =
            X (.inr j) *
              (∑ k : Fin 3, (X (.inr k) : SB K) *
                pderiv (.inr k) (pderiv (.inr j) P)) := by
              exact congrArg (fun q : SB K => (X (.inr j) : SB K) * q) (he1 j)
        _ = ∑ k : Fin 3, X (.inr j) * X (.inr k) *
              pderiv (.inr k) (pderiv (.inr j) P) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- The actual cubic initial source satisfies the quadratic
third-derivative representation, with no artificial chart or
additional source assumption. -/
theorem sourceCubic_transverseGradient_quadraticIdentity
    (F : SB K) (i : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    (2 : SB K) * pderiv (.inr i) L =
      ∑ j : Fin 3, ∑ k : Fin 3,
        (X (.inr j) : SB K) * X (.inr k) *
          pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)) := by
  let L := initialForm transverseCubicWeight 3 F
  have hL : L.IsWeightedHomogeneous transverseCubicWeight 3 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have hP : (pderiv (.inr i) L).IsWeightedHomogeneous
      transverseCubicWeight 2 := by
    have h := pderiv_isWeightedHomogeneous hL (.inr i)
    simpa [transverseCubicWeight] using h
  exact transverseSourceQuadraticEuler
    (pderiv (.inr i) L) hP

end
end HC4.Polynomial.RankThreeCubic
