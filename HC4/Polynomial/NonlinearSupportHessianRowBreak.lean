import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Nonlinear support turns a first-derivative break into a Hessian-row break

The A19.55 coordinate-max parents are supported entirely in ordinary degrees
at least three.  Therefore a coordinate which genuinely occurs in the parent
cannot occur only affinely: some entry of the corresponding Hessian row is
nonzero.

This file isolates that elementary characteristic-zero coefficient fact.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A supported monomial positive in two distinct coordinates forces the
corresponding mixed second derivative to be nonzero. -/
theorem pderiv_pderiv_ne_zero_of_support_two_positive
    (k i : Fin 4)
    (hki : k ≠ i)
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hdk : 0 < d k)
    (hdi : 0 < d i) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv k F) ≠ 0 := by
  intro hzero
  let d₁ : Fin 4 →₀ ℕ := d - Finsupp.single k 1
  have hdk0 : d k ≠ 0 := Nat.ne_of_gt hdk
  have hadd : d₁ + Finsupp.single k 1 = d := by
    dsimp [d₁]
    exact Finsupp.sub_add_single_one_cancel hdk0
  have hdne : MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hd₁coeff :
      MvPolynomial.coeff d₁ (MvPolynomial.pderiv k F) ≠ 0 := by
    rw [HC4.Newton.coeff_pderiv_backport]
    rw [hadd]
    apply mul_ne_zero hdne
    exact_mod_cast Nat.succ_ne_zero (d₁ k)
  have hd₁zero : d₁ i = 0 :=
    HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero
      i (MvPolynomial.pderiv k F) hzero d₁ hd₁coeff
  have haddi := congrArg (fun e : Fin 4 →₀ ℕ => e i) hadd
  have hki' : i ≠ k := Ne.symm hki
  simp [hki'] at haddi
  omega

/-- If every source monomial has ordinary degree at least three, then a
nonzero first derivative in coordinate `k` forces some nonzero Hessian entry
in the `k` row. -/
theorem exists_hessian_entry_ne_zero_of_pderiv_ne_zero_of_support_degree_ge_three
    (k : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d)
    (hk : MvPolynomial.pderiv k F ≠ 0) :
    ∃ i : Fin 4,
      MvPolynomial.pderiv i (MvPolynomial.pderiv k F) ≠ 0 := by
  have hex : ∃ d ∈ F.support, 0 < d k := by
    by_contra hnone
    apply hk
    apply HC4.Newton.pderiv_eq_zero_of_all_supported_exponents_zero
    intro d hdcoeff
    have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hdcoeff
    have hnot : ¬ 0 < d k := by
      intro hpos
      exact hnone ⟨d, hd, hpos⟩
    exact Nat.eq_zero_of_not_pos hnot
  rcases hex with ⟨d, hd, hdk⟩
  by_cases hdk2 : 2 ≤ d k
  · exact ⟨k,
      HC4.Valuation.pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        k F d hd hdk2⟩
  · have hdk1 : d k = 1 := by omega
    have hdeg : 3 ≤ ordinaryDegree4 d := hnonlinear d hd
    have hother : ∃ i : Fin 4, i ≠ k ∧ 0 < d i := by
      fin_cases k
      · by_cases h1 : 0 < d (1 : Fin 4)
        · exact ⟨1, by decide, h1⟩
        by_cases h2 : 0 < d (2 : Fin 4)
        · exact ⟨2, by decide, h2⟩
        by_cases h3 : 0 < d (3 : Fin 4)
        · exact ⟨3, by decide, h3⟩
        have hz1 : d (1 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h1
        have hz2 : d (2 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h2
        have hz3 : d (3 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h3
        simp [ordinaryDegree4, hdk1, hz1, hz2, hz3] at hdeg
      · by_cases h0 : 0 < d (0 : Fin 4)
        · exact ⟨0, by decide, h0⟩
        by_cases h2 : 0 < d (2 : Fin 4)
        · exact ⟨2, by decide, h2⟩
        by_cases h3 : 0 < d (3 : Fin 4)
        · exact ⟨3, by decide, h3⟩
        have hz0 : d (0 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h0
        have hz2 : d (2 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h2
        have hz3 : d (3 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h3
        simp [ordinaryDegree4, hdk1, hz0, hz2, hz3] at hdeg
      · by_cases h0 : 0 < d (0 : Fin 4)
        · exact ⟨0, by decide, h0⟩
        by_cases h1 : 0 < d (1 : Fin 4)
        · exact ⟨1, by decide, h1⟩
        by_cases h3 : 0 < d (3 : Fin 4)
        · exact ⟨3, by decide, h3⟩
        have hz0 : d (0 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h0
        have hz1 : d (1 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h1
        have hz3 : d (3 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h3
        simp [ordinaryDegree4, hdk1, hz0, hz1, hz3] at hdeg
      · by_cases h0 : 0 < d (0 : Fin 4)
        · exact ⟨0, by decide, h0⟩
        by_cases h1 : 0 < d (1 : Fin 4)
        · exact ⟨1, by decide, h1⟩
        by_cases h2 : 0 < d (2 : Fin 4)
        · exact ⟨2, by decide, h2⟩
        have hz0 : d (0 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h0
        have hz1 : d (1 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h1
        have hz2 : d (2 : Fin 4) = 0 := Nat.eq_zero_of_not_pos h2
        simp [ordinaryDegree4, hdk1, hz0, hz1, hz2] at hdeg
    rcases hother with ⟨i, hik, hdi⟩
    exact ⟨i,
      pderiv_pderiv_ne_zero_of_support_two_positive
        k i (Ne.symm hik) F d hd hdk hdi⟩

end

end HC4.Polynomial
