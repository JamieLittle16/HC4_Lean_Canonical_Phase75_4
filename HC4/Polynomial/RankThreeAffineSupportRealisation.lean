import HC4.Polynomial.RankThreeAffineLineRealisation
import Mathlib.Tactic

/-!
# Generic affine-support realisation

This file packages a small piece of coefficient-profile plumbing that occurs
repeatedly in the rank-three closure.

If coordinate `0` is injective on the support of an honest multivariate
polynomial and every supported exponent lies on one affine rank-three line,
then collecting coefficients by coordinate `0` loses no information.  The
resulting one-variable profile therefore reconstructs the original polynomial
literally through `RankThreeAffineLineData`.

The omitted-coordinate step is one, which is exactly the form needed by the
finite-staircase cross-roof adapters.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Source-honest support data for a rank-three affine line with unit omitted
coordinate step. -/
structure RankThreeAffineSupportData
    (G : MvPolynomial (Fin 4) K)
    (A B C : ℕ) (q r s : K) where
  eq_of_zeroCoordinate_eq :
    ∀ {e f : Fin 4 →₀ ℕ}, e ∈ G.support → f ∈ G.support → e 0 = f 0 → e = f
  affine :
    ∀ e ∈ G.support,
      (fun i : Fin 4 => ((e i : ℕ) : K)) =
        fun i =>
          rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
            (e 0 : K) * rankThreeLogDirection (1 : K) q r s i

namespace RankThreeAffineSupportData

/-- Coefficient profile indexed by the honest coordinate-zero exponent. -/
noncomputable def coefficientProfile
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (_D : RankThreeAffineSupportData G A B C q r s) : Polynomial K :=
  ∑ e ∈ G.support, Polynomial.monomial (e 0) (MvPolynomial.coeff e G)

/-- Injectivity of coordinate zero prevents cancellation in the extracted
profile. -/
theorem coeff_coefficientProfile_of_mem
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    {e : Fin 4 →₀ ℕ} (he : e ∈ G.support) :
    D.coefficientProfile.coeff (e 0) = MvPolynomial.coeff e G := by
  classical
  change
    (∑ f ∈ G.support,
      Polynomial.monomial (f 0) (MvPolynomial.coeff f G)).coeff (e 0) =
      MvPolynomial.coeff e G
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hz : f 0 ≠ e 0 := by
      intro hcoord
      apply hfe
      exact D.eq_of_zeroCoordinate_eq hf he hcoord
    simp [Polynomial.coeff_monomial, hz]
  · intro hnot
    exact (hnot he).elim

/-- Every actual support exponent contributes its coordinate-zero index to the
profile. -/
theorem coefficientProfile_mem_of_mem
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    {e : Fin 4 →₀ ℕ} (he : e ∈ G.support) :
    e 0 ∈ D.coefficientProfile.support := by
  rw [Polynomial.mem_support_iff]
  rw [D.coeff_coefficientProfile_of_mem he]
  exact MvPolynomial.mem_support_iff.mp he

/-- Conversely, every profile support index comes from an actual exponent of
`G`. -/
theorem exists_exponent_of_coefficientProfile_mem
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    {n : ℕ} (hn : n ∈ D.coefficientProfile.support) :
    ∃ e ∈ G.support, e 0 = n := by
  classical
  by_contra hnone
  have hzero : D.coefficientProfile.coeff n = 0 := by
    unfold coefficientProfile
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    have hne : e 0 ≠ n := by
      intro h
      apply hnone
      exact ⟨e, he, h⟩
    simp [Polynomial.coeff_monomial, hne, Ne.symm hne]
  exact (Polynomial.mem_support_iff.mp hn) hzero

/-- Canonical exponent over a supported profile index. -/
noncomputable def exponentAt
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if hn : n ∈ D.coefficientProfile.support then
    Classical.choose (D.exists_exponent_of_coefficientProfile_mem hn)
  else 0

/-- The canonical exponent is supported and has the requested index. -/
theorem exponentAt_spec
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    {n : ℕ} (hn : n ∈ D.coefficientProfile.support) :
    D.exponentAt n ∈ G.support ∧ D.exponentAt n 0 = n := by
  unfold exponentAt
  rw [dif_pos hn]
  exact Classical.choose_spec
    (D.exists_exponent_of_coefficientProfile_mem hn)

/-- The generic affine-line package attached to the support data. -/
noncomputable def affineLineData
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s) :
    RankThreeAffineLineData A B C 1 q r s D.coefficientProfile where
  exponent := D.exponentAt
  affine := by
    intro n hn
    have hs := D.exponentAt_spec hn
    have haff := D.affine (D.exponentAt n) hs.1
    rw [hs.2] at haff
    simpa using haff

/-- The affine-line representation reconstructs the original polynomial
literally. -/
theorem affineLineData_polynomial_eq
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s) :
    D.affineLineData.polynomial = G := by
  classical
  let L := D.affineLineData
  change L.polynomial = G
  apply MvPolynomial.ext
  intro d
  simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ G.support
  · have hidx : d 0 ∈ D.coefficientProfile.support :=
      D.coefficientProfile_mem_of_mem hd
    have hexp : L.exponent (d 0) = d := by
      have hs := D.exponentAt_spec hidx
      change D.exponentAt (d 0) = d
      exact D.eq_of_zeroCoordinate_eq hs.1 hd hs.2
    have hcoeff : D.coefficientProfile.coeff (d 0) =
        MvPolynomial.coeff d G :=
      D.coeff_coefficientProfile_of_mem hd
    rw [Finset.sum_eq_single (d 0)]
    · rw [L.term_eq_monomial]
      simp [hexp, hcoeff]
    · intro n hn hnd
      have hne : L.exponent n ≠ d := by
        intro heq
        have h0 := congrArg (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) heq
        have hn0 : L.exponent n (0 : Fin 4) = n := by
          have hz := L.exponent_zero_eq hn
          simpa using hz
        have h0' : L.exponent n (0 : Fin 4) = d (0 : Fin 4) := by
          simpa using h0
        rw [hn0] at h0'
        exact hnd h0'
      rw [L.term_eq_monomial]
      simp [hne]
    · intro hnot
      exact (hnot hidx).elim
  · have hd0 : MvPolynomial.coeff d G = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hd0]
    apply Finset.sum_eq_zero
    intro n hn
    have hs := D.exponentAt_spec hn
    have hLmem : L.exponent n ∈ G.support := by
      change D.exponentAt n ∈ G.support
      exact hs.1
    have hne : L.exponent n ≠ d := by
      intro heq
      apply hd
      simpa [heq] using hLmem
    rw [L.term_eq_monomial]
    simp [hne]

/-- A supported exponent at coordinate zero gives a nonzero constant
coefficient in the exact profile. -/
theorem coeff_zero_ne_zero_of_mem_zero
    {G : MvPolynomial (Fin 4) K} {A B C : ℕ} {q r s : K}
    (D : RankThreeAffineSupportData G A B C q r s)
    {e : Fin 4 →₀ ℕ} (he : e ∈ G.support) (he0 : e 0 = 0) :
    D.coefficientProfile.coeff 0 ≠ 0 := by
  rw [← he0, D.coeff_coefficientProfile_of_mem he]
  exact MvPolynomial.mem_support_iff.mp he

end RankThreeAffineSupportData

end

end HC4.Polynomial
