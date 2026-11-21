import HC4.Polynomial.RankThreeCubicPoleSquarefreeResidue
import Mathlib

/-!
# A genuine 2x2 cofactor survives on a squarefree cubic pole component

A surviving Cramer numerator coordinate modulo an irreducible factor
forces a surviving adjugate entry modulo the same factor.
This is the nonzero 2x2-minor geometry needed to sharpen the
squarefree residue-kernel branch.

We do not assume a principal minor: an adjugate entry can be an
off-principal cofactor. The source-derived conclusion has the
nonzero kernel vector and a 2x2 cofactor on the *same* factor.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- A nonzero Cramer numerator modulo p forces a nonzero cofactor
of the underlying matrix modulo p. No rank theorem is presumed. -/
theorem exists_cofactor_not_dvd_of_cramer_numerator_not_dvd
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K) (p : B3 K)
    (hnon : ∃ i : Fin 3, ¬ p ∣ (H.adjugate *ᵥ r) i) :
    ∃ i j : Fin 3, ¬ p ∣ H.adjugate i j := by
  classical
  obtain ⟨i, hi⟩ := hnon
  by_contra h
  push_neg at h
  apply hi
  change p ∣ ∑ j : Fin 3, H.adjugate i j * r j
  apply Finset.dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_left (h i j) (r j)

/-- A squarefree determinant turns a genuinely non-polynomial
rational characteristic into both a nonzero residue Hessian kernel
and a nonvanishing adjugate cofactor on the same irreducible divisor.

The cofactor is necessarily a 2x2 minor, but need not be a
principal minor. It is an exact matrix-level geometric witness,
not a terminal contradiction. -/
theorem exists_residueKernel_and_cofactor_of_squarefree_fractionKernel
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (hnonpolynomial : ∃ i : Fin 3, ∀ a : B3 K,
      algebraMap (B3 K) (F3 K) a ≠ V i)
    (hsq : Squarefree H.det) :
    ∃ p : B3 K, Irreducible p ∧ p ∣ H.det ∧
      (∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
        S ≠ 0 ∧
        (H.map (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) ∧
      (∃ i j : Fin 3, ¬ p ∣ H.adjugate i j) := by
  classical
  obtain ⟨i, p, hp, hpdet, hpd, hpn⟩ :=
    exists_genuinePolePrime_of_nonPolynomial_fractionKernel
      H r V hkernel hnonpolynomial
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let n : B3 K := IsFractionRing.num (B3 K) (V i)
  let d : B3 K := IsFractionRing.den (B3 K) (V i)
  obtain ⟨c, hc⟩ := reduced_denominator_dvd_hessianDet H r V hkernel i
  have hfactor : H.det = d * c := hc
  have hnotc : ¬ p ∣ c := by
    intro hpc
    have hpp : p * p ∣ H.det := by
      rw [hfactor]
      exact mul_dvd_mul hpd hpc
    exact hp.not_isUnit (hsq p hpp)
  have hdn : g d ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (B3 K) (F3 K)).ne
        (nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B3 K) (V i)))
  have hfrac : V i * g d = g n := by
    have hrepr : g n / g d = V i :=
      IsFractionRing.mk'_num_den' (B3 K) (V i)
    rw [← hrepr]
    exact div_mul_cancel₀ _ hdn
  have hA : (H.adjugate *ᵥ r) i = n * c := by
    apply IsFractionRing.injective (B3 K) (F3 K)
    have hcramer :=
      fractionKernel_adjugate_numerator_identity H r V hkernel i
    calc
      g ((H.adjugate *ᵥ r) i) = g H.det * V i := hcramer.symm
      _ = (g d * g c) * V i := by rw [hfactor, map_mul]
      _ = g c * (V i * g d) := by ring
      _ = g c * g n := by rw [hfrac]
      _ = g (n * c) := by rw [map_mul]; ring
  have hnon : ¬ p ∣ (H.adjugate *ᵥ r) i := by
    rw [hA]
    exact hp.prime.not_dvd_mul hpn hnotc
  have hadj : H *ᵥ (H.adjugate *ᵥ r) = H.det • r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨S, hS, hker⟩ :=
    exists_nonzero_residueKernel_of_normalized_denominator
      H r (H.adjugate *ᵥ r) H.det p hadj hpdet ⟨i, hnon⟩
  obtain ⟨j, k, hjk⟩ :=
    exists_cofactor_not_dvd_of_cramer_numerator_not_dvd
      H r p ⟨i, hnon⟩
  exact ⟨p, hp, hpdet, ⟨S, hS, hker⟩, ⟨j, k, hjk⟩⟩

/-- The actual full-rank cubic source either has a constant-linear
rational characteristic, has a nonsquarefree selected determinant,
or gives on one irreducible source determinant factor *both* a
nonzero residue kernel and a nonzero Hessian 2x2 cofactor. -/
theorem exists_sourceCubic_linear_or_nonsquarefree_or_residueCofactor
    [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → F3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (F3 K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ ¬ Squarefree (sourceTransverseHessian a L).det
        ∨ ∃ p : B3 K, Irreducible p ∧
          p ∣ (sourceTransverseHessian a L).det ∧
          (∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
            S ≠ 0 ∧
            ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) ∧
          ∃ i j : Fin 3, ¬ p ∣
            (sourceTransverseHessian a L).adjugate i j) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linearVelocity_or_nonPolynomial F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnon
  · exact Or.inl hlin
  · by_cases hsq : Squarefree
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F)).det
    · exact Or.inr (Or.inr
        (exists_residueKernel_and_cofactor_of_squarefree_fractionKernel
          (sourceTransverseHessian a
            (initialForm transverseCubicWeight 3 F))
          (sourceNegativeMixedHessian a
            (initialForm transverseCubicWeight 3 F))
          (fun i => V (.inr i)) heq hnon hsq))
    · exact Or.inr (Or.inl hsq)

end
end HC4.Polynomial.RankThreeCubic
