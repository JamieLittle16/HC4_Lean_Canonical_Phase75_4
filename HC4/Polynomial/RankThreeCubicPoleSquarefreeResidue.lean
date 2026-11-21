import HC4.Polynomial.RankThreeCubicPoleReducedDenominator
import Mathlib

/-!
# A genuine cubic characteristic pole on a squarefree determinant

For a squarefree transverse Hessian determinant, reducing the raw
Cramer numerator modulo a non-cancelled denominator prime gives a
nonzero vector. Its Hessian image vanishes in the prime quotient.

The source-level conclusion is unconditional: either the actual
cubic characteristic is linear, its specialized transverse determinant
is not squarefree, or it yields this nonzero residue kernel.

This theorem does not rule out the pole branch. Neither the residue
kernel nor nonsquarefree determinant is yet contradictory.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- For a squarefree polynomial determinant, an actual non-polynomial
characteristic yields a nonzero kernel vector modulo an irreducible
divisor of the determinant.

Squarefreeness is an explicit hypothesis here, not a general property
of the source. The repeated-factor case remains separate. -/
theorem exists_nonzero_primeResidueKernel_of_squarefree_fractionKernel
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
      ∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
        S ≠ 0 ∧
        (H.map (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0 := by
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
    exact (hp.prime.not_dvd_mul hpn hnotc)
  have hadj : H *ᵥ (H.adjugate *ᵥ r) = H.det • r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨S, hS, hker⟩ :=
    exists_nonzero_residueKernel_of_normalized_denominator
      H r (H.adjugate *ᵥ r) H.det p hadj hpdet ⟨i, hnon⟩
  exact ⟨p, hp, hpdet, S, hS, hker⟩

/-- On an actual cap-three full-transverse-rank cubic source, the
remaining rational characteristic is either linear, its chosen
source slice has a nonsquarefree transverse Hessian determinant,
or there is a genuine nonzero residue kernel at a prime factor.

Unlike the squarefree lemma above, no squarefree assumption is
imposed on F: the nonsquarefree case is an explicit disjunct. -/
theorem exists_sourceCubic_linear_or_nonsquarefree_or_primeResidue
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
          ∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
            S ≠ 0 ∧
            ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linearVelocity_or_nonPolynomial F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnon
  · exact Or.inl hlin
  · by_cases hsq : Squarefree
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F)).det
    · exact Or.inr (Or.inr
        (exists_nonzero_primeResidueKernel_of_squarefree_fractionKernel
          (sourceTransverseHessian a
            (initialForm transverseCubicWeight 3 F))
          (sourceNegativeMixedHessian a
            (initialForm transverseCubicWeight 3 F))
          (fun i => V (.inr i)) heq hnon hsq))
    · exact Or.inr (Or.inl hsq)

end
end HC4.Polynomial.RankThreeCubic
