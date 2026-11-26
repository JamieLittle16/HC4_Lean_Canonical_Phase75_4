module

public import HC4.Polynomial.RankThreeCubicPoleCofactor
public import Mathlib.Tactic

/-!
# Genuine nonzero Cramer residue on a squarefree cubic pole

For a rational solution H V = r with a non-polynomial coordinate,
a squarefree det(H) forces an irreducible determinant factor p at
which an *actual Cramer numerator* A = adj(H) r survives.

Unlike an unspecified quotient-kernel vector, this is the exact
numerator appearing in the cleared source quadratic transport
identity. It is therefore the missing nonzero input for the
quadratic pole-residue equation.

The statement is not yet a contradiction: a nonzero singular
direction can exist on an individual cubic.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RankThreeCubicSquarefreeCramerNonzero

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

end RankThreeCubicSquarefreeCramerNonzero

open RankThreeCubicSquarefreeCramerNonzero (B3 F3)

/-- A nonpolynomial rational Hessian characteristic with squarefree
determinant has an irreducible factor at which at least one coordinate
of its *Cramer numerator* is not divisible by that factor. -/
theorem exists_squarefreePole_CramerNumerator_not_dvd
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (hnonpoly : ∃ i : Fin 3, ∀ a : B3 K,
      algebraMap (B3 K) (F3 K) a ≠ V i)
    (hsq : Squarefree H.det) :
    ∃ (p : B3 K) (i : Fin 3),
      Irreducible p ∧ p ∣ H.det ∧
      ¬ p ∣ (H.adjugate *ᵥ r) i := by
  classical
  obtain ⟨i, p, hp, hpdet, hpd, hpn⟩ :=
    exists_genuinePolePrime_of_nonPolynomial_fractionKernel
      H r V hkernel hnonpoly
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
  exact ⟨p, i, hp, hpdet, hnon⟩

/-- For an irreducible pole factor, the genuine Cramer residue is
nonzero as a vector in the factor quotient. The corresponding
Hessian-kernel condition is retained without choosing a new vector. -/
theorem exists_squarefreePole_nonzeroCramerResidue
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (hnonpoly : ∃ i : Fin 3, ∀ a : B3 K,
      algebraMap (B3 K) (F3 K) a ≠ V i)
    (hsq : Squarefree H.det) :
    ∃ (p : B3 K),
      Irreducible p ∧ p ∣ H.det ∧
      let q := Ideal.Quotient.mk (Ideal.span {p})
      let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q ((H.adjugate *ᵥ r) j)
      S ≠ 0 ∧ (H.map q) *ᵥ S = 0 := by
  classical
  obtain ⟨p, i, hp, hpdet, hnon⟩ :=
    exists_squarefreePole_CramerNumerator_not_dvd
      H r V hkernel hnonpoly hsq
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q ((H.adjugate *ᵥ r) j)
  have hSi : S i ≠ 0 := by
    intro hz
    apply hnon
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hS : S ≠ 0 := by
    intro hzero
    exact hSi (by simpa using congrFun hzero i)
  have hadj : H *ᵥ (H.adjugate *ᵥ r) = H.det • r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdetzero : q H.det = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hpdet)
  have hker : (H.map q) *ᵥ S = 0 := by
    funext j
    change (∑ k : Fin 3, q (H j k) * q ((H.adjugate *ᵥ r) k)) = 0
    calc
      _ = q ((H *ᵥ (H.adjugate *ᵥ r)) j) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      _ = q (H.det * r j) := by
        rw [hadj]
        rfl
      _ = 0 := by rw [map_mul, hdetzero, zero_mul]
  exact ⟨p, hp, hpdet, hS, hker⟩

end
end HC4.Polynomial.RankThreeCubic
