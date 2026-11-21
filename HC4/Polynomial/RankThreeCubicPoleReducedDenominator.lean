import HC4.Polynomial.RankThreeCubicPoleDeterminant
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Tactic

/-!
# Genuine irreducible denominator factors for cubic rational characteristics

The determinantal-quotient kernel may be supported on a nonreduced
divisor. We therefore first isolate a *genuine* prime factor of a
reduced fraction's denominator. This gives a height-one pole witness
with a numerator not divisible by the same irreducible polynomial.

This module does not claim that the raw Cramer numerator survives
reduction modulo that prime (it can vanish for multiple factors of
the determinant). A maximal pole-order normalization remains necessary
before extracting the residue kernel.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- A reduced fraction whose coordinate is not polynomial has a genuine
irreducible denominator factor, absent from its reduced numerator. -/
theorem exists_irreducible_reduced_denominator_factor
    (x : F3 K)
    (hx : ∀ a : B3 K, algebraMap (B3 K) (F3 K) a ≠ x) :
    ∃ p : B3 K, Irreducible p ∧
      p ∣ (IsFractionRing.den (B3 K) x : B3 K) ∧
      ¬ p ∣ IsFractionRing.num (B3 K) x := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let n : B3 K := IsFractionRing.num (B3 K) x
  let d : B3 K := IsFractionRing.den (B3 K) x
  have hnonunit : ¬ IsUnit d := by
    intro hu
    have hinteger : IsLocalization.IsInteger (B3 K) x :=
      (IsFractionRing.isUnit_den_iff (B3 K) x).mp hu
    change x ∈ g.rangeS at hinteger
    obtain ⟨a, ha⟩ := hinteger
    exact hx a ha
  have hd0 : d ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B3 K) x)
  obtain ⟨p, hp, hpd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hnonunit hd0
  refine ⟨p, hp, hpd, ?_⟩
  intro hpn
  have hcop : IsRelPrime n d :=
    IsFractionRing.num_den_reduced (B3 K) x
  exact hp.not_isUnit (hcop hpn hpd)

/-- If H V = r and the determinant is nonzero, every reduced
coordinate denominator of V divides det(H), not merely some power of
det(H). This follows from Cramer's identity and coprimality. -/
theorem reduced_denominator_dvd_hessianDet
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (i : Fin 3) :
    (IsFractionRing.den (B3 K) (V i) : B3 K) ∣ H.det := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let n : B3 K := IsFractionRing.num (B3 K) (V i)
  let d : B3 K := IsFractionRing.den (B3 K) (V i)
  have hdn : g d ≠ 0 := by
    apply (IsFractionRing.injective (B3 K) (F3 K)).ne
    exact nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B3 K) (V i))
  have hfrac : V i * g d = g n := by
    have hrepr : g n / g d = V i :=
      IsFractionRing.mk'_num_den' (B3 K) (V i)
    rw [← hrepr]
    exact div_mul_cancel₀ _ hdn
  have heq : H.det * n = (H.adjugate *ᵥ r) i * d := by
    apply IsFractionRing.injective (B3 K) (F3 K)
    calc
      g (H.det * n) = g H.det * g n := map_mul g _ _
      _ = g H.det * (V i * g d) := by rw [hfrac]
      _ = (g H.det * V i) * g d := by ring
      _ = g ((H.adjugate *ᵥ r) i) * g d := by
        rw [fractionKernel_adjugate_numerator_identity H r V hkernel i]
      _ = g ((H.adjugate *ᵥ r) i * d) := (map_mul g _ _).symm
  have hdvd : d ∣ H.det * n := by
    refine ⟨(H.adjugate *ᵥ r) i, ?_⟩
    simpa [mul_comm] using heq
  have hcop : IsRelPrime d n :=
    (IsFractionRing.num_den_reduced (B3 K) (V i)).symm
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- Non-polynomial coordinate of a rational Hessian characteristic
selects an actual irreducible prime divisor of det H at which the
coordinate has a non-cancelled reduced denominator. -/
theorem exists_genuinePolePrime_of_nonPolynomial_fractionKernel
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (hnonpolynomial : ∃ i : Fin 3, ∀ a : B3 K,
      algebraMap (B3 K) (F3 K) a ≠ V i) :
    ∃ (i : Fin 3) (p : B3 K),
      Irreducible p ∧ p ∣ H.det ∧
      p ∣ (IsFractionRing.den (B3 K) (V i) : B3 K) ∧
      ¬ p ∣ IsFractionRing.num (B3 K) (V i) := by
  obtain ⟨i, hi⟩ := hnonpolynomial
  obtain ⟨p, hp, hpd, hpn⟩ :=
    exists_irreducible_reduced_denominator_factor (V i) hi
  have hdd : (IsFractionRing.den (B3 K) (V i) : B3 K) ∣ H.det :=
    reduced_denominator_dvd_hessianDet H r V hkernel i
  exact ⟨i, p, hp, dvd_trans hpd hdd, hpd, hpn⟩

/-- The actual full-transverse-rank cubic source yields either a
constant-linear rational characteristic or an irreducible pole prime
of its *source* transverse Hessian determinant. The non-cancellation
witness refers to a reduced coordinate, not an arbitrary denominator. -/
theorem exists_sourceCubic_linear_or_genuinePolePrime [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans :
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
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
        ∨
        (∃ (i : Fin 3) (p : B3 K),
          Irreducible p ∧
          p ∣ (sourceTransverseHessian a L).det ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr i)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr i)))) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linearVelocity_or_nonPolynomial F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnon
  · exact Or.inl hlin
  · exact Or.inr
      (exists_genuinePolePrime_of_nonPolynomial_fractionKernel
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F))
        (sourceNegativeMixedHessian a
          (initialForm transverseCubicWeight 3 F))
        (fun i => V (.inr i)) heq hnon)

end
end HC4.Polynomial.RankThreeCubic
