import HC4.Polynomial.RankThreeCubicCancelledCramerResidue
import Mathlib.Tactic

/-!
# A genuine pole has a nonzero common-denominator residue

For three rational functions over K[y₁,y₂,y₃], use the least
common multiple of their *reduced denominators*. It is a polynomial
common denominator. If an irreducible p divides any one reduced
denominator, then p divides the common denominator, and some
common-denominator numerator survives reduction modulo p.

This provides the missing nonzero residue in the repeated-pole
branch without a chosen p-adic order or an additional endpoint
hypothesis. It applies to the source's actual rational characteristic.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- Every irreducible prime of one reduced coordinate denominator
supports a *nonzero* residue of the common-denominator numerators
of a finite rational vector. The common denominator is the LCM of
the three reduced coordinate denominators. -/
theorem exists_commonDenominator_nonzeroResidue_at_genuinePole
    (V : Fin 3 → F3 K)
    (p : B3 K)
    (hp : Irreducible p)
    (j : Fin 3)
    (hpj : p ∣ (IsFractionRing.den (B3 K) (V j) : B3 K)) :
    ∃ (s : B3 K) (T : Fin 3 → B3 K),
      p ∣ s ∧
      (∀ i : Fin 3,
        algebraMap (B3 K) (F3 K) (T i) =
          algebraMap (B3 K) (F3 K) s * V i) ∧
      (∃ i : Fin 3, ¬ p ∣ T i) := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let n : Fin 3 → B3 K := fun i => IsFractionRing.num (B3 K) (V i)
  let d : Fin 3 → B3 K :=
    fun i => (IsFractionRing.den (B3 K) (V i) : B3 K)
  let s : B3 K := (Finset.univ : Finset (Fin 3)).lcm d
  have hd0 (i : Fin 3) : d i ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B3 K) (V i))
  have hs0 : s ≠ 0 := by
    apply (Finset.lcm_ne_zero_iff).2
    intro i _
    exact hd0 i
  have hds (i : Fin 3) : d i ∣ s :=
    Finset.dvd_lcm (s := Finset.univ) (f := d) (Finset.mem_univ i)
  let t : Fin 3 → B3 K := fun i => Classical.choose (hds i)
  have ht (i : Fin 3) : s = d i * t i :=
    Classical.choose_spec (hds i)
  let T : Fin 3 → B3 K := fun i => n i * t i
  have hfrac (i : Fin 3) : V i * g (d i) = g (n i) := by
    have hgd : g (d i) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective (B3 K) (F3 K)).ne (hd0 i)
    have hrepr : g (n i) / g (d i) = V i :=
      IsFractionRing.mk'_num_den' (B3 K) (V i)
    rw [← hrepr]
    exact div_mul_cancel₀ _ hgd
  have hscale (i : Fin 3) : g (T i) = g s * V i := by
    calc
      g (T i) = g (n i) * g (t i) := map_mul g _ _
      _ = (V i * g (d i)) * g (t i) := by rw [hfrac]
      _ = g s * V i := by rw [ht i, map_mul]; ring
  have hps : p ∣ s :=
    (hpj : p ∣ d j).trans (hds j)
  refine ⟨s, T, hps, hscale, ?_⟩
  by_contra hall
  push_neg at hall
  have htdiv (i : Fin 3) : p ∣ t i := by
    by_contra hpt
    by_cases hpdi : p ∣ d i
    · have hnnot : ¬ p ∣ n i := by
        intro hpni
        have hrel : IsRelPrime (n i) (d i) :=
          IsFractionRing.num_den_reduced (B3 K) (V i)
        exact hp.not_isUnit (hrel hpni hpdi)
      have hpT : p ∣ n i * t i := hall i
      exact (hp.prime.not_dvd_mul hnnot hpt) hpT
    · have hptotal : p ∣ d i * t i := by
        rw [← ht i]
        exact hps
      exact (hp.prime.not_dvd_mul hpdi hpt) hptotal
  obtain ⟨u, hu⟩ := hps
  have hdsu (i : Fin 3) : d i ∣ u := by
    obtain ⟨v, hv⟩ := htdiv i
    have hp_eq : p * u = p * (d i * v) := by
      calc
        p * u = s := hu.symm
        _ = d i * t i := ht i
        _ = d i * (p * v) := by rw [hv]
        _ = p * (d i * v) := by ring
    exact ⟨v, mul_left_cancel₀ hp.ne_zero hp_eq⟩
  have hsu : s ∣ u := by
    apply Finset.lcm_dvd
    intro i _
    exact hdsu i
  obtain ⟨w, hw⟩ := hsu
  have hp_one : p ∣ (1 : B3 K) := by
    refine ⟨w, ?_⟩
    have heq : s * (1 : B3 K) = s * (p * w) := by
      calc
        s * 1 = s := by ring
        _ = p * u := hu
        _ = p * (s * w) := by rw [hw]
        _ = s * (p * w) := by ring
    exact (mul_left_cancel₀ hs0 heq).symm
  exact hp.not_isUnit (isUnit_of_dvd_one hp_one)

end HC4.Polynomial.RankThreeCubic
