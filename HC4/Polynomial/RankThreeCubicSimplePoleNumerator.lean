import HC4.Polynomial.RankThreeCubicSquarefreeCramerNonzero
import Mathlib.Tactic

/-!
# A simple genuine pole has a surviving Cramer numerator

For a polynomial Hessian system over a fraction field, the reduced
denominator of a rational solution divides the determinant. If a
genuine reduced denominator factor occurs only once in that determinant,
the Cramer numerator cannot vanish modulo the factor.

This result is local to a chosen irreducible factor: no global
squarefreeness assumption is used.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- At a simple irreducible factor of det(H) supporting a *genuine*
reduced denominator pole, the actual Cramer numerator survives modulo
that factor. This does not require det(H) to be squarefree globally. -/
theorem cramerNumerator_not_dvd_of_simplePole
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun j => algebraMap (B3 K) (F3 K) (r j))
    (i : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V i) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V i))
    (hsimple : ¬ p * p ∣ H.det) :
    ¬ p ∣ (H.adjugate *ᵥ r) i := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let n : B3 K := IsFractionRing.num (B3 K) (V i)
  let d : B3 K := IsFractionRing.den (B3 K) (V i)
  obtain ⟨c, hc⟩ := reduced_denominator_dvd_hessianDet H r V hkernel i
  have hfactor : H.det = d * c := hc
  have hnotc : ¬ p ∣ c := by
    intro hpc
    apply hsimple
    rw [hfactor]
    exact mul_dvd_mul hpd hpc
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
  rw [hA]
  exact hp.prime.not_dvd_mul hpn hnotc

end
end HC4.Polynomial.RankThreeCubic
