import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesSectionTransport
import HC4.Valuation.StrictSmithFirstContactGeometry
import Mathlib.Tactic

/-!
# A19.29: parity of the early positive transverse Rees section frontier

The A19 positive transverse Rees family first ramifies the parameter by two.
The maximal moving-section frontier is measured *after* that ramification.
Consequently, whenever the frontier stops strictly before the determinant-
closing weight, the attained section order is an actual parameter order of a
ramified coordinate and is therefore even.

This is the source arithmetic needed to remove the artificial factor-two
cover in the next re-entry adapter.  No descent or recursion is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact parameter order scales by a positive parameter ramification.

This is the order-level counterpart of
`parameterRamification_sourceCoefficient_factorisation`: the primitive factor
remains primitive because positive ramification preserves its constant term. -/
theorem polynomialParameterOrder_parameterRamificationHom_eq
    (R : ℕ)
    (hR : 0 < R)
    (p : Polynomial K)
    (hp : p ≠ 0) :
    polynomialParameterOrder
        (parameterRamificationHom (K := K) R p)
        (parameterRamificationHom_ne_zero_of_pos R hR hp) =
      R * polynomialParameterOrder p hp := by
  let q := polynomialParameterOrder p hp
  let u := polynomialParameterPrimitivePart p hp
  have hprimitive : p = Polynomial.X ^ q * u := by
    simpa [q, u] using polynomialParameterPrimitivePart_spec p hp
  have hfactor :
      parameterRamificationHom (K := K) R p =
        Polynomial.X ^ (R * q) *
          parameterRamificationHom (K := K) R u := by
    rw [hprimitive, map_mul, parameterRamificationHom_X_pow]
  have huconst : Polynomial.constantCoeff u ≠ 0 := by
    simpa [u] using polynomialParameterPrimitivePart_constantCoeff_ne_zero p hp
  have hramconst :
      Polynomial.constantCoeff
          (parameterRamificationHom (K := K) R u) ≠ 0 := by
    rw [constantCoeff_parameterRamificationHom R hR]
    exact huconst
  exact
    polynomialParameterOrder_eq_of_exact_X_power_factorisation
      (parameterRamificationHom (K := K) R p)
      (parameterRamificationHom_ne_zero_of_pos R hR hp)
      (R * q)
      (parameterRamificationHom (K := K) R u)
      hramconst hfactor

/-- An early capped order of a section coordinate ramified by two is even. -/
theorem canonicalPositiveTransverseSectionOrderCap_parameterRamification_even_of_lt
    (Delta : ℕ)
    (b : Fin 4 → Polynomial K)
    (i : Fin 4)
    (hlt :
      canonicalPositiveTransverseSectionOrderCap Delta
          (parameterRamificationSection (K := K) 2 b i) < Delta) :
    Even
      (canonicalPositiveTransverseSectionOrderCap Delta
        (parameterRamificationSection (K := K) 2 b i)) := by
  let p := parameterRamificationSection (K := K) 2 b i
  rcases canonicalPositiveTransverseSectionOrderCap_exact_of_lt
      (K := K) Delta p hlt with
    ⟨hp, hfactor, hconst⟩
  have hbi : b i ≠ 0 := by
    intro hzero
    apply hp
    simp [p, parameterRamificationSection, hzero]
  have horderRam :
      polynomialParameterOrder p hp =
        2 * polynomialParameterOrder (b i) hbi := by
    simpa [p, parameterRamificationSection] using
      polynomialParameterOrder_parameterRamificationHom_eq
        (K := K) 2 (by norm_num) (b i) hbi
  have horderCap :
      polynomialParameterOrder p hp =
        canonicalPositiveTransverseSectionOrderCap Delta p := by
    exact
      polynomialParameterOrder_eq_of_exact_X_power_factorisation
        p hp
        (canonicalPositiveTransverseSectionOrderCap Delta p)
        (polynomialParameterPrimitivePart p hp)
        hconst hfactor
  refine ⟨polynomialParameterOrder (b i) hbi, ?_⟩
  dsimp [p] at horderRam horderCap ⊢
  omega

/-- **Every strict early A19 section frontier has even weight.**

Thus the factor-two parameter cover introduced by the positive transverse
Rees transform has not created an intrinsically odd first section contact. -/
theorem canonicalPositiveTransverseSectionFrontierWeight_even_of_lt
    (Delta : ℕ)
    (b : Fin 4 → Polynomial K)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight Delta b < Delta) :
    Even (canonicalPositiveTransverseSectionFrontierWeight Delta b) := by
  rcases canonicalPositiveTransverseSectionFrontierWeight_eq_cap
      (K := K) Delta b with h1 | h2 | h3
  · rw [h1]
    apply
      canonicalPositiveTransverseSectionOrderCap_parameterRamification_even_of_lt
        (K := K) Delta b (1 : Fin 4)
    rw [← h1]
    exact hlt
  · rw [h2]
    apply
      canonicalPositiveTransverseSectionOrderCap_parameterRamification_even_of_lt
        (K := K) Delta b (2 : Fin 4)
    rw [← h2]
    exact hlt
  · rw [h3]
    apply
      canonicalPositiveTransverseSectionOrderCap_parameterRamification_even_of_lt
        (K := K) Delta b (3 : Fin 4)
    rw [← h3]
    exact hlt

end

end HC4.Valuation
