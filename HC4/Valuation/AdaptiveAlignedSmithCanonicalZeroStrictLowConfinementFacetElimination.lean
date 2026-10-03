import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowResidualSupport
import Mathlib.Tactic

/-!
# A19.62: low-negative residual support eliminates confinement facets

A19.60 isolates the only genuinely lower-dimensional alternative in the
rank-three boundary branch: every nonlinear source monomial could be confined
to one coordinate facet.  A19.61 now gives literal nonlinear source monomials
forced by each low-negative strict-low residual.

Those witnesses immediately rule out two coordinate facets in each case:

* low-negative-first has positive source coordinates `0` and `2`, so only the
  facets omitting `1` or `3` can contain all nonlinear support;
* low-negative-second has positive source coordinates `0` and `1`, so only the
  facets omitting `2` or `3` can contain all nonlinear support.

This is a direct support contradiction.  No balance, cocharacter, or Hessian
argument is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Under low-negative-first, complete nonlinear confinement can survive only
on the facets omitting source coordinate `1` or `3`. -/
theorem lowNegativeFirst_nonlinearConfined_facet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hpat : IsLowNegativeFirstSmithPattern T.terminal.exponent)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    facet = .pr ∨ facet = .rq := by
  rcases T.lowNegativeFirst_sourceSupport hpat with
    ⟨d, hd, hdeg, hd0, hd2⟩
  have hfacet := hconfined d hd hdeg
  cases facet with
  | pr => exact Or.inl rfl
  | rq => exact Or.inr rfl
  | qs =>
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega
  | sp =>
      have hz : d (2 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega

/-- Under low-negative-second, complete nonlinear confinement can survive only
on the facets omitting source coordinate `2` or `3`. -/
theorem lowNegativeSecond_nonlinearConfined_facet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hpat : IsLowNegativeSecondSmithPattern T.terminal.exponent)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    facet = .sp ∨ facet = .rq := by
  rcases T.lowNegativeSecond_sourceSupport hpat with
    ⟨d, hd, hdeg, hd0, hd1⟩
  have hfacet := hconfined d hd hdeg
  cases facet with
  | pr =>
      have hz : d (1 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega
  | rq => exact Or.inr rfl
  | qs =>
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega
  | sp => exact Or.inl rfl

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
