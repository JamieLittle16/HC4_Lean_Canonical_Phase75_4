import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementFacetElimination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import Mathlib.Tactic

/-!
# A19.64: every strict-low nonlinear confinement avoids the marked facet

A19.61 and A19.63 turn each of the three strict-low residual patterns into an
actual nonlinear source monomial with positive distinguished longitudinal
coordinate.  Complete nonlinear confinement to the `qs` facet would force
that same coordinate to vanish, because `qs` is the coordinate facet omitting
source coordinate `0`.

Hence the fully nonlinear-confined branch of A19.60 can never lie on `qs`.
The two low-negative patterns retain the sharper facet lists from A19.62.
No balance, cocharacter, or Hessian-minor hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Pure-longitudinal complete nonlinear confinement can occur only on one of
the three transverse omitted-coordinate facets. -/
theorem pureLongitudinal_nonlinearConfined_facet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hpat : IsPureLongitudinalSmithPattern T.terminal.exponent)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    facet = .pr ∨ facet = .sp ∨ facet = .rq := by
  rcases T.pureLongitudinal_sourceSupport hpat with
    ⟨d, hd, hdeg, hd0, _hd1, _hd2, _hd3⟩
  have hfacet := hconfined d hd hdeg
  cases facet with
  | pr => exact Or.inl rfl
  | sp => exact Or.inr (Or.inl rfl)
  | rq => exact Or.inr (Or.inr rfl)
  | qs =>
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega

/-- Unified strict-low confinement exclusion: the marked `qs` facet is never
compatible with complete nonlinear source confinement. -/
theorem nonlinearConfined_facet_ne_qs
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    facet ≠ .qs := by
  intro hqs
  subst facet
  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · rcases T.pureLongitudinal_sourceSupport hpure with
      ⟨d, hd, hdeg, hd0, _hd1, _hd2, _hd3⟩
    have hfacet := hconfined d hd hdeg
    have hz : d (0 : Fin 4) = 0 := by
      simpa [HC4.Toric.OnFacet] using hfacet
    omega
  · rcases T.lowNegativeFirst_sourceSupport hfirst with
      ⟨d, hd, hdeg, hd0, _hd2⟩
    have hfacet := hconfined d hd hdeg
    have hz : d (0 : Fin 4) = 0 := by
      simpa [HC4.Toric.OnFacet] using hfacet
    omega
  · rcases T.lowNegativeSecond_sourceSupport hsecond with
      ⟨d, hd, hdeg, hd0, _hd1⟩
    have hfacet := hconfined d hd hdeg
    have hz : d (0 : Fin 4) = 0 := by
      simpa [HC4.Toric.OnFacet] using hfacet
    omega

/-- Pattern-sensitive complete list of surviving confinement facets. -/
theorem nonlinearConfined_facet_classification
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    (IsPureLongitudinalSmithPattern T.terminal.exponent ∧
        (facet = .pr ∨ facet = .sp ∨ facet = .rq)) ∨
      (IsLowNegativeFirstSmithPattern T.terminal.exponent ∧
        (facet = .pr ∨ facet = .rq)) ∨
      (IsLowNegativeSecondSmithPattern T.terminal.exponent ∧
        (facet = .sp ∨ facet = .rq)) := by
  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · exact Or.inl ⟨hpure, T.pureLongitudinal_nonlinearConfined_facet facet hpure hconfined⟩
  · exact Or.inr (Or.inl
      ⟨hfirst, T.lowNegativeFirst_nonlinearConfined_facet facet hfirst hconfined⟩)
  · exact Or.inr (Or.inr
      ⟨hsecond, T.lowNegativeSecond_nonlinearConfined_facet facet hsecond hconfined⟩)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
