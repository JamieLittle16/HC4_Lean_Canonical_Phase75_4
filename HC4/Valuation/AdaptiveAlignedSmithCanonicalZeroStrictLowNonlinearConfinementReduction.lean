import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import Mathlib.Tactic

/-!
# Pattern-sensitive reduction of complete nonlinear confinement

The final zero-strict-low frontier retains one static source-side alternative:
every nonlinear represented-source monomial lies on one coordinate facet.

The strict-low residual normal forms already provide actual nonlinear source
witnesses with explicit positive coordinates:

* pure-longitudinal: coordinate `0` is positive;
* low-negative-first: coordinates `0` and `2` are positive;
* low-negative-second: coordinates `0` and `1` are positive.

Therefore the confinement facet cannot omit any one of those positive
coordinates.  This gives the exact finite compatibility table below.  No
balance, top-face membership, auxiliary clock, repair progress, or JC2 input is
used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **Strict-low source confinement has only pattern-compatible facets.**

The only possible pairs are:

* `.rq` with any strict-low pattern;
* `.pr` with pure-longitudinal or low-negative-first;
* `.sp` with pure-longitudinal or low-negative-second.

In particular complete nonlinear confinement to `.qs` is impossible. -/
theorem nonlinearConfined_facetPattern_restriction
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    facet = .rq ∨
      (facet = .pr ∧
        (IsPureLongitudinalSmithPattern T.terminal.exponent ∨
          IsLowNegativeFirstSmithPattern T.terminal.exponent)) ∨
      (facet = .sp ∧
        (IsPureLongitudinalSmithPattern T.terminal.exponent ∨
          IsLowNegativeSecondSmithPattern T.terminal.exponent)) := by
  cases facet with
  | rq =>
      exact Or.inl rfl
  | pr =>
      right
      left
      refine ⟨rfl, ?_⟩
      rcases T.terminal.pattern with hpure | hfirst | hsecond
      · exact Or.inl hpure
      · exact Or.inr hfirst
      · rcases T.lowNegativeSecond_sourceSupport hsecond with
          ⟨d, hd, hdeg, _hd0, hd1⟩
        have hfacet := hconfined d hd hdeg
        have hz : d (1 : Fin 4) = 0 := by
          simpa [HC4.Toric.OnFacet] using hfacet
        omega
  | qs =>
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
  | sp =>
      right
      right
      refine ⟨rfl, ?_⟩
      rcases T.terminal.pattern with hpure | hfirst | hsecond
      · exact Or.inl hpure
      · rcases T.lowNegativeFirst_sourceSupport hfirst with
          ⟨d, hd, hdeg, _hd0, hd2⟩
        have hfacet := hconfined d hd hdeg
        have hz : d (2 : Fin 4) = 0 := by
          simpa [HC4.Toric.OnFacet] using hfacet
        omega
      · exact Or.inr hsecond

/-- Immediate corollary used by the `.qs` local dispatcher. -/
theorem nonlinearConfined_qs_impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet .qs (HC4.Polynomial.toToricExponent d)) :
    False := by
  have h := T.nonlinearConfined_facetPattern_restriction .qs hconfined
  rcases h with h | h | h
  · contradiction
  · exact (by
      rcases h with ⟨hfacet, _⟩
      contradiction)
  · exact (by
      rcases h with ⟨hfacet, _⟩
      contradiction)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
