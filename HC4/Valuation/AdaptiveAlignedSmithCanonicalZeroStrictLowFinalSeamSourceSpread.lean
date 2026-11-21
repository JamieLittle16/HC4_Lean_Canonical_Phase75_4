
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamSingleAxis
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import Mathlib.Tactic

/-!
# G10: nonlinear source spread at the final seam

G9 proves that represented nonlinear source support cannot live on one
coordinate axis.  The strict-low residual support sharpens the remaining
finite alternative.

A final seam therefore has either an actual nonlinear monomial with two
distinct positive source coordinates, or actual pure nonlinear powers on two
different source axes.

The low-negative patterns are immediately mixed using their certified source
witnesses.  In the pure-longitudinal pattern, A19.63 supplies the pure
longitudinal power and G8 forces a nonlinear transverse escape.  If that escape
is not mixed, it must itself be a pure transverse-axis power.

No progress label, repair transition, terminal weight, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

def HasMixedNonlinearSourceMonomial
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∃ d ∈ T.representedSpecialFiber.support,
    3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      ∃ i j : Fin 4, i ≠ j ∧ 0 < d i ∧ 0 < d j

def HasTwoPureNonlinearAxes
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧
    ∃ ni nj : ℕ,
      3 ≤ ni ∧ 3 ≤ nj ∧
      Finsupp.single i ni ∈ T.representedSpecialFiber.support ∧
      Finsupp.single j nj ∈ T.representedSpecialFiber.support

theorem hasMixedNonlinearSourceMonomial_of_witness
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ T.representedSpecialFiber.support)
    (hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : 0 < d i) (hj : 0 < d j) :
    T.HasMixedNonlinearSourceMonomial :=
  ⟨d, hd, hdeg, i, j, hij, hi, hj⟩

private theorem exponent_eq_single_of_not_mixed
    (d : Fin 4 →₀ ℕ)
    (j : Fin 4)
    (hj : 0 < d j)
    (hnomix :
      ¬ ∃ i k : Fin 4, i ≠ k ∧ 0 < d i ∧ 0 < d k) :
    d = Finsupp.single j (d j) := by
  ext i
  by_cases hij : i = j
  · subst i
    simp
  · have hi : d i = 0 := by
      by_contra hine
      have hipos : 0 < d i := Nat.pos_of_ne_zero hine
      exact hnomix ⟨i, j, hij, hipos, hj⟩
    simp [hij, hi]

theorem mixedNonlinearSource_or_twoPureNonlinearAxes
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.HasMixedNonlinearSourceMonomial ∨ T.HasTwoPureNonlinearAxes := by
  rcases T.terminal.pattern with hpure | hfirst | hsecond
  · rcases T.pureLongitudinal_sourceSupport hpure with
      ⟨d0, hd0, hdeg0, hd00, hd01, hd02, hd03⟩

    by_cases hmixed : T.HasMixedNonlinearSourceMonomial
    · exact Or.inl hmixed
    · right

      have hescape :
          ∃ d ∈ T.representedSpecialFiber.support,
            3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
              (0 < d (1 : Fin 4) ∨
               0 < d (2 : Fin 4) ∨
               0 < d (3 : Fin 4)) := by
        by_contra hnone
        push_neg at hnone
        have hconf : T.RepresentedNonlinearSupportLongitudinal := by
          intro d hd hdeg
          have h := hnone d hd hdeg
          exact ⟨Nat.eq_zero_of_not_pos h.1,
            Nat.eq_zero_of_not_pos h.2.1,
            Nat.eq_zero_of_not_pos h.2.2⟩
        exact T.impossible_of_representedNonlinearSupportLongitudinal hconf

      rcases hescape with ⟨d, hd, hdeg, htrans⟩

      have hnomix :
          ¬ ∃ i j : Fin 4, i ≠ j ∧ 0 < d i ∧ 0 < d j := by
        intro h
        exact hmixed ⟨d, hd, hdeg, h⟩

      have hd0zero : d (0 : Fin 4) = 0 := by
        by_contra hne
        have h0pos : 0 < d (0 : Fin 4) := Nat.pos_of_ne_zero hne
        rcases htrans with h1 | h2 | h3
        · exact hnomix ⟨0, 1, by decide, h0pos, h1⟩
        · exact hnomix ⟨0, 2, by decide, h0pos, h2⟩
        · exact hnomix ⟨0, 3, by decide, h0pos, h3⟩

      have hd0form :
          d0 = Finsupp.single (0 : Fin 4) (d0 0) := by
        ext i
        fin_cases i
        · simp
        · simp [hd01]
        · simp [hd02]
        · simp [hd03]

      rcases htrans with h1 | h2 | h3
      · have hdform :=
          exponent_eq_single_of_not_mixed d (1 : Fin 4) h1 hnomix
        refine ⟨0, 1, by decide, d0 0, d 1, ?_, ?_, ?_, ?_⟩
        · have h := hdeg0
          rw [hd0form] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · have h := hdeg
          rw [hdform] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · simpa [hd0form] using hd0
        · simpa [hdform] using hd
      · have hdform :=
          exponent_eq_single_of_not_mixed d (2 : Fin 4) h2 hnomix
        refine ⟨0, 2, by decide, d0 0, d 2, ?_, ?_, ?_, ?_⟩
        · have h := hdeg0
          rw [hd0form] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · have h := hdeg
          rw [hdform] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · simpa [hd0form] using hd0
        · simpa [hdform] using hd
      · have hdform :=
          exponent_eq_single_of_not_mixed d (3 : Fin 4) h3 hnomix
        refine ⟨0, 3, by decide, d0 0, d 3, ?_, ?_, ?_, ?_⟩
        · have h := hdeg0
          rw [hd0form] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · have h := hdeg
          rw [hdform] at h
          simpa [HC4.Polynomial.ordinaryDegree4] using h
        · simpa [hd0form] using hd0
        · simpa [hdform] using hd

  · rcases T.lowNegativeFirst_sourceSupport hfirst with
      ⟨d, hd, hdeg, h0, h2⟩
    exact Or.inl
      (T.hasMixedNonlinearSourceMonomial_of_witness
        hd hdeg (i := 0) (j := 2) (by decide) h0 (by omega))

  · rcases T.lowNegativeSecond_sourceSupport hsecond with
      ⟨d, hd, hdeg, h0, h1⟩
    exact Or.inl
      (T.hasMixedNonlinearSourceMonomial_of_witness
        hd hdeg (i := 0) (j := 1) (by decide) h0 (by omega))

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
