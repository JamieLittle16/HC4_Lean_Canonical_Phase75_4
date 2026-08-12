import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# Adaptive exact rank-one Schur clock

`FirstSchurDepartureBridge` contains a complete matrix-level Schur exhaustion
theory, but its strongest clock is indexed by the legacy
`CanonicalSmithDepartureFrontier`.  That legacy object carries full
parameter-family homogeneity and is therefore intentionally not used by the
new adaptive aligned-Smith programme.

This file extracts the *actual algebraic content* of that clock and indexes it
directly by an honest `AdaptiveAlignedSmithMinimalEndpoint`.

No homogeneity hypothesis is introduced.  The endpoint already retains:

* the genuine transformed polynomial family;
* its exact Hessian determinant clock;
* the nonlinear degree bound;
* the exact moving collision;
* the canonical right special point.

The only extra data required here are exactly the four-block Schur data
themselves.

Once this structure is constructed, the first positive transverse Schur order
is automatic and has only the two intended possibilities:

* preterminal: strict rank-one -> rank-two repair progress;
* closing: a nonzero transverse Schur coefficient occurs exactly at the
  determinant-closing exponent.

Thus the remaining blocker problem becomes a single honest geometric
construction theorem: build this adaptive Schur clock from the retained
blocker family.  No legacy homogeneous frontier is involved.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Exact denominator-cleared rank-one Schur clock over an honest adaptive
aligned endpoint.

This is the frontier-free analogue of `FrontierExactRankOneSchurClock`.
-/
structure AdaptiveAlignedExactRankOneSchurClock
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) where
  series : RankOneSchurSeries (MvPolynomial (Fin 4) K)
  leading_ne_zero : series.leading ≠ 0
  clearedFactor : Polynomial (MvPolynomial (Fin 4) K)
  clearedFactor_coeff_zero_ne_zero :
    clearedFactor.coeff 0 ≠ 0
  schurFactor :
    series.determinant =
      clearedFactor * Polynomial.X ^ E.defect

namespace AdaptiveAlignedExactRankOneSchurClock

/-- The exact determinant clock forces a genuine positive transverse Schur
layer. -/
theorem hasTransverse
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    S.series.HasPositiveTransverseLayer := by
  exact
    S.series.hasPositiveTransverseLayer_of_determinant_eq_factor_mul_X_pow
      S.clearedFactor E.defect S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- Canonical first positive transverse Schur order. -/
noncomputable def firstOrder
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) : ℕ :=
  S.series.firstPositiveTransverseOrder S.hasTransverse

theorem firstOrder_pos
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    0 < S.firstOrder := by
  exact
    S.series.firstPositiveTransverseOrder_pos S.hasTransverse

/-- The first transverse Schur order occurs no later than exact determinant
closure. -/
theorem firstOrder_le_defect
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    S.firstOrder ≤ E.defect := by
  exact
    S.series.firstPositiveTransverseOrder_le_of_determinant_eq_factor_mul_X_pow
      S.hasTransverse S.clearedFactor S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- Exact two-way timing split: preterminal or determinant-closing. -/
theorem firstOrder_preterminal_or_closing
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    S.firstOrder < E.defect ∨ S.firstOrder = E.defect := by
  exact lt_or_eq_of_le S.firstOrder_le_defect

/-- Package the selected order into the already-green matrix-valued
first-departure linearisation object. -/
noncomputable def firstDeparture
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    FirstRankOneSchurDeparture (MvPolynomial (Fin 4) K) where
  order := S.firstOrder
  leading := S.series.leading
  active := S.series.active
  offDiag := S.series.offDiag
  kernel := S.series.kernel
  order_pos := S.firstOrder_pos
  active_coeff_zero := S.series.active_coeff_zero
  offDiag_lower_zero := by
    intro n hn
    exact
      S.series.offDiag_coeff_eq_zero_of_lt_first
        S.hasTransverse hn
  kernel_lower_zero := by
    intro n hn
    exact
      S.series.kernel_coeff_eq_zero_of_lt_first
        S.hasTransverse hn

/-- Below determinant closure, the exact factorisation kills the selected
Schur determinant coefficient. -/
theorem determinant_coeff_firstOrder_eq_zero_of_preterminal
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect) :
    S.series.determinant.coeff S.firstOrder = 0 := by
  rw [S.schurFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_lt hpre]

/-- At a preterminal first transverse order the kernel entry vanishes by the
matrix first-layer linearisation and nonzero rank-one leading coefficient. -/
theorem kernel_coeff_firstOrder_eq_zero_of_preterminal
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect) :
    S.series.kernel.coeff S.firstOrder = 0 := by
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, firstDeparture] using
      S.firstDeparture.coeff_order_determinant
  have hprod :
      S.series.leading * S.series.kernel.coeff S.firstOrder = 0 := by
    rw [← hlin]
    exact
      S.determinant_coeff_firstOrder_eq_zero_of_preterminal hpre
  exact (mul_eq_zero.mp hprod).resolve_left S.leading_ne_zero

/-- The selected preterminal layer is therefore genuinely off-diagonal. -/
theorem offDiag_coeff_firstOrder_ne_zero_of_preterminal
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect) :
    S.series.offDiag.coeff S.firstOrder ≠ 0 := by
  rcases S.series.transverse_nonzero_at_first S.hasTransverse with hB | hC
  · exact hB
  · exact
      False.elim
        (hC (S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre))

/-- Matrix-level preterminal departure is a strict rank-one -> rank-two
repair step.  The determinant-clock family itself is unchanged. -/
theorem preterminal_rankTwoProgress
    {degreeCap complexity : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure := by
  have hprogress := rankOne_to_rankTwo_repairProgress complexity
  exact
    ⟨hprogress,
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre,
      repairState_measure_lt_of_progress hprogress⟩

/-- At determinant closure, the selected layer is still genuinely
transverse. -/
theorem closing_transverse_nonzero
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hclose : S.firstOrder = E.defect) :
    S.series.offDiag.coeff E.defect ≠ 0 ∨
      S.series.kernel.coeff E.defect ≠ 0 := by
  have h :=
    S.series.transverse_nonzero_at_first S.hasTransverse
  have hfirst :
      S.series.firstPositiveTransverseOrder S.hasTransverse =
        E.defect := by
    simpa only [firstOrder] using hclose
  rw [hfirst] at h
  exact h

/-- **Adaptive exact Schur exhaustion.**

Once the actual aligned endpoint supplies this exact matrix clock, there are
only two local outcomes:

* strict rank-two repair progress before determinant closure;
* a nonzero transverse Schur coefficient exactly at closure.

No full-family homogeneity and no legacy `CanonicalSmithDepartureFrontier`
appear in the statement.
-/
theorem rankTwoProgress_or_closing
    {degreeCap complexity : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
    (S.firstOrder = E.defect ∧
      (S.series.offDiag.coeff E.defect ≠ 0 ∨
       S.series.kernel.coeff E.defect ≠ 0)) := by
  rcases S.firstOrder_preterminal_or_closing with hpre | hclose
  · exact Or.inl (S.preterminal_rankTwoProgress hpre)
  · exact Or.inr ⟨hclose, S.closing_transverse_nonzero hclose⟩

end AdaptiveAlignedExactRankOneSchurClock

/-! ## Blocker-facing construction target -/

/-- The precise remaining geometric certificate for a canonical aligned
blocker.

The blocker endpoint already retains the honest family and determinant clock.
A certificate only has to construct the denominator-cleared rank-one Schur
series on that very endpoint.  Once supplied, the entire timing and repair
analysis is automatic via `rankTwoProgress_or_closing`.

Keeping this as a named `Prop` prevents the master proof from silently
assuming the missing four-block extraction.
-/
def HasAdaptiveAlignedBlockerExactSchurClock
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) : Prop :=
  Nonempty
    (AdaptiveAlignedExactRankOneSchurClock
      B.aligned.endpoint)

/-- A blocker carrying the exact adaptive Schur certificate has only the
preterminal strict-repair or determinant-closing alternatives. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rankTwoProgress_or_closing_of_exactSchurClock
    {degreeCap complexity : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (h : HasAdaptiveAlignedBlockerExactSchurClock B) :
    (∃ S : AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint,
      RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity) ∧
        S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure) ∨
    (∃ S : AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint,
      S.firstOrder = B.aligned.endpoint.defect ∧
        (S.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
         S.series.kernel.coeff B.aligned.endpoint.defect ≠ 0)) := by
  rcases h with ⟨S⟩
  rcases S.rankTwoProgress_or_closing (complexity := complexity) with
    hprogress | hclosing
  · exact Or.inl ⟨S, hprogress⟩
  · exact Or.inr ⟨S, hclosing⟩

end

end HC4.Valuation
