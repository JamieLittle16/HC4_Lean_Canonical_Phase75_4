import HC4.Newton.ScalarPivotThreeSchur
import Mathlib.Tactic

/-!
# A18.4.93: first-entry clock for a zero scalar-Schur three-block

This is the `3 x 3` analogue of `ZeroSchurFirstEntryClock`.

A symmetric polynomial matrix `S(tau)` whose complete constant matrix is zero
has a least positive order `e` at which some entry appears.  Every entry is
then divisible by `tau^e`; after removing that common factor from all nine
entries,

    det S = tau^(3e) det S_tail.

If the determinant also has the exact form

    det S = Q(tau) tau^Delta,   Q(0) != 0,

then `3e <= Delta`, and cancellation gives the exact residual clock

    det S_tail = Q(tau) tau^(Delta - 3e).

Thus the first scalar-Schur re-entry consumes a strictly positive integral
amount of the determinant clock.  No rational scale or geometric hypothesis
appears here.
-/

namespace HC4.Newton

noncomputable section

open scoped Matrix

universe u
variable {R : Type u} [CommRing R]

/-- A polynomial `3 x 3` matrix with identically zero constant matrix. -/
structure ZeroScalarSchurThreeSeries (R : Type*) [CommRing R] where
  series : Matrix (Fin 3) (Fin 3) (Polynomial R)
  constant_zero : ∀ i j : Fin 3, (series i j).coeff 0 = 0

namespace ZeroScalarSchurThreeSeries

/-- Positive parameter orders occurring in at least one matrix entry. -/
noncomputable def positiveEntryOrders
    (S : ZeroScalarSchurThreeSeries R) : Finset ℕ :=
  ((Finset.univ.biUnion fun i : Fin 3 =>
      Finset.univ.biUnion fun j : Fin 3 =>
        (S.series i j).support).filter fun n => 0 < n)

/-- At least one positive matrix layer occurs. -/
def HasPositiveEntryLayer (S : ZeroScalarSchurThreeSeries R) : Prop :=
  S.positiveEntryOrders.Nonempty

/-- Least positive order occurring in any entry. -/
noncomputable def firstPositiveEntryOrder
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) : ℕ :=
  S.positiveEntryOrders.min' h

 theorem firstPositiveEntryOrder_mem
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.firstPositiveEntryOrder h ∈ S.positiveEntryOrders := by
  exact Finset.min'_mem _ h

 theorem firstPositiveEntryOrder_pos
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    0 < S.firstPositiveEntryOrder h := by
  exact (Finset.mem_filter.mp (S.firstPositiveEntryOrder_mem h)).2

/-- Every coefficient below the first positive matrix order vanishes. -/
theorem entry_coeff_eq_zero_of_lt_first
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3)
    {n : ℕ}
    (hn : n < S.firstPositiveEntryOrder h) :
    (S.series i j).coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.constant_zero i j
  · by_contra hcoeff
    have hmem : n ∈ S.positiveEntryOrders := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ i, ?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ j, ?_⟩
        exact Polynomial.mem_support_iff.mpr hcoeff
      · omega
    have hle : S.firstPositiveEntryOrder h ≤ n :=
      Finset.min'_le S.positiveEntryOrders n hmem
    omega

/-- The selected first order contains an actually nonzero matrix entry. -/
theorem exists_entry_ne_zero_at_first
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    ∃ i j : Fin 3,
      (S.series i j).coeff (S.firstPositiveEntryOrder h) ≠ 0 := by
  have hm := S.firstPositiveEntryOrder_mem h
  have hu := (Finset.mem_filter.mp hm).1
  rcases Finset.mem_biUnion.mp hu with ⟨i, _hi, hrest⟩
  rcases Finset.mem_biUnion.mp hrest with ⟨j, _hj, hsupport⟩
  exact ⟨i, j, Polynomial.mem_support_iff.mp hsupport⟩

/-- If no positive layer exists, every matrix entry is the zero polynomial. -/
theorem series_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroScalarSchurThreeSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series = 0 := by
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro n
  change (S.series i j).coeff n = 0
  by_cases hn0 : n = 0
  · subst n
    exact S.constant_zero i j
  · by_contra hcoeff
    apply h
    refine ⟨n, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ j, ?_⟩
      exact Polynomial.mem_support_iff.mpr hcoeff
    · omega

/-- If the zero-constant matrix never moves, its determinant is zero. -/
theorem determinant_eq_zero_of_not_hasPositiveEntryLayer
    (S : ZeroScalarSchurThreeSeries R)
    (h : ¬ S.HasPositiveEntryLayer) :
    S.series.det = 0 := by
  rw [S.series_eq_zero_of_not_hasPositiveEntryLayer h]
  simp

/-- The first common power divides every matrix entry. -/
theorem firstFactor_dvd_entry
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) :
    (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ∣
      S.series i j := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact S.entry_coeff_eq_zero_of_lt_first h i j hn

/-- Entry of the normalised tail after removing the first common power. -/
noncomputable def tailEntry
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) : Polynomial R :=
  Classical.choose (S.firstFactor_dvd_entry h i j)

/-- The complete normalised tail matrix. -/
noncomputable def tailMatrix
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    Matrix (Fin 3) (Fin 3) (Polynomial R) :=
  fun i j => S.tailEntry h i j

 theorem entry_eq_firstFactor_mul_tail
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) :
    S.series i j =
      Polynomial.X ^ S.firstPositiveEntryOrder h * S.tailMatrix h i j := by
  exact Classical.choose_spec (S.firstFactor_dvd_entry h i j)

/-- First selected coefficient equals the constant coefficient of the
normalised tail entry. -/
theorem entry_coeff_first_eq_tail_zero
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) :
    (S.series i j).coeff (S.firstPositiveEntryOrder h) =
      (S.tailMatrix h i j).coeff 0 := by
  rw [S.entry_eq_firstFactor_mul_tail h i j]
  rw [Polynomial.coeff_X_pow_mul']
  simp

/-- The normalised tail has a nonzero constant matrix. -/
theorem tail_constantMatrix_ne_zero
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    (fun i j => (S.tailMatrix h i j).coeff 0) ≠
      (0 : Matrix (Fin 3) (Fin 3) R) := by
  rcases S.exists_entry_ne_zero_at_first h with ⟨i, j, hij⟩
  intro hzero
  have hz := congrFun (congrFun hzero i) j
  apply hij
  rw [S.entry_coeff_first_eq_tail_zero h i j]
  simpa using hz

/-- Removing the first common order removes its cube from the determinant. -/
theorem determinant_eq_firstFactor_cube_mul_tail
    (S : ZeroScalarSchurThreeSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.series.det =
      Polynomial.X ^ (3 * S.firstPositiveEntryOrder h) *
        (S.tailMatrix h).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp_rw [S.entry_eq_firstFactor_mul_tail h]
  have hpow :
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ^ 3 =
        Polynomial.X ^ (3 * S.firstPositiveEntryOrder h) := by
    calc
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ^ 3 =
          Polynomial.X ^ (S.firstPositiveEntryOrder h * 3) :=
        (pow_mul (Polynomial.X : Polynomial R)
          (S.firstPositiveEntryOrder h) 3).symm
      _ = Polynomial.X ^ (3 * S.firstPositiveEntryOrder h) := by
        congr 1
        omega
  rw [← hpow]
  ring

end ZeroScalarSchurThreeSeries

/-- Exact determinant clock for a zero-constant scalar-Schur `3 x 3` block. -/
structure ExactScalarSchurThreeClock (R : Type*) [CommRing R] where
  zeroSeries : ZeroScalarSchurThreeSeries R
  clearingFactor : Polynomial R
  defect : ℕ
  clearingFactor_coeff_zero_ne_zero : clearingFactor.coeff 0 ≠ 0
  determinantFactor :
    zeroSeries.series.det = clearingFactor * Polynomial.X ^ defect

namespace ExactScalarSchurThreeClock

variable [IsDomain R]

/-- A nonzero exact determinant clock forces a positive matrix layer. -/
theorem hasPositiveEntryLayer
    (E : ExactScalarSchurThreeClock R) :
    E.zeroSeries.HasPositiveEntryLayer := by
  by_contra hnone
  have hdet0 := E.zeroSeries.determinant_eq_zero_of_not_hasPositiveEntryLayer hnone
  have hcoeff :
      (E.clearingFactor * Polynomial.X ^ E.defect).coeff E.defect =
        E.clearingFactor.coeff 0 := by
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, ← E.determinantFactor, hdet0]
  simp

/-- First positive scalar-Schur matrix order. -/
noncomputable def firstOrder (E : ExactScalarSchurThreeClock R) : ℕ :=
  E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer

/-- Normalised tail matrix after removing the common first order. -/
noncomputable def tailMatrix
    (E : ExactScalarSchurThreeClock R) :
    Matrix (Fin 3) (Fin 3) (Polynomial R) :=
  E.zeroSeries.tailMatrix E.hasPositiveEntryLayer

 theorem firstOrder_pos (E : ExactScalarSchurThreeClock R) :
    0 < E.firstOrder :=
  E.zeroSeries.firstPositiveEntryOrder_pos E.hasPositiveEntryLayer

/-- Exact determinant factorisation after removing the first common order. -/
theorem determinant_eq_firstFactor_cube_mul_tail
    (E : ExactScalarSchurThreeClock R) :
    E.zeroSeries.series.det =
      Polynomial.X ^ (3 * E.firstOrder) * E.tailMatrix.det := by
  simpa [firstOrder, tailMatrix] using
    E.zeroSeries.determinant_eq_firstFactor_cube_mul_tail E.hasPositiveEntryLayer

/-- The first common order consumes at most one third of the determinant
order. -/
theorem thrice_firstOrder_le_defect
    (E : ExactScalarSchurThreeClock R) :
    3 * E.firstOrder ≤ E.defect := by
  by_contra hnot
  have hlt : E.defect < 3 * E.firstOrder := Nat.lt_of_not_ge hnot
  have hzero : E.zeroSeries.series.det.coeff E.defect = 0 := by
    rw [E.determinant_eq_firstFactor_cube_mul_tail]
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_lt hlt]
  have hcoeff :
      E.zeroSeries.series.det.coeff E.defect =
        E.clearingFactor.coeff 0 := by
    rw [E.determinantFactor]
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, hzero]

/-- Residual determinant order after the scalar-Schur first entry. -/
def residualDefect (E : ExactScalarSchurThreeClock R) : ℕ :=
  E.defect - 3 * E.firstOrder

/-- Cancelling the common first factor gives the exact determinant clock of
the normalised `3 x 3` tail. -/
theorem tail_determinantFactor
    (E : ExactScalarSchurThreeClock R) :
    E.tailMatrix.det =
      E.clearingFactor * Polynomial.X ^ E.residualDefect := by
  have hle := E.thrice_firstOrder_le_defect
  have hsplit : E.defect = 3 * E.firstOrder + E.residualDefect := by
    unfold residualDefect
    omega
  have hscaled :
      Polynomial.X ^ (3 * E.firstOrder) * E.tailMatrix.det =
        Polynomial.X ^ (3 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
    calc
      Polynomial.X ^ (3 * E.firstOrder) * E.tailMatrix.det =
          E.zeroSeries.series.det :=
        E.determinant_eq_firstFactor_cube_mul_tail.symm
      _ = E.clearingFactor * Polynomial.X ^ E.defect := E.determinantFactor
      _ = Polynomial.X ^ (3 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
        rw [hsplit, pow_add]
        ring
  exact mul_left_cancel₀
    (pow_ne_zero (3 * E.firstOrder) Polynomial.X_ne_zero)
    hscaled

/-- Constant coefficient matrix of the normalised tail. -/
noncomputable def tailConstantMatrix
    (E : ExactScalarSchurThreeClock R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => (E.tailMatrix i j).coeff 0

/-- The first tail constant matrix is nonzero. -/
theorem tailConstantMatrix_ne_zero
    (E : ExactScalarSchurThreeClock R) :
    E.tailConstantMatrix ≠ 0 := by
  simpa [tailConstantMatrix, tailMatrix] using
    E.zeroSeries.tail_constantMatrix_ne_zero E.hasPositiveEntryLayer

/-- Constant coefficient commutes with the `3 x 3` determinant. -/
theorem tailConstantMatrix_det
    (E : ExactScalarSchurThreeClock R) :
    E.tailConstantMatrix.det = E.tailMatrix.det.coeff 0 := by
  let f : Polynomial R →+* R := Polynomial.constantCoeff
  change (f.mapMatrix E.tailMatrix).det = f E.tailMatrix.det
  exact (f.map_det E.tailMatrix).symm

/-- Positive residual order forces determinant zero on the first tail
constant matrix. -/
theorem tailConstantMatrix_det_zero_of_residual_pos
    (E : ExactScalarSchurThreeClock R)
    (hres : 0 < E.residualDefect) :
    E.tailConstantMatrix.det = 0 := by
  rw [E.tailConstantMatrix_det, E.tail_determinantFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le.mpr hres]

/-- Residual order zero makes the first tail constant matrix nondegenerate. -/
theorem tailConstantMatrix_det_ne_zero_of_residual_zero
    (E : ExactScalarSchurThreeClock R)
    (hres : E.residualDefect = 0) :
    E.tailConstantMatrix.det ≠ 0 := by
  rw [E.tailConstantMatrix_det, E.tail_determinantFactor, hres]
  simpa using E.clearingFactor_coeff_zero_ne_zero

/-- The residual determinant clock is strictly smaller than the incoming one. -/
theorem residualDefect_lt
    (E : ExactScalarSchurThreeClock R) :
    E.residualDefect < E.defect := by
  unfold residualDefect
  have hpos := E.firstOrder_pos
  have hle := E.thrice_firstOrder_le_defect
  omega

end ExactScalarSchurThreeClock

end

end HC4.Newton