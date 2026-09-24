import HC4.Newton.RankOneThreeSchur
import Mathlib.Tactic

/-!
# First-entry clock for a zero-constant 3x3 polynomial matrix

This is the 3x3 analogue of `ZeroSchurFirstEntryClock`.

Let S(X) be a 3x3 matrix over R[X] with S(0)=0 and suppose

    det S = Q(X) X^N,     Q(0) != 0.

Let e>0 be the least parameter order at which any matrix entry is nonzero.
Then every entry is divisible by X^e, so

    S = X^e S1
    det S = X^(3e) det S1.

Consequently

    3e <= N.

This file stops at that exact clock inequality.  Later geometry may inspect
the constant coefficient matrix of S1 and split by its rank.

No HC4 geometry appears here.
-/

namespace HC4.Newton

noncomputable section

open scoped Matrix

variable {R : Type*} [CommRing R]

/-- A 3x3 polynomial matrix with zero complete constant coefficient matrix. -/
structure ZeroThreeSchurSeries (R : Type*) [CommRing R] where
  matrix : Matrix (Fin 3) (Fin 3) (Polynomial R)
  coeff_zero : ∀ i j : Fin 3, (matrix i j).coeff 0 = 0

namespace ZeroThreeSchurSeries

/-- There is a positive parameter order at which some matrix entry is
nonzero. -/
def HasPositiveEntryLayer (S : ZeroThreeSchurSeries R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ i j : Fin 3, (S.matrix i j).coeff n ≠ 0

/-- Least positive order at which any entry of the 3x3 matrix is nonzero. -/
noncomputable def firstPositiveEntryOrder
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) : ℕ := by
  classical
  exact Nat.find h

theorem firstPositiveEntryOrder_spec
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    0 < S.firstPositiveEntryOrder h ∧
      ∃ i j : Fin 3,
        (S.matrix i j).coeff (S.firstPositiveEntryOrder h) ≠ 0 := by
  classical
  simpa [firstPositiveEntryOrder] using (Nat.find_spec h)

theorem firstPositiveEntryOrder_pos
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    0 < S.firstPositiveEntryOrder h :=
  (S.firstPositiveEntryOrder_spec h).1

/-- Every entry coefficient below the first positive common order vanishes. -/
theorem entry_coeff_eq_zero_of_lt_first
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3)
    {n : ℕ}
    (hn : n < S.firstPositiveEntryOrder h) :
    (S.matrix i j).coeff n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact S.coeff_zero i j
  · by_contra hcoeff
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hcandidate :
        0 < n ∧ ∃ i j : Fin 3, (S.matrix i j).coeff n ≠ 0 :=
      ⟨hpos, ⟨i, j, hcoeff⟩⟩
    have hmin : S.firstPositiveEntryOrder h ≤ n := by
      classical
      unfold firstPositiveEntryOrder
      exact Nat.find_min' h hcandidate
    omega

/-- The first common parameter power divides every matrix entry. -/
theorem firstFactor_dvd_entry
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) :
    (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ∣
      S.matrix i j := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact S.entry_coeff_eq_zero_of_lt_first h i j hn

/-- Entry of the matrix after removing the common first parameter power. -/
noncomputable def tailEntry
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) : Polynomial R :=
  Classical.choose (S.firstFactor_dvd_entry h i j)

/-- Normalised 3x3 matrix after removing the common first parameter power. -/
noncomputable def tailMatrix
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    Matrix (Fin 3) (Fin 3) (Polynomial R) :=
  fun i j => S.tailEntry h i j

theorem entry_eq_firstFactor_mul_tail
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3) :
    S.matrix i j =
      Polynomial.X ^ S.firstPositiveEntryOrder h *
        S.tailMatrix h i j := by
  exact Classical.choose_spec (S.firstFactor_dvd_entry h i j)

/-- Matrix-level common-factor identity. -/
theorem matrix_eq_firstFactor_smul_tail
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.matrix =
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) •
        S.tailMatrix h := by
  ext i j
  rw [S.entry_eq_firstFactor_mul_tail h i j]
  simp

/-- The coefficient at physical order `firstPositiveEntryOrder + r` is
exactly coefficient `r` of the normalised tail entry. -/
theorem entry_coeff_first_add_eq_tail
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3)
    (r : ℕ) :
    (S.matrix i j).coeff (S.firstPositiveEntryOrder h + r) =
      (S.tailMatrix h i j).coeff r := by
  rw [S.entry_eq_firstFactor_mul_tail h i j]
  rw [Polynomial.coeff_X_pow_mul']
  simp

/-- If one raw matrix entry first opens at a physical order `J` strictly
after the common first 3x3 order `q`, its normalised tail entry first opens
at the relative order `J-q`. -/
theorem tailEntry_gap_and_open_at_sub
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer)
    (i j : Fin 3)
    {q J : ℕ}
    (hfirst : S.firstPositiveEntryOrder h = q)
    (hqJ : q < J)
    (hgap : ∀ n : ℕ, n < J → (S.matrix i j).coeff n = 0)
    (hopen : (S.matrix i j).coeff J ≠ 0) :
    (∀ n : ℕ, n < J - q →
      (S.tailMatrix h i j).coeff n = 0) ∧
    (S.tailMatrix h i j).coeff (J - q) ≠ 0 := by
  constructor
  · intro n hn
    have hphys : q + n < J := by omega
    have ht := S.entry_coeff_first_add_eq_tail h i j n
    rw [hfirst] at ht
    rw [← ht]
    exact hgap (q + n) hphys
  · have hqle : q ≤ J := Nat.le_of_lt hqJ
    have hadd : q + (J - q) = J := Nat.add_sub_of_le hqle
    have ht := S.entry_coeff_first_add_eq_tail h i j (J - q)
    rw [hfirst, hadd] at ht
    intro hz
    apply hopen
    rw [ht]
    exact hz

/-- The determinant acquires exactly three copies of the common entry
factor. -/
theorem determinant_eq_firstFactor_cube_mul_tail
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    S.matrix.det =
      Polynomial.X ^ (3 * S.firstPositiveEntryOrder h) *
        (S.tailMatrix h).det := by
  rw [S.matrix_eq_firstFactor_smul_tail h]
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  have hpow :
      (Polynomial.X ^ S.firstPositiveEntryOrder h : Polynomial R) ^ 3 =
        Polynomial.X ^ (3 * S.firstPositiveEntryOrder h) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow]

/-- At least one constant coefficient of the normalised tail matrix is
nonzero. -/
theorem tail_constant_entry_ne_zero
    (S : ZeroThreeSchurSeries R)
    (h : S.HasPositiveEntryLayer) :
    ∃ i j : Fin 3, (S.tailMatrix h i j).coeff 0 ≠ 0 := by
  rcases (S.firstPositiveEntryOrder_spec h).2 with ⟨i, j, hij⟩
  refine ⟨i, j, ?_⟩
  have heq := S.entry_coeff_first_add_eq_tail h i j 0
  simp only [Nat.add_zero] at heq
  rw [← heq]
  exact hij

end ZeroThreeSchurSeries

/-- A zero-constant 3x3 series carrying one exact determinant clock up to a
clearing factor which is a unit at parameter zero. -/
structure ExactZeroThreeSchurClock (R : Type*) [CommRing R] where
  zeroSeries : ZeroThreeSchurSeries R
  clearingFactor : Polynomial R
  defect : ℕ
  clearingFactor_coeff_zero_ne_zero : clearingFactor.coeff 0 ≠ 0
  determinantFactor :
    zeroSeries.matrix.det =
      clearingFactor * Polynomial.X ^ defect

namespace ExactZeroThreeSchurClock

variable [IsDomain R]

/-- An exact nonzero determinant clock forces a genuine positive matrix
layer. -/
theorem hasPositiveEntryLayer
    (E : ExactZeroThreeSchurClock R) :
    E.zeroSeries.HasPositiveEntryLayer := by
  by_contra hnone
  have hmatrix : E.zeroSeries.matrix = 0 := by
    funext i j
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_zero]
    by_cases hn0 : n = 0
    · subst n
      exact E.zeroSeries.coeff_zero i j
    · by_contra hcoeff
      apply hnone
      exact ⟨n, Nat.pos_of_ne_zero hn0, i, j, hcoeff⟩
  have hdetzero : E.zeroSeries.matrix.det = 0 := by
    rw [hmatrix]
    simp
  have hcoeff :
      (E.clearingFactor * Polynomial.X ^ E.defect).coeff E.defect =
        E.clearingFactor.coeff 0 := by
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, ← E.determinantFactor, hdetzero]
  simp

/-- First positive common entry order of the exact 3x3 clock. -/
noncomputable def firstOrder
    (E : ExactZeroThreeSchurClock R) : ℕ :=
  E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer

theorem firstOrder_pos
    (E : ExactZeroThreeSchurClock R) :
    0 < E.firstOrder :=
  E.zeroSeries.firstPositiveEntryOrder_pos E.hasPositiveEntryLayer

/-- Exact determinant factorisation after removing the first common entry
order. -/
theorem determinant_eq_firstFactor_cube_mul_tail
    (E : ExactZeroThreeSchurClock R) :
    E.zeroSeries.matrix.det =
      Polynomial.X ^ (3 * E.firstOrder) *
        (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det := by
  simpa [firstOrder] using
    E.zeroSeries.determinant_eq_firstFactor_cube_mul_tail
      E.hasPositiveEntryLayer

/-- The first common 3x3 quotient order consumes at most one third of the
exact determinant clock. -/
theorem triple_firstOrder_le_defect
    (E : ExactZeroThreeSchurClock R) :
    3 * E.firstOrder ≤ E.defect := by
  by_contra hnot
  have hlt : E.defect < 3 * E.firstOrder := Nat.lt_of_not_ge hnot
  have hzero : E.zeroSeries.matrix.det.coeff E.defect = 0 := by
    rw [E.determinant_eq_firstFactor_cube_mul_tail]
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_lt hlt]
  have hcoeff :
      E.zeroSeries.matrix.det.coeff E.defect =
        E.clearingFactor.coeff 0 := by
    rw [E.determinantFactor]
    simpa using Polynomial.coeff_mul_X_pow E.clearingFactor E.defect 0
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff, hzero]

/-- The normalised first coefficient matrix is genuinely nonzero. -/
theorem tail_constant_entry_ne_zero
    (E : ExactZeroThreeSchurClock R) :
    ∃ i j : Fin 3,
      (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer i j).coeff 0 ≠ 0 := by
  exact E.zeroSeries.tail_constant_entry_ne_zero E.hasPositiveEntryLayer


/-- Residual determinant order after removing the common first 3x3 entry
factor. -/
def residualDefect
    (E : ExactZeroThreeSchurClock R) : ℕ :=
  E.defect - 3 * E.firstOrder

/-- Exact determinant clock on the normalised first-entry tail matrix. -/
theorem tail_determinantFactor
    (E : ExactZeroThreeSchurClock R) :
    (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det =
      E.clearingFactor * Polynomial.X ^ E.residualDefect := by
  have hle := E.triple_firstOrder_le_defect
  have hsplit :
      E.defect = 3 * E.firstOrder + E.residualDefect := by
    unfold residualDefect
    omega
  have hscaled :
      Polynomial.X ^ (3 * E.firstOrder) *
          (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det =
        Polynomial.X ^ (3 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
    calc
      Polynomial.X ^ (3 * E.firstOrder) *
            (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det =
          E.zeroSeries.matrix.det :=
        E.determinant_eq_firstFactor_cube_mul_tail.symm
      _ = E.clearingFactor * Polynomial.X ^ E.defect :=
        E.determinantFactor
      _ = Polynomial.X ^ (3 * E.firstOrder) *
          (E.clearingFactor * Polynomial.X ^ E.residualDefect) := by
        rw [hsplit, pow_add]
        ring
  exact mul_left_cancel₀
    (pow_ne_zero (3 * E.firstOrder) Polynomial.X_ne_zero)
    hscaled

/-- Constant coefficient matrix of the normalised first-entry tail. -/
noncomputable def tailConstantMatrix
    (E : ExactZeroThreeSchurClock R) :
    Matrix (Fin 3) (Fin 3) R :=
  fun i j =>
    (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer i j).coeff 0

/-- The tail constant matrix is nonzero. -/
theorem tailConstantMatrix_ne_zero
    (E : ExactZeroThreeSchurClock R) :
    E.tailConstantMatrix ≠ 0 := by
  rcases E.tail_constant_entry_ne_zero with ⟨i, j, hij⟩
  intro hz
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i j) hz
  simpa [tailConstantMatrix] using hij hentry

/-- If residual determinant order remains, the normalised first coefficient
matrix is singular. -/
theorem tailConstantMatrix_det_zero_of_residual_pos
    (E : ExactZeroThreeSchurClock R)
    (hres : 0 < E.residualDefect) :
    E.tailConstantMatrix.det = 0 := by
  have hcoeff :
      (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det.coeff 0 = 0 := by
    rw [E.tail_determinantFactor]
    rw [Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le.mpr hres]
  simpa [tailConstantMatrix, Matrix.det_fin_three,
    Polynomial.coeff_zero_eq_eval_zero] using hcoeff

/-- If no residual determinant order remains, the first coefficient matrix
is already nondegenerate. -/
theorem tailConstantMatrix_det_ne_zero_of_residual_zero
    (E : ExactZeroThreeSchurClock R)
    (hres : E.residualDefect = 0) :
    E.tailConstantMatrix.det ≠ 0 := by
  have hcoeff :
      (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer).det.coeff 0 =
        E.clearingFactor.coeff 0 := by
    rw [E.tail_determinantFactor, hres]
    simp
  intro hdet
  apply E.clearingFactor_coeff_zero_ne_zero
  rw [← hcoeff]
  simpa [tailConstantMatrix, Matrix.det_fin_three,
    Polynomial.coeff_zero_eq_eval_zero] using hdet

/-- A concrete nonzero 2x2 minor of a 3x3 matrix. -/
def HasTwoByTwoMinor
    (M : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∃ i j k l : Fin 3,
    M i j * M k l - M i l * M k j ≠ 0

/-- All 2x2 minors of a 3x3 matrix vanish. -/
def AllTwoByTwoMinorsZero
    (M : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j k l : Fin 3,
    M i j * M k l - M i l * M k j = 0

/-- Finite rank frontier of the normalised first 3x3 coefficient block. -/
inductive FirstTailRankFrontier
    (E : ExactZeroThreeSchurClock R) : Prop
  | determinantClosing
      (residual_eq_zero : E.residualDefect = 0)
      (det_ne_zero : E.tailConstantMatrix.det ≠ 0)
  | rankTwo
      (residual_pos : 0 < E.residualDefect)
      (minor : HasTwoByTwoMinor E.tailConstantMatrix)
  | rankOne
      (residual_pos : 0 < E.residualDefect)
      (allMinors : AllTwoByTwoMinorsZero E.tailConstantMatrix)
      (matrix_ne_zero : E.tailConstantMatrix ≠ 0)

/-- Every exact zero-constant 3x3 clock reaches the finite first-tail rank
frontier. -/
theorem firstTailRankFrontier
    (E : ExactZeroThreeSchurClock R) :
    E.FirstTailRankFrontier := by
  by_cases hres : E.residualDefect = 0
  · exact .determinantClosing hres
      (E.tailConstantMatrix_det_ne_zero_of_residual_zero hres)
  · have hrespos : 0 < E.residualDefect := Nat.pos_of_ne_zero hres
    by_cases hminor : HasTwoByTwoMinor E.tailConstantMatrix
    · exact .rankTwo hrespos hminor
    · have hall : AllTwoByTwoMinorsZero E.tailConstantMatrix := by
        intro i j k l
        by_contra hne
        exact hminor ⟨i, j, k, l, hne⟩
      exact .rankOne hrespos hall E.tailConstantMatrix_ne_zero

end ExactZeroThreeSchurClock

end

end HC4.Newton
