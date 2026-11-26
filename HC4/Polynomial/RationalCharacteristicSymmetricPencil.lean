module

public import HC4.Polynomial.RationalCharacteristicConstants
public import Mathlib.Tactic

/-!
# Symmetric affine pencil rigidity

An elementary substitute for the coefficient-matrix rank split in the
rank-one rational characteristic argument. If a symmetric pencil A - T B
annihilates a polynomial vector whose components are linearly independent
over the coefficient field, both A and B vanish.

The proof compares two independent coefficient indices: symmetry moves
one coefficient step from the left to the right until the constant
coefficient equation kills the pairing. No Jordan basis, cross product,
Lueroth theorem, or geometric classification is needed for this lemma.
The separate construction of the rank-one parametrization and lifted
trace identity remains necessary.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

private theorem symmetric_dotProduct_move
    (A : Matrix ι ι K) (hA : A.transpose = A) (u v : ι → K) :
    u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

/-- The coefficient recurrence of a symmetric affine pencil forces
every pairing of coefficient vectors through B to vanish. If those
vectors have no nonzero constant annihilator, the pencil is zero. -/
theorem symmetric_affinePencil_eq_zero_of_coefficientRecurrence
    (A B : Matrix ι ι K) (hA : A.transpose = A) (hB : B.transpose = B)
    (u : ℕ → ι → K)
    (hzero : A *ᵥ u 0 = 0)
    (hstep : ∀ n : ℕ, A *ᵥ u (n + 1) = B *ᵥ u n)
    (hspan : ∀ b : ι → K, (∀ n : ℕ, b ⬝ᵥ u n = 0) → b = 0) :
    A = 0 ∧ B = 0 := by
  classical
  have hpair : ∀ m n : ℕ, u m ⬝ᵥ (B *ᵥ u n) = 0 := by
    intro m
    induction m with
    | zero =>
      intro n
      calc
        u 0 ⬝ᵥ (B *ᵥ u n) =
            u 0 ⬝ᵥ (A *ᵥ u (n + 1)) := by rw [hstep n]
        _ = (A *ᵥ u 0) ⬝ᵥ u (n + 1) :=
          symmetric_dotProduct_move A hA _ _
        _ = 0 := by rw [hzero]; simp [dotProduct]
    | succ m ih =>
      intro n
      calc
        u (m + 1) ⬝ᵥ (B *ᵥ u n) =
            u (m + 1) ⬝ᵥ (A *ᵥ u (n + 1)) := by rw [hstep n]
        _ = (A *ᵥ u (m + 1)) ⬝ᵥ u (n + 1) :=
          symmetric_dotProduct_move A hA _ _
        _ = (B *ᵥ u m) ⬝ᵥ u (n + 1) := by rw [hstep m]
        _ = u m ⬝ᵥ (B *ᵥ u (n + 1)) :=
          (symmetric_dotProduct_move B hB _ _).symm
        _ = 0 := ih (n + 1)
  have hBu (n : ℕ) : B *ᵥ u n = 0 := by
    apply hspan
    intro m
    rw [dotProduct_comm]
    exact hpair m n
  have hAu (n : ℕ) : A *ᵥ u n = 0 := by
    cases n with
    | zero => exact hzero
    | succ n =>
      rw [hstep n, hBu n]
  have hmat (M : Matrix ι ι K) (hM : ∀ n : ℕ, M *ᵥ u n = 0) :
      M = 0 := by
    apply Matrix.ext
    intro i j
    have hr : (fun k => M i k) = 0 := by
      apply hspan
      intro n
      exact congrFun (hM n) i
    exact congrFun hr j
  exact ⟨hmat A hAu, hmat B hBu⟩

/-- A symmetric affine matrix pencil cannot have a polynomial kernel
vector with ground-field linearly independent components unless the
pencil itself vanishes. The independence hypothesis is expressed
directly as absence of a constant relation on the components. -/
theorem symmetric_affinePencil_eq_zero_of_independent_polynomialKernel
    (A B : Matrix ι ι K) (hA : A.transpose = A) (hB : B.transpose = B)
    (U : ι → _root_.Polynomial K)
    (hker : ∀ i : ι,
      (∑ j : ι, _root_.Polynomial.C (A i j) * U j) =
        _root_.Polynomial.X * (∑ j : ι, _root_.Polynomial.C (B i j) * U j))
    (hind : ∀ b : ι → K,
      (∑ j : ι, _root_.Polynomial.C (b j) * U j) = 0 → b = 0) :
    A = 0 ∧ B = 0 := by
  classical
  let u : ℕ → ι → K := fun n j => (U j).coeff n
  apply symmetric_affinePencil_eq_zero_of_coefficientRecurrence A B hA hB u
  · funext i
    have h := congrArg (fun p : _root_.Polynomial K => p.coeff 0) (hker i)
    change (∑ j : ι, _root_.Polynomial.C (A i j) * U j).coeff 0 =
      (_root_.Polynomial.X * (∑ j : ι, _root_.Polynomial.C (B i j) * U j)).coeff 0 at h
    simp only [_root_.Polynomial.finset_sum_coeff, _root_.Polynomial.coeff_C_mul,
      _root_.Polynomial.coeff_X_mul_zero] at h
    exact h
  · intro n
    funext i
    have h := congrArg (fun p : _root_.Polynomial K => p.coeff (n + 1)) (hker i)
    change (∑ j : ι, _root_.Polynomial.C (A i j) * U j).coeff (n + 1) =
      (_root_.Polynomial.X * (∑ j : ι, _root_.Polynomial.C (B i j) * U j)).coeff (n + 1) at h
    simp only [_root_.Polynomial.coeff_X_mul, _root_.Polynomial.finset_sum_coeff,
      _root_.Polynomial.coeff_C_mul] at h
    exact h
  · intro b hb
    apply hind
    apply _root_.Polynomial.ext
    intro n
    simp only [_root_.Polynomial.finset_sum_coeff, _root_.Polynomial.coeff_C_mul,
      _root_.Polynomial.coeff_zero]
    exact hb n

end
end HC4.Polynomial.RankThreeCubic
