import HC4.Newton.LinearPowerRecurrenceClassification
import Mathlib.Tactic

/-!
# Frozen transverse slices of an MvPolynomial

Phase 91.9 classifies every scalar sequence satisfying the finite
directional recurrence as a scalar multiple of the coefficient profile of

    (v*X - u*Y)^n.

This file connects that scalar theorem back to an actual `MvPolynomial`.

Fix two transverse variables `i,j` and freeze all other exponents in a
multi-index `r` with

    r i = 0,   r j = 0.

The degree-`n` transverse slice is

    d_k = r + k*e_i + (n-k)*e_j,

and its coefficient sequence is

    c(k) = coeff d_k F.

For `k < n`, apply the Phase 91.6 directional coefficient recurrence at

    m_k = r + k*e_i + (n-1-k)*e_j.

Then

    m_k + e_i = d_(k+1),
    m_k + e_j = d_k,

so the abstract recurrence becomes exactly

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0.

Phase 91.9 therefore classifies every frozen external slice of `F`.
This is the coefficientwise content of the desired
`a(X) * L(Y)^n` normal form.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Multi-index of the degree-`n` transverse slice with frozen external
multi-index `r`. -/
def transverseSliceIndex
    (r : σ →₀ ℕ)
    (i j : σ)
    (n k : ℕ) :
    σ →₀ ℕ :=
  r + Finsupp.single i k + Finsupp.single j (n - k)

/-- Coefficient sequence of a frozen degree-`n` transverse slice. -/
def transverseSliceCoeff
    (F : MvPolynomial σ K)
    (r : σ →₀ ℕ)
    (i j : σ)
    (n k : ℕ) : K :=
  MvPolynomial.coeff (transverseSliceIndex r i j n k) F

/-- First transverse exponent of a slice index when the frozen base has no
`i`-component. -/
theorem transverseSliceIndex_apply_first
    {r : σ →₀ ℕ} {i j : σ}
    (hij : i ≠ j)
    (hri : r i = 0)
    (n k : ℕ) :
    transverseSliceIndex r i j n k i = k := by
  simp [transverseSliceIndex, hri, hij, Ne.symm hij]

/-- Second transverse exponent of a slice index when the frozen base has no
`j`-component. -/
theorem transverseSliceIndex_apply_second
    {r : σ →₀ ℕ} {i j : σ}
    (hij : i ≠ j)
    (hrj : r j = 0)
    (n k : ℕ) :
    transverseSliceIndex r i j n k j = n - k := by
  simp [transverseSliceIndex, hrj, hij, Ne.symm hij]

/-- At recurrence step `k<n`, adding `e_i` to the lower degree-`n-1`
index gives the next degree-`n` slice index. -/
theorem transverseSliceIndex_lower_add_first
    {r : σ →₀ ℕ} {i j : σ}
    (hij : i ≠ j)
    (hri : r i = 0)
    (hrj : r j = 0)
    {n k : ℕ}
    (hk : k < n) :
    transverseSliceIndex r i j (n - 1) k +
        Finsupp.single i 1 =
      transverseSliceIndex r i j n (k + 1) := by
  classical
  ext x
  by_cases hxi : x = i
  · subst x
    simp [transverseSliceIndex, hri, hij, Ne.symm hij]
  · by_cases hxj : x = j
    · subst x
      simp [transverseSliceIndex, hrj, hij, Ne.symm hij]
      omega
    · simp [transverseSliceIndex, Finsupp.single_apply, hxi, hxj]

/-- At recurrence step `k<n`, adding `e_j` to the lower degree-`n-1`
index recovers the current degree-`n` slice index. -/
theorem transverseSliceIndex_lower_add_second
    {r : σ →₀ ℕ} {i j : σ}
    (hij : i ≠ j)
    (hri : r i = 0)
    (hrj : r j = 0)
    {n k : ℕ}
    (hk : k < n) :
    transverseSliceIndex r i j (n - 1) k +
        Finsupp.single j 1 =
      transverseSliceIndex r i j n k := by
  classical
  ext x
  by_cases hxi : x = i
  · subst x
    simp [transverseSliceIndex, hri, hij, Ne.symm hij]
  · by_cases hxj : x = j
    · subst x
      simp [transverseSliceIndex, hrj, hij, Ne.symm hij]
      omega
    · simp [transverseSliceIndex, Finsupp.single_apply, hxi, hxj]

/-- **MvPolynomial slice recurrence.**
A vanishing fixed directional derivative forces every frozen external
degree-`n` coefficient slice to satisfy the finite recurrence of
Phase 91.7. -/
theorem transverseSlice_satisfiesDirectionalRecurrence
    (u v : K)
    {i j : σ}
    (hij : i ≠ j)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (r : σ →₀ ℕ)
    (hri : r i = 0)
    (hrj : r j = 0)
    (n : ℕ) :
    SatisfiesDirectionalRecurrence
      u v n (transverseSliceCoeff F r i j n) := by
  intro k hk
  let m : σ →₀ ℕ :=
    transverseSliceIndex r i j (n - 1) k
  have hrec :=
    directionalCoefficient_recurrence_assoc
      u v i j F hdir m
  have hmi : m i = k := by
    dsimp [m]
    exact transverseSliceIndex_apply_first
      hij hri (n - 1) k
  have hmj : m j = (n - 1) - k := by
    dsimp [m]
    exact transverseSliceIndex_apply_second
      hij hrj (n - 1) k
  have hfirst :
      m + Finsupp.single i 1 =
        transverseSliceIndex r i j n (k + 1) := by
    dsimp [m]
    exact transverseSliceIndex_lower_add_first
      hij hri hrj hk
  have hsecond :
      m + Finsupp.single j 1 =
        transverseSliceIndex r i j n k := by
    dsimp [m]
    exact transverseSliceIndex_lower_add_second
      hij hri hrj hk
  have hmult :
      ((n - 1) - k) + 1 = n - k := by
    omega
  rw [hmi, hmj, hfirst, hsecond, hmult] at hrec
  simpa [transverseSliceCoeff] using hrec

/-- **Frozen-slice linear-power classification.**
In characteristic zero, every frozen degree-`n` transverse slice of a
polynomial annihilated by `D_(u,v)` is the scalar multiple of the
coefficient profile of `(v*X-u*Y)^n`. -/
theorem transverseSlice_eq_linearPowerProfile
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (r : σ →₀ ℕ)
    (hri : r i = 0)
    (hrj : r j = 0)
    (n : ℕ) :
    ∀ k, k ≤ n ->
      transverseSliceCoeff F r i j n k =
        linearPowerScalar u n
            (transverseSliceCoeff F r i j n) *
          linearPowerProfile u v n k := by
  apply directionalRecurrence_eq_linearPowerProfile
    u v hu n (transverseSliceCoeff F r i j n)
  exact transverseSlice_satisfiesDirectionalRecurrence
    u v hij F hdir r hri hrj n

/-- Expanded binomial version of the frozen-slice classification. -/
theorem transverseSlice_eq_binomialProfile
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (r : σ →₀ ℕ)
    (hri : r i = 0)
    (hrj : r j = 0)
    (n : ℕ) :
    ∀ k, k ≤ n ->
      transverseSliceCoeff F r i j n k =
        linearPowerScalar u n
            (transverseSliceCoeff F r i j n) *
          ((Nat.choose n k : ℕ) : K) *
          v ^ k *
          (-u) ^ (n - k) := by
  intro k hk
  rw [transverseSlice_eq_linearPowerProfile
    u v hu hij F hdir r hri hrj n k hk]
  unfold linearPowerProfile
  ring

end

end HC4.Newton
