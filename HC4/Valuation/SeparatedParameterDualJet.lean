import HC4.Valuation.ParameterGapDualJet
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A separated parameter coefficient dual jet

Suppose a polynomial has no positive coefficients below `r`, and choose an
order `N` with

    r < N < 2*r.

Then the coefficient of a product at order `N` has only the two boundary
convolutions `(0,N)` and `(N,0)`: if both indices were positive, the gap would
force both to be at least `r`, contradicting `N < 2*r`.

Consequently

    p |-> (p_0,p_N)

is a ring homomorphism from the existing parameter-gap subring to dual
numbers.  This is the exact coefficient extractor needed for a three-layer
pencil whose terminal order lies strictly between the first and second
multiples of its first positive order.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- At a separated order `r < N < 2r`, only the boundary convolution terms
survive. -/
theorem coeff_mul_at_separated_endpoint_commRing
    {r N : ℕ} (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r)
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow r p)
    (hq : HasNoPositiveParameterCoeffBelow r q) :
    (p * q).coeff N =
      p.coeff 0 * q.coeff N + p.coeff N * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal N
  let f : ℕ × ℕ → R := fun x => p.coeff x.1 * q.coeff x.2
  have h0N : (0, N) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hN0 : (N, 0) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hne : (N, 0) ≠ (0, N) := by
    intro h
    have hfirst : N = 0 := congrArg Prod.fst h
    omega
  have hN0erase : (N, 0) ∈ s.erase (0, N) :=
    Finset.mem_erase.mpr ⟨hne, hN0⟩
  have hrest :
      ∀ x ∈ (s.erase (0, N)).erase (N, 0), f x = 0 := by
    intro x hx
    have hx1 := Finset.mem_of_mem_erase hx
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx1
    have hxneN0 : x ≠ (N, 0) := (Finset.mem_erase.mp hx).1
    have hxne0N : x ≠ (0, N) := (Finset.mem_erase.mp hx1).1
    have hsum : x.1 + x.2 = N :=
      Finset.mem_antidiagonal.mp (by simpa [s] using hxs)
    have hx1pos : 0 < x.1 := by
      by_contra hnot
      have hx1zero : x.1 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx2eq : x.2 = N := by omega
      exact hxne0N (Prod.ext hx1zero hx2eq)
    have hx2pos : 0 < x.2 := by
      by_contra hnot
      have hx2zero : x.2 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx1eq : x.1 = N := by omega
      exact hxneN0 (Prod.ext hx1eq hx2zero)
    by_cases hx1lt : x.1 < r
    · simp [f, hp x.1 hx1pos hx1lt]
    · have hx1ge : r ≤ x.1 := Nat.le_of_not_gt hx1lt
      have hx2lt : x.2 < r := by omega
      simp [f, hq x.2 hx2pos hx2lt]
  have hsplit0 := Finset.add_sum_erase s f h0N
  have hsplitN := Finset.add_sum_erase (s.erase (0, N)) f hN0erase
  have hz : ∑ x ∈ (s.erase (0, N)).erase (N, 0), f x = 0 :=
    Finset.sum_eq_zero hrest
  change (∑ x ∈ s, f x) = _
  rw [← hsplit0, ← hsplitN, hz]
  simp [f]

/-- The `(0,N)` dual jet on polynomials with a positive coefficient gap `r`,
valid when `r < N < 2r`. -/
noncomputable def separatedParameterDualJet
    (r N : ℕ) (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r) :
    parameterGapSubring (R := R) r →+* DualNumber R where
  toFun p := (p.1.coeff 0, p.1.coeff N)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change (1 : Polynomial R).coeff N = 0
      rw [Polynomial.coeff_one]
      have hN0 : N ≠ 0 := by omega
      exact if_neg hN0
  map_add' p q := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp [Polynomial.mul_coeff_zero]
    · simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mk,
        TrivSqZeroExt.snd_mk]
      exact coeff_mul_at_separated_endpoint_commRing
        (R := R) hr hrN hN2r p.property q.property

/-- Entrywise separated `(0,N)` jet of a matrix carrying an `r`-gap. -/
noncomputable def matrixSeparatedParameterDualJet
    {r N : ℕ} (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow r (M i j)) :
    Matrix (Fin 4) (Fin 4) (DualNumber R) :=
  (separatedParameterDualJet (R := R) r N hr hrN hN2r).mapMatrix
    (matrixToParameterGapCommRing M hM)

@[simp] theorem matrixSeparatedParameterDualJet_apply
    {r N : ℕ} (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow r (M i j))
    (i j : Fin 4) :
    matrixSeparatedParameterDualJet hr hrN hN2r M hM i j =
      ((M i j).coeff 0, (M i j).coeff N) := by
  rfl

/-- **Separated determinant coefficient bridge.** -/
theorem snd_det_matrixSeparatedParameterDualJet
    {r N : ℕ} (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow r (M i j)) :
    TrivSqZeroExt.snd
      (matrixSeparatedParameterDualJet hr hrN hN2r M hM).det =
      M.det.coeff N := by
  let J := separatedParameterDualJet (R := R) r N hr hrN hN2r
  let G := matrixToParameterGapCommRing M hM
  have hmap : J G.det = (J.mapMatrix G).det := J.map_det G
  have hsub := (parameterGapSubring (R := R) r).subtype.map_det G
  have hmatrix :
      (parameterGapSubring (R := R) r).subtype.mapMatrix G = M := by
    ext i j
    rfl
  rw [hmatrix] at hsub
  change TrivSqZeroExt.snd ((J.mapMatrix G).det) = M.det.coeff N
  rw [← hmap]
  change ((G.det : parameterGapSubring (R := R) r) : Polynomial R).coeff N = _
  simpa using congrArg (fun p : Polynomial R => p.coeff N) hsub

end

end HC4.Valuation
