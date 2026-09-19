import HC4.Valuation.ParameterGapDualJet
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Intermediate coefficient jet below twice the first parameter gap

If a polynomial has no positive coefficient below `q` and

    q < N < 2*q,

then the coefficient at `N` of a product has only the two boundary
convolution terms.  Hence `p ↦ (p₀,p_N)` is again a dual-number ring
homomorphism on the `q`-gap subring.  This is useful when a three-layer family
has its middle layer at `q` and its far endpoint at an intermediate order
`N < 2q`.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- Below twice the first positive gap, only the boundary convolution terms
can contribute. -/
theorem coeff_mul_at_intermediate_gap_endpoint_commRing
    {q N : ℕ} (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    {p r : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow q p)
    (hr : HasNoPositiveParameterCoeffBelow q r) :
    (p * r).coeff N =
      p.coeff 0 * r.coeff N + p.coeff N * r.coeff 0 := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal N
  let f : ℕ × ℕ → R := fun x => p.coeff x.1 * r.coeff x.2
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
    have hxs : x ∈ s :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hxne0N : x ≠ (0, N) :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hxneN0 : x ≠ (N, 0) := (Finset.mem_erase.mp hx).1
    have hsum : x.1 + x.2 = N :=
      Finset.mem_antidiagonal.mp (by simpa [s] using hxs)
    have hx1pos : 0 < x.1 := by
      by_contra hn
      have hz : x.1 = 0 := Nat.eq_zero_of_not_pos hn
      have h2 : x.2 = N := by omega
      exact hxne0N (Prod.ext hz h2)
    have hx2pos : 0 < x.2 := by
      by_contra hn
      have hz : x.2 = 0 := Nat.eq_zero_of_not_pos hn
      have h1 : x.1 = N := by omega
      exact hxneN0 (Prod.ext h1 hz)
    by_cases hx1lt : x.1 < q
    · simp [f, hp x.1 hx1pos hx1lt]
    by_cases hx2lt : x.2 < q
    · simp [f, hr x.2 hx2pos hx2lt]
    have hx1ge : q ≤ x.1 := Nat.le_of_not_gt hx1lt
    have hx2ge : q ≤ x.2 := Nat.le_of_not_gt hx2lt
    exfalso
    omega
  have hsplit0 := Finset.add_sum_erase s f h0N
  have hsplitN := Finset.add_sum_erase (s.erase (0, N)) f hN0erase
  have hz : ∑ x ∈ (s.erase (0, N)).erase (N, 0), f x = 0 :=
    Finset.sum_eq_zero hrest
  change (∑ x ∈ s, f x) = _
  rw [← hsplit0, ← hsplitN, hz]
  simp [f]

/-- The `(0,N)` jet on the `q`-gap subring when `N < 2q`. -/
noncomputable def parameterGapIntermediateDualJet
    (q N : ℕ) (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q) :
    parameterGapSubring (R := R) q →+* DualNumber R where
  toFun p := (p.1.coeff 0, p.1.coeff N)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change (1 : Polynomial R).coeff N = 0
      rw [Polynomial.coeff_one]
      exact if_neg (by omega)
  map_add' p r := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' p r := by
    apply TrivSqZeroExt.ext
    · simp [Polynomial.coeff_mul]
    · simp only [TrivSqZeroExt.snd_mk, DualNumber.snd_mul,
        TrivSqZeroExt.fst_mk]
      exact coeff_mul_at_intermediate_gap_endpoint_commRing
        hq hqN hN2q p.property r.property

/-- Entrywise intermediate dual jet. -/
noncomputable def matrixParameterGapIntermediateDualJet
    {q N : ℕ} (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow q (M i j)) :
    Matrix (Fin 4) (Fin 4) (DualNumber R) :=
  (parameterGapIntermediateDualJet (R := R) q N hq hqN hN2q).mapMatrix
    (matrixToParameterGapCommRing M hM)

@[simp] theorem matrixParameterGapIntermediateDualJet_apply
    {q N : ℕ} (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow q (M i j))
    (i j : Fin 4) :
    matrixParameterGapIntermediateDualJet hq hqN hN2q M hM i j =
      ((M i j).coeff 0, (M i j).coeff N) := by
  rfl

/-- Determinant coefficient bridge at an intermediate order `N < 2q`. -/
theorem snd_det_matrixParameterGapIntermediateDualJet
    {q N : ℕ} (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i j, HasNoPositiveParameterCoeffBelow q (M i j)) :
    TrivSqZeroExt.snd
      (matrixParameterGapIntermediateDualJet hq hqN hN2q M hM).det =
      M.det.coeff N := by
  let J := parameterGapIntermediateDualJet (R := R) q N hq hqN hN2q
  let G := matrixToParameterGapCommRing M hM
  have hmap : J G.det = (J.mapMatrix G).det := J.map_det G
  have hsub := (parameterGapSubring (R := R) q).subtype.map_det G
  have hmatrix :
      (parameterGapSubring (R := R) q).subtype.mapMatrix G = M := by
    ext i j
    rfl
  rw [hmatrix] at hsub
  change TrivSqZeroExt.snd ((J.mapMatrix G).det) = M.det.coeff N
  rw [← hmap]
  change ((G.det : parameterGapSubring (R := R) q) : Polynomial R).coeff N = _
  simpa using congrArg (fun p : Polynomial R => p.coeff N) hsub

end

end HC4.Valuation
