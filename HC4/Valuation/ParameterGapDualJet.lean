import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerCausality
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Parameter-gap dual jet over an arbitrary commutative coefficient ring

The direct-closing stack already uses the `(0,j)` coefficient jet over a field.
The planar-contact first variation needs the same elementary construction with
coefficient ring `Polynomial K`.  This file therefore records the genuinely
generic version once.

If every entry of a polynomial matrix has no positive parameter coefficient
below `j`, then

    p |-> (p_0, p_j)

is a ring homomorphism to the dual numbers.  Consequently the nilpotent part
of the determinant of the entrywise jet is exactly the `j`th coefficient of
the original determinant.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- At a positive gap order the endpoint coefficient of a product has only
the two boundary convolution terms. -/
theorem coeff_mul_at_gap_endpoint_commRing
    {j : ℕ} (hj : 0 < j)
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    (p * q).coeff j =
      p.coeff 0 * q.coeff j + p.coeff j * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal j
  let f : ℕ × ℕ → R := fun x => p.coeff x.1 * q.coeff x.2
  have h0j : (0, j) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hj0 : (j, 0) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hne : (j, 0) ≠ (0, j) := by
    intro h
    have hfirst : j = 0 := congrArg Prod.fst h
    omega
  have hj0erase : (j, 0) ∈ s.erase (0, j) :=
    Finset.mem_erase.mpr ⟨hne, hj0⟩
  have hrest :
      ∀ x ∈ (s.erase (0, j)).erase (j, 0), f x = 0 := by
    intro x hx
    have hxs : x ∈ s :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hxne0j : x ≠ (0, j) :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hxnej0 : x ≠ (j, 0) := (Finset.mem_erase.mp hx).1
    have hsum : x.1 + x.2 = j :=
      Finset.mem_antidiagonal.mp (by simpa [s] using hxs)
    have hx1pos : 0 < x.1 := by
      by_contra hnot
      have hx1zero : x.1 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx2eq : x.2 = j := by omega
      exact hxne0j (Prod.ext hx1zero hx2eq)
    have hx2pos : 0 < x.2 := by
      by_contra hnot
      have hx2zero : x.2 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx1eq : x.1 = j := by omega
      exact hxnej0 (Prod.ext hx1eq hx2zero)
    have hx1lt : x.1 < j := by omega
    have hx2lt : x.2 < j := by omega
    simp [f, hp x.1 hx1pos hx1lt, hq x.2 hx2pos hx2lt]
  have hsplit0 := Finset.add_sum_erase s f h0j
  have hsplitj := Finset.add_sum_erase (s.erase (0, j)) f hj0erase
  have hz : ∑ x ∈ (s.erase (0, j)).erase (j, 0), f x = 0 :=
    Finset.sum_eq_zero hrest
  change (∑ x ∈ s, f x) = _
  rw [← hsplit0, ← hsplitj, hz]
  simp [f]

/-- The `(0,j)` coefficient jet on the parameter-gap subring, over an
arbitrary commutative coefficient ring. -/
noncomputable def parameterGapDualJet
    (j : ℕ) (hj : 0 < j) :
    parameterGapSubring (R := R) j →+* DualNumber R where
  toFun p := (p.1.coeff 0, p.1.coeff j)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change (1 : Polynomial R).coeff j = 0
      rw [Polynomial.coeff_one]
      exact if_neg (Nat.ne_of_gt hj)
  map_add' p q := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp [Polynomial.coeff_mul]
    · simp only [TrivSqZeroExt.snd_mk, DualNumber.snd_mul,
        TrivSqZeroExt.fst_mk]
      exact coeff_mul_at_gap_endpoint_commRing hj p.property q.property

@[simp] theorem parameterGapDualJet_fst
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.fst (parameterGapDualJet (R := R) j hj p) = p.1.coeff 0 := by
  rfl

@[simp] theorem parameterGapDualJet_snd
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.snd (parameterGapDualJet (R := R) j hj p) = p.1.coeff j := by
  rfl

/-- Lift a polynomial matrix whose entries share the `j`-gap into the gap
subring. -/
noncomputable def matrixToParameterGapCommRing
    {j : ℕ}
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s)) :
    Matrix (Fin 4) (Fin 4) (parameterGapSubring (R := R) j) :=
  fun r s => ⟨M r s, hM r s⟩

/-- Entrywise `(0,j)` dual jet of a gap matrix. -/
noncomputable def matrixParameterGapDualJet
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s)) :
    Matrix (Fin 4) (Fin 4) (DualNumber R) :=
  (parameterGapDualJet (R := R) j hj).mapMatrix
    (matrixToParameterGapCommRing M hM)

@[simp] theorem matrixParameterGapDualJet_apply
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s))
    (r s : Fin 4) :
    matrixParameterGapDualJet hj M hM r s =
      ((M r s).coeff 0, (M r s).coeff j) := by
  rfl

/-- **Determinant coefficient bridge.**  The nilpotent determinant component
of the gap jet is exactly the selected coefficient of the original polynomial
matrix determinant. -/
theorem snd_det_matrixParameterGapDualJet
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s)) :
    TrivSqZeroExt.snd (matrixParameterGapDualJet hj M hM).det =
      M.det.coeff j := by
  let J := parameterGapDualJet (R := R) j hj
  let G := matrixToParameterGapCommRing M hM
  have hmap : J G.det = (J.mapMatrix G).det := J.map_det G
  have hsub := (parameterGapSubring (R := R) j).subtype.map_det G
  have hmatrix :
      (parameterGapSubring (R := R) j).subtype.mapMatrix G = M := by
    ext r s
    rfl
  rw [hmatrix] at hsub
  change TrivSqZeroExt.snd ((J.mapMatrix G).det) = M.det.coeff j
  rw [← hmap]
  change ((G.det : parameterGapSubring (R := R) j) : Polynomial R).coeff j = _
  simpa using congrArg (fun p : Polynomial R => p.coeff j) hsub

end

end HC4.Valuation
