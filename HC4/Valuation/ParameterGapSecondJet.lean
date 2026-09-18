import HC4.Valuation.ParameterGapDualJet
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Second-order parameter-gap jet

`ParameterGapDualJet` records coefficients `0` and `j`.  For the final A19
finite-staircase obstruction we need the next convolution endpoint as well.
If a polynomial has no positive coefficient below `j`, then at order `2*j`
there are only three possible product convolutions:

    (0,2j), (j,j), (2j,0).

This gives a second-order jet into nested dual numbers.  Write `e` for the
inner nilpotent and `d` for the outer nilpotent; the element

    ((a,b),(b,2*c))

represents `a + b(e+d) + 2c ed`, where `(e+d)^2 = 2ed` and
`(e+d)^3 = 0`.  The image is multiplicatively closed precisely by the gap
convolution formula above.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {R : Type u} [CommRing R]

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-- At twice a positive gap order, only the two boundary terms and the middle
`(j,j)` convolution survive. -/
theorem coeff_mul_at_twice_gap_endpoint_commRing
    {j : ℕ} (hj : 0 < j)
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    (p * q).coeff (2 * j) =
      p.coeff 0 * q.coeff (2 * j) +
        p.coeff j * q.coeff j +
        p.coeff (2 * j) * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal (2 * j)
  let f : ℕ × ℕ → R := fun x => p.coeff x.1 * q.coeff x.2
  have h0 : (0, 2 * j) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hjj : (j, j) ∈ s := by
    simp [s, Finset.mem_antidiagonal, two_mul]
  have h2 : (2 * j, 0) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hne0j : (j, j) ≠ (0, 2 * j) := by
    intro h
    have hz : j = 0 := congrArg Prod.fst h
    omega
  have hne20 : (2 * j, 0) ≠ (0, 2 * j) := by
    intro h
    have hz : 2 * j = 0 := congrArg Prod.fst h
    omega
  have hne2j : (2 * j, 0) ≠ (j, j) := by
    intro h
    have hz : 2 * j = j := congrArg Prod.fst h
    omega
  have hjErase : (j, j) ∈ s.erase (0, 2 * j) :=
    Finset.mem_erase.mpr ⟨hne0j, hjj⟩
  have h2Erase : (2 * j, 0) ∈ (s.erase (0, 2 * j)).erase (j, j) := by
    apply Finset.mem_erase.mpr
    refine ⟨hne2j, ?_⟩
    exact Finset.mem_erase.mpr ⟨hne20, h2⟩
  have hrest :
      ∀ x ∈ ((s.erase (0, 2 * j)).erase (j, j)).erase (2 * j, 0),
        f x = 0 := by
    intro x hx
    have hx1 := Finset.mem_of_mem_erase hx
    have hx2 := Finset.mem_of_mem_erase hx1
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx2
    have hxne2 : x ≠ (2 * j, 0) := (Finset.mem_erase.mp hx).1
    have hxnej : x ≠ (j, j) := (Finset.mem_erase.mp hx1).1
    have hxne0 : x ≠ (0, 2 * j) := (Finset.mem_erase.mp hx2).1
    have hsum : x.1 + x.2 = 2 * j :=
      Finset.mem_antidiagonal.mp (by simpa [s] using hxs)
    have hx1pos : 0 < x.1 := by
      by_contra hn
      have hz : x.1 = 0 := Nat.eq_zero_of_not_pos hn
      have h2j : x.2 = 2 * j := by omega
      exact hxne0 (Prod.ext hz h2j)
    have hx2pos : 0 < x.2 := by
      by_contra hn
      have hz : x.2 = 0 := Nat.eq_zero_of_not_pos hn
      have h2j : x.1 = 2 * j := by omega
      exact hxne2 (Prod.ext h2j hz)
    by_cases hx1lt : x.1 < j
    · simp [f, hp x.1 hx1pos hx1lt]
    · have hx1ge : j ≤ x.1 := Nat.le_of_not_gt hx1lt
      by_cases hx1eq : x.1 = j
      · have hx2eq : x.2 = j := by omega
        exact (hxnej (Prod.ext hx1eq hx2eq)).elim
      · have hx1gt : j < x.1 := lt_of_le_of_ne hx1ge (Ne.symm hx1eq)
        have hx2lt : x.2 < j := by omega
        simp [f, hq x.2 hx2pos hx2lt]
  have hsplit0 := Finset.add_sum_erase s f h0
  have hsplitj := Finset.add_sum_erase (s.erase (0, 2 * j)) f hjErase
  have hsplit2 := Finset.add_sum_erase
    ((s.erase (0, 2 * j)).erase (j, j)) f h2Erase
  have hz :
      ∑ x ∈ (((s.erase (0, 2 * j)).erase (j, j)).erase (2 * j, 0)), f x = 0 :=
    Finset.sum_eq_zero hrest
  change (∑ x ∈ s, f x) = _
  rw [← hsplit0, ← hsplitj, ← hsplit2, hz]
  simp [f, add_assoc]

/-- The second-order `(0,j,2j)` jet on the parameter-gap subring. -/
noncomputable def parameterGapSecondJet
    (j : ℕ) (hj : 0 < j) :
    parameterGapSubring (R := R) j →+* DualNumber (DualNumber R) where
  toFun p :=
    ((p.1.coeff 0, p.1.coeff j),
      (p.1.coeff j, 2 * p.1.coeff (2 * j)))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · apply TrivSqZeroExt.ext <;> simp
    · apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · apply TrivSqZeroExt.ext
      · simp
      · change (1 : Polynomial R).coeff j = 0
        rw [Polynomial.coeff_one]
        exact if_neg (Nat.ne_of_gt hj)
    · apply TrivSqZeroExt.ext
      · change (1 : Polynomial R).coeff j = 0
        rw [Polynomial.coeff_one]
        exact if_neg (Nat.ne_of_gt hj)
      · change 2 * (1 : Polynomial R).coeff (2 * j) = 0
        rw [Polynomial.coeff_one]
        have h2j : 2 * j ≠ 0 := by omega
        simp [h2j]
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · apply TrivSqZeroExt.ext <;> simp
    · apply TrivSqZeroExt.ext <;> simp <;> ring
  map_mul' p q := by
    have hgap := coeff_mul_at_gap_endpoint_commRing
      (R := R) hj p.property q.property
    have hgap2 := coeff_mul_at_twice_gap_endpoint_commRing
      (R := R) hj p.property q.property
    apply TrivSqZeroExt.ext
    · apply TrivSqZeroExt.ext
      · simp [Polynomial.mul_coeff_zero]
      · simpa [DualNumber.snd_mul] using hgap
    · apply TrivSqZeroExt.ext
      · simpa [DualNumber.snd_mul] using hgap
      · simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mk,
          TrivSqZeroExt.snd_mk]
        change 2 * (p.1 * q.1).coeff (2 * j) = _
        rw [hgap2]
        simp [DualNumber.snd_mul]
        ring

@[simp] theorem parameterGapSecondJet_fst_fst
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.fst
      (TrivSqZeroExt.fst (parameterGapSecondJet (R := R) j hj p)) =
      p.1.coeff 0 := by
  simp [parameterGapSecondJet]

@[simp] theorem parameterGapSecondJet_fst_snd
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.fst (parameterGapSecondJet (R := R) j hj p)) =
      p.1.coeff j := by
  simp [parameterGapSecondJet]

@[simp] theorem parameterGapSecondJet_snd_fst
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.fst
      (TrivSqZeroExt.snd (parameterGapSecondJet (R := R) j hj p)) =
      p.1.coeff j := by rfl

@[simp] theorem parameterGapSecondJet_snd_snd
    (j : ℕ) (hj : 0 < j)
    (p : parameterGapSubring (R := R) j) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd (parameterGapSecondJet (R := R) j hj p)) =
      2 * p.1.coeff (2 * j) := by
  simp [parameterGapSecondJet]

/-- Entrywise second-order gap jet of a polynomial matrix. -/
noncomputable def matrixParameterGapSecondJet
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s)) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber R)) :=
  (parameterGapSecondJet (R := R) j hj).mapMatrix
    (matrixToParameterGapCommRing M hM)

@[simp] theorem matrixParameterGapSecondJet_apply
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s))
    (r s : Fin 4) :
    matrixParameterGapSecondJet hj M hM r s =
      (((M r s).coeff 0, (M r s).coeff j),
        ((M r s).coeff j, 2 * (M r s).coeff (2 * j))) := by
  simp [matrixParameterGapSecondJet, parameterGapSecondJet,
    matrixToParameterGapCommRing]

/-- **Second determinant coefficient bridge.**  The doubly-nilpotent component
of the determinant is twice the selected `2*j` coefficient. -/
theorem snd_snd_det_matrixParameterGapSecondJet
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ r s, HasNoPositiveParameterCoeffBelow j (M r s)) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd (matrixParameterGapSecondJet hj M hM).det) =
      2 * M.det.coeff (2 * j) := by
  let J : parameterGapSubring (R := R) j →+*
      DualNumber (DualNumber R) :=
    parameterGapSecondJet (R := R) j hj
  let G : Matrix (Fin 4) (Fin 4) (parameterGapSubring (R := R) j) :=
    matrixToParameterGapCommRing M hM
  have hmap : J G.det = (J.mapMatrix G).det := by
    exact J.map_det G
  have hsub := (parameterGapSubring (R := R) j).subtype.map_det G
  have hmatrix :
      (parameterGapSubring (R := R) j).subtype.mapMatrix G = M := by
    ext r s
    rfl
  rw [hmatrix] at hsub
  change
    TrivSqZeroExt.snd (TrivSqZeroExt.snd ((J.mapMatrix G).det)) =
      2 * M.det.coeff (2 * j)
  rw [← hmap]
  change
    2 * (((G.det : parameterGapSubring (R := R) j) : Polynomial R).coeff (2 * j)) =
      2 * M.det.coeff (2 * j)
  simpa using congrArg (fun p : Polynomial R => 2 * p.coeff (2 * j)) hsub

end

end HC4.Valuation
