import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# First determinant jet at a determinant-one matrix

The first variation is the adjugate-trace pairing. A ring homomorphism
after a derivation gives the same identity on a restricted locus.
-/

namespace HC4.Polynomial

open scoped Polynomial Matrix

noncomputable section

variable {R : Type*} [CommRing R]

private def dualJet : Polynomial R →+* DualNumber R where
  toFun p := (p.coeff 0, p.coeff 1)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [Polynomial.coeff_one]
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp [Polynomial.coeff_mul]
    · simp [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, add_comm]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a determinant-one matrix, the nilpotent component of the determinant
is the trace pairing of the adjugate with the first jet. -/
theorem snd_det_dualJet_of_det_one (A E : Matrix n n R)
    (hA : A.det = 1) :
    TrivSqZeroExt.snd
      (Matrix.of (fun i j => (A i j, E i j)) : Matrix n n (DualNumber R)).det =
      (A.adjugate * E).trace := by
  let T : Matrix n n (Polynomial R) :=
    A.map Polynomial.C + (Polynomial.X : Polynomial R) • E.map Polynomial.C
  have hmap : (dualJet (R := R)).mapMatrix T =
      (Matrix.of (fun i j => (A i j, E i j)) : Matrix n n (DualNumber R)) := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · change ((T i j).coeff 0) = A i j
      simp [T, Matrix.smul_apply, smul_eq_mul]
    · change ((T i j).coeff 1) = E i j
      simp [T, Matrix.smul_apply, smul_eq_mul]
  have hadj : A.adjugate * A = 1 := by
    rw [Matrix.adjugate_mul, hA, one_smul]
  have hadjDet : A.adjugate.det = 1 := by
    have h := congrArg Matrix.det hadj
    simpa [Matrix.det_mul, hA] using h
  have hnormalize :
      A.adjugate.map Polynomial.C * T =
        1 + (Polynomial.X : Polynomial R) • (A.adjugate * E).map Polynomial.C := by
    simp [T, Matrix.mul_add, ← Matrix.map_mul, hadj]
  have hnormalizedDet :
      (1 + (Polynomial.X : Polynomial R) • (A.adjugate * E).map Polynomial.C :
        Matrix n n (Polynomial R)).det =
        T.det := by
    rw [← hnormalize, Matrix.det_mul]
    change (Polynomial.C.mapMatrix A.adjugate).det * T.det = T.det
    rw [← Polynomial.C.map_det, hadjDet, map_one, one_mul]
  rw [← hmap, ← (dualJet (R := R)).map_det]
  change T.det.coeff 1 = _
  rw [← hnormalizedDet]
  exact Matrix.coeff_det_one_add_X_smul_one (A.adjugate * E)

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- Restrict a value and its first derivative simultaneously. -/
private def restrictedDualJet (φ : S →+* R) (D : Derivation k S S) :
    S →+* DualNumber R where
  toFun p := (φ p, φ (D p))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [D.leibniz, smul_eq_mul, mul_comm]

/-- Jacobi's determinant identity after any ring restriction, written so
the source determinant and all source derivatives remain unchanged. -/
theorem restricted_derivation_det_eq_trace (φ : S →+* R) (D : Derivation k S S)
    (M : Matrix n n S) (hdet : (φ.mapMatrix M).det = 1) :
    φ (D M.det) =
      ((φ.mapMatrix M).adjugate * M.map (fun a => φ (D a))).trace := by
  let J := restrictedDualJet φ D
  have h := congrArg TrivSqZeroExt.snd (J.map_det M)
  change φ (D M.det) =
    TrivSqZeroExt.snd
      (Matrix.of (fun i j => (φ (M i j), φ (D (M i j)))) :
        Matrix n n (DualNumber R)).det at h
  rw [h]
  exact snd_det_dualJet_of_det_one (φ.mapMatrix M) (M.map fun a => φ (D a)) hdet

end

end HC4.Polynomial
