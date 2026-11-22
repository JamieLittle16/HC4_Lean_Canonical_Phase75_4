import HC4.Polynomial.RankThreeCubicDetOneFixedTangentRepairOrTriple
import Mathlib.Tactic

/-!
# Determinant-one rigidity of a purely longitudinal repair

Suppose B is a 4x4 matrix over a commutative ring with det(B)=1.
If its action on v has no transverse coordinates, but some
transverse coordinate of v is a unit, then the one surviving
longitudinal coordinate of Bv must itself be a unit.

This strengthens the weak "nonzero correction" result.
The proof is elementary and valid over the prime quotient
without passing to its fraction field. The adjugate of B
reconstructs v from Bv; a unit transverse coordinate of v
forces the longitudinal output of B to divide a unit.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- A determinant-one matrix cannot map a vector with a unit
transverse pivot into the longitudinal axis with a nonunit
longitudinal coordinate. No field or domain hypotheses. -/
theorem detOne_pureLongitudinal_output_isUnit
    {R : Type*} [CommRing R]
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (v : Unit ⊕ Fin 3 → R)
    (k : Fin 3)
    (hdet : B.det = 1)
    (hvk : IsUnit (v (.inr k)))
    (htrans : ∀ i : Fin 3, (B *ᵥ v) (.inr i) = 0) :
    IsUnit ((B *ᵥ v) (.inl ())) := by
  classical
  have hadj : B.adjugate * B = 1 := by
    rw [Matrix.adjugate_mul, hdet]
    simp
  have hrecover : B.adjugate *ᵥ (B *ᵥ v) = v := by
    rw [← Matrix.mulVec_mulVec, hadj]
    simp
  have hk := congrFun hrecover (.inr k)
  change
    (∑ j : Unit ⊕ Fin 3,
      B.adjugate (.inr k) j * (B *ᵥ v) j) =
      v (.inr k) at hk
  have hlong :
      B.adjugate (.inr k) (.inl ()) *
        (B *ᵥ v) (.inl ()) = v (.inr k) := by
    simpa [Fintype.sum_sum_type, htrans] using hk
  have hdvd : (B *ᵥ v) (.inl ()) ∣ v (.inr k) := by
    refine ⟨B.adjugate (.inr k) (.inl ()), ?_⟩
    calc
      v (.inr k) =
          B.adjugate (.inr k) (.inl ()) *
            (B *ᵥ v) (.inl ()) := hlong.symm
      _ = (B *ᵥ v) (.inl ()) *
          B.adjugate (.inr k) (.inl ()) := mul_comm _ _
  exact isUnit_of_dvd_unit hdvd hvk

end
end HC4.Polynomial.RankThreeCubic
