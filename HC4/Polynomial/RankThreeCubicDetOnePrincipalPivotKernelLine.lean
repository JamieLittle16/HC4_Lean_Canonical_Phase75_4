import HC4.Polynomial.RankThreeCubicDetOneSourceRankThreeRepairIsotropic
import Mathlib.Tactic

/-!
# A surviving full principal cofactor automatically makes a kernel line

This is algebra over an arbitrary integral domain, not an added HC4
endpoint assumption. A nonzero diagonal adjugate entry of A implies
that replacing column k by column k plus the kth standard basis vector
produces a matrix with nonzero determinant, provided det A = 0.

Consequently a vector in ker A whose kth coordinate is zero must
vanish. If a fixed kernel vector has invertible kth coordinate,
every kernel vector is a scalar multiple of that vector.

The second statement is the missing rank-three hypothesis in the
source-cubic trace-isotropy bridge: constant nonzero ground-field
coordinates remain units in the pole quotient.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A principal cofactor pivot eliminates kernel vectors with
zero coordinate at that pivot. The proof needs no field of fractions. -/
theorem principalCofactor_kernel_zero_of_pivot_zero
    (A : Matrix ι ι R)
    (hdet : A.det = 0)
    (k : ι)
    (hkk : A.adjugate k k ≠ 0)
    (z : ι → R)
    (hAz : A *ᵥ z = 0)
    (hzk : z k = 0) :
    z = 0 := by
  classical
  let A' : Matrix ι ι R :=
    A.updateCol k (fun i => A i k + Pi.single k (1 : R) i)
  have hcol : (A.updateCol k (Pi.single k (1 : R))).det =
      A.adjugate k k := by
    calc
      (A.updateCol k (Pi.single k (1 : R))).det =
          (A.cramer (Pi.single k (1 : R))) k :=
        (Matrix.cramer_apply A (Pi.single k (1 : R)) k).symm
      _ = (A.adjugate *ᵥ Pi.single k (1 : R)) k :=
        congrFun (Matrix.cramer_eq_adjugate_mulVec A (Pi.single k (1 : R))) k
      _ = A.adjugate k k := by
        simp [Matrix.mulVec, dotProduct]
  have hA'det : A'.det = A.adjugate k k := by
    change (A.updateCol k
      ((fun i => A i k) + Pi.single k (1 : R))).det = _
    rw [Matrix.det_updateCol_add, Matrix.updateCol_eq_self]
    rw [hdet, zero_add]
    exact hcol
  have hA'ne : A'.det ≠ 0 := by
    rw [hA'det]
    exact hkk
  have hsame : A' *ᵥ z = A *ᵥ z := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · subst j
      simp [A', hzk]
    · simp [A', Matrix.updateCol_ne hj]
  have hA'z : A' *ᵥ z = 0 := by
    rw [hsame, hAz]
  exact Matrix.eq_zero_of_mulVec_eq_zero hA'ne hA'z

/-- In a singular matrix with a surviving principal cofactor,
a nonzero kernel vector cannot vanish at the pivot coordinate. -/
theorem principalCofactor_kernelVector_pivot_ne_zero
    (A : Matrix ι ι R) (v : ι → R)
    (hAv : A *ᵥ v = 0)
    (hv : v ≠ 0)
    (k : ι) (hkk : A.adjugate k k ≠ 0) :
    v k ≠ 0 := by
  intro hvk
  have hdet : A.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hAv⟩
  exact hv (principalCofactor_kernel_zero_of_pivot_zero
    A hdet k hkk v hAv hvk)

/-- If the fixed kernel vector has a unit at the principal
cofactor pivot, it generates the entire kernel over the original
domain, not merely over its fraction field. -/
theorem principalCofactor_kernelLine_of_unitCoordinate
    (A : Matrix ι ι R) (v : ι → R)
    (hAv : A *ᵥ v = 0)
    (k : ι) (hkk : A.adjugate k k ≠ 0)
    (hinv : ∃ t : R, v k * t = 1) :
    ∀ z : ι → R, A *ᵥ z = 0 →
      ∃ c : R, ∀ i : ι, z i = c * v i := by
  classical
  obtain ⟨t, ht⟩ := hinv
  have hv : v ≠ 0 := by
    intro hz
    have hvk : v k = 0 := congrFun hz k
    rw [hvk, zero_mul] at ht
    exact zero_ne_one ht
  have hdet : A.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hAv⟩
  intro z hAz
  let d : ι → R := fun i => v k * z i - z k * v i
  have hdk : d k = 0 := by
    dsimp [d]
    ring
  have hdker : A *ᵥ d = 0 := by
    have hd : d = v k • z - z k • v := by
      funext i
      simp [d, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hd, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hAz, hAv]
    simp
  have hd0 : d = 0 :=
    principalCofactor_kernel_zero_of_pivot_zero
      A hdet k hkk d hdker hdk
  have hcross (i : ι) : v k * z i = z k * v i := by
    have hi := congrFun hd0 i
    exact sub_eq_zero.mp (by simpa [d] using hi)
  refine ⟨t * z k, ?_⟩
  intro i
  calc
    z i = (v k * t) * z i := by rw [ht, one_mul]
    _ = t * (v k * z i) := by ring
    _ = t * (z k * v i) := by rw [hcross i]
    _ = (t * z k) * v i := by ring

end
end HC4.Polynomial.RankThreeCubic
