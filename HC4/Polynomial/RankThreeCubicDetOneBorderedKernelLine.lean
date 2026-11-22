import HC4.Polynomial.RankThreeCubicDetOneFixedTangentOriginQuadraticKernelOrTriple
import Mathlib.Tactic

/-!
# A singular 3-by-3 block of an invertible bordered 4-by-4 matrix
# has a one-dimensional kernel

Let B be invertible over a field K, indexed by Unit ⊕ Fin 3.
Let T be its transverse 3-by-3 block. Suppose a nonzero
vector w is killed by T.

The longitudinal pairing c_w = sum_j B[x,j] w_j is nonzero:
otherwise B(0,w)=0. More strongly, for every z in ker(T),
the vector c_w*z - c_z*w has zero transverse block response
and zero longitudinal response. Invertibility of B forces
that vector to vanish, so z = (c_z/c_w)*w.

No symmetry or source hypotheses are needed. Over K, this
characterizes a one-dimensional kernel (equivalently rank(T)=2).
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

private abbrev BI (K : Type*) [Field K] :=
  Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K

/-- A nonzero transverse kernel direction of an invertible
bordered matrix necessarily couples nontrivially to the
longitudinal row. -/
theorem borderedInvertible_transverseKernel_longitudinalPairing_ne_zero
    (B : BI K) (hB : B.det ≠ 0)
    (w : Fin 3 → K) (hw : w ≠ 0)
    (hwrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B (.inr i) (.inr j) * w j) = 0) :
    (∑ j : Fin 3, B (.inl ()) (.inr j) * w j) ≠ 0 := by
  classical
  intro hc
  let v : Unit ⊕ Fin 3 → K :=
    Sum.elim (fun _ : Unit => 0) w
  have hv : B *ᵥ v = 0 := by
    funext i
    cases i with
    | inl u =>
      cases u
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v] using hc
    | inr k =>
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v] using hwrows k
  have hvzero : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hB hv
  apply hw
  funext j
  have hj := congrFun hvzero (.inr j)
  simpa [v] using hj

/-- An invertible bordered matrix's singular transverse block
has no kernel direction independent from a fixed nonzero
kernel vector w: the entire kernel is K*w. -/
theorem borderedInvertible_transverseKernel_isLine
    (B : BI K) (hB : B.det ≠ 0)
    (w : Fin 3 → K) (hw : w ≠ 0)
    (hwrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B (.inr i) (.inr j) * w j) = 0) :
    ∀ z : Fin 3 → K,
      (∀ i : Fin 3,
        (∑ j : Fin 3, B (.inr i) (.inr j) * z j) = 0) →
      ∃ c : K, ∀ j : Fin 3, z j = c * w j := by
  classical
  let cw : K := ∑ j : Fin 3, B (.inl ()) (.inr j) * w j
  have hcwnz : cw ≠ 0 :=
    borderedInvertible_transverseKernel_longitudinalPairing_ne_zero
      B hB w hw hwrows
  intro z hzrows
  let cz : K := ∑ j : Fin 3, B (.inl ()) (.inr j) * z j
  let d : Fin 3 → K := fun j => cw * z j - cz * w j
  have hsum (i : Unit ⊕ Fin 3) :
      (∑ j : Fin 3, B i (.inr j) * d j) =
        cw * (∑ j : Fin 3, B i (.inr j) * z j) -
        cz * (∑ j : Fin 3, B i (.inr j) * w j) := by
    calc
      _ = ∑ j : Fin 3,
        (cw * (B i (.inr j) * z j) -
          cz * (B i (.inr j) * w j)) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [d]
          ring
      _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  let vd : Unit ⊕ Fin 3 → K :=
    Sum.elim (fun _ : Unit => 0) d
  have hrow (i : Unit ⊕ Fin 3) :
      (B *ᵥ vd) i =
        (∑ j : Fin 3, B i (.inr j) * d j) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, vd]
  have hzero : B *ᵥ vd = 0 := by
    funext i
    rw [hrow i, hsum i]
    cases i with
    | inl u =>
      cases u
      change cw * cz - cz * cw = 0
      ring
    | inr j =>
      rw [hzrows j, hwrows j]
      simp only [Pi.zero_apply]
  have hvzero : vd = 0 := Matrix.eq_zero_of_mulVec_eq_zero hB hzero
  have hproportional (j : Fin 3) : cw * z j = cz * w j := by
    have hj := congrFun hvzero (.inr j)
    have hdiff : d j = 0 := by simpa [vd] using hj
    exact sub_eq_zero.mp hdiff
  refine ⟨cz / cw, ?_⟩
  intro j
  apply mul_left_cancel₀ hcwnz
  calc
    cw * z j = cz * w j := hproportional j
    _ = cw * ((cz / cw) * w j) := by
      field_simp [hcwnz]

end
end HC4.Polynomial.RankThreeCubic
