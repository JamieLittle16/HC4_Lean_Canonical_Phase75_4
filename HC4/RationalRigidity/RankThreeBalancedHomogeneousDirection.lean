import HC4.RationalRigidity.RankThreeBalancedDirectionDegeneracy
import HC4.RationalRigidity.RankThreeSupportedSingleDirectionRefinement
import HC4.RationalRigidity.RankThreePrimitiveEndpointShape
import Mathlib.Tactic

/-!
# A18.5.54: every balanced rank-three terminal direction preserves ordinary degree

A18.5.51 leaves four possibilities: one of three transverse affine directions
vanishes, or the primitive direction preserves ordinary total degree.
A18.5.52--53 refine any single vanishing direction to a second vanishing
direction or ordinary-degree preservation.

Two fixed transverse coordinates are impossible for a balanced boundary edge.
The primitive endpoint classification A18.5.44 leaves only one possible
boundary shape in the first two pairings, and the balance equations at the
initial and final endpoints then force a positive term to vanish.  The third
pairing contradicts the boundary shape immediately.

Therefore the only surviving rank-three terminal direction is homogeneous:

    1 + u2 + u3 + u4 = v2 + v3 + v4.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Two fixed transverse endpoint coordinates are incompatible with a genuine
balanced singular rank-three boundary edge. -/
theorem supported_balanced_rankThree_two_fixed_impossible
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b F)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0)
    (hfixed :
      (u2 = v2 ∧ u3 = v3) ∨
      (u2 = v2 ∧ u4 = v4) ∨
      (u3 = v3 ∧ u4 = v4)) : False := by
  let e0 := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M 0
  let eM := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M M
  have he0mem : e0 ∈ F.support := MvPolynomial.mem_support_iff.mpr hstart
  have heMmem : eM ∈ F.support := MvPolynomial.mem_support_iff.mpr hend
  have hBal0raw : IsBalancedExponent a b e0 := hbalanced e0 he0mem
  have hBalMraw : IsBalancedExponent a b eM := hbalanced eM heMmem
  have hBase : b * v2 = b * v3 + a * v4 := by
    change b * (M * v2) = b * (M * v3) + a * (M * v4) at hBal0raw
    have hfac : M * (b * v2) = M * (b * v3 + a * v4) := by
      calc
        M * (b * v2) = b * (M * v2) := by ring
        _ = b * (M * v3) + a * (M * v4) := hBal0raw
        _ = M * (b * v3 + a * v4) := by ring
    exact Nat.mul_left_cancel hM hfac

  have hshape := supported_rankThree_edge_primitive_endpoint_shape
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  have hu1one : u1 = 1 := hshape.1
  have hEnd : a + b * u2 = b * u3 + a * u4 := by
    change a * (M * u1) + b * (M * u2) =
      b * (M * u3) + a * (M * u4) at hBalMraw
    rw [hu1one] at hBalMraw
    have hfac : M * (a + b * u2) = M * (b * u3 + a * u4) := by
      calc
        M * (a + b * u2) = a * (M * 1) + b * (M * u2) := by ring
        _ = b * (M * u3) + a * (M * u4) := hBalMraw
        _ = M * (b * u3 + a * u4) := by ring
    exact Nat.mul_left_cancel hM hfac

  rcases hfixed with ⟨hu2, hu3⟩ | ⟨hu2, hu4⟩ | ⟨hu3, hu4⟩
  · rcases hshape.2 with hp | hr | hsp | hrq
    · rcases hp with ⟨hz2, hz3, hz4⟩
      rw [hu2] at hz2
      omega
    · rcases hr with ⟨hz2, hp3, hz4⟩
      rw [hu2] at hz2
      omega
    · rcases hsp with ⟨hp2, hz3, hp4⟩
      rw [hu3] at hz3
      omega
    · rcases hrq with ⟨hp2, hp3, hz4⟩
      have hEnd' : a + b * v2 = b * v3 := by
        simpa [hu2, hu3, hz4] using hEnd
      have hav4 : 0 < a * v4 := Nat.mul_pos ha hv4
      omega
  · rcases hshape.2 with hp | hr | hsp | hrq
    · rcases hp with ⟨hz2, hz3, hz4⟩
      rw [hu2] at hz2
      omega
    · rcases hr with ⟨hz2, hp3, hz4⟩
      rw [hu2] at hz2
      omega
    · rcases hsp with ⟨hp2, hz3, hp4⟩
      have hEnd' : a + b * v2 = a * v4 := by
        simpa [hu2, hu4, hz3] using hEnd
      have hbv3 : 0 < b * v3 := Nat.mul_pos hb hv3
      omega
    · rcases hrq with ⟨hp2, hp3, hz4⟩
      rw [hu4] at hz4
      omega
  · rcases hshape.2 with hp | hr | hsp | hrq
    · rcases hp with ⟨hz2, hz3, hz4⟩
      rw [hu3] at hz3
      omega
    · rcases hr with ⟨hz2, hp3, hz4⟩
      rw [hu4] at hz4
      omega
    · rcases hsp with ⟨hp2, hz3, hp4⟩
      rw [hu3] at hz3
      omega
    · rcases hrq with ⟨hp2, hp3, hz4⟩
      rw [hu4] at hz4
      omega

/-- **Every genuine balanced singular supported rank-three terminal direction
preserves ordinary total degree.** -/
theorem supported_balanced_rankThree_edge_ordinaryDegreePreserving
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b F)
    (hsupp : IsSupportedOnRankThreeLine v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0) :
    1 + u2 + u3 + u4 = v2 + v3 + v4 := by
  rcases supported_balanced_rankThree_edge_directionDegenerate
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet with hu2 | hu3 | hu4 | hhom
  · rcases supported_rankThree_edge_u2_eq_refines
      (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet hu2 with
      hu3 | hu4 | hhom
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inl ⟨hu2, hu3⟩))
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inr (Or.inl ⟨hu2, hu4⟩)))
    · exact hhom
  · rcases supported_rankThree_edge_u3_eq_refines
      (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet hu3 with
      hu2 | hu4 | hhom
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inl ⟨hu2, hu3⟩))
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inr (Or.inr ⟨hu3, hu4⟩)))
    · exact hhom
  · rcases supported_rankThree_edge_u4_eq_refines
      (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet hu4 with
      hu2 | hu3 | hhom
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inr (Or.inl ⟨hu2, hu4⟩)))
    · exact False.elim
        (supported_balanced_rankThree_two_fixed_impossible
          (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced hsupp hstart hend hdet
          (Or.inr (Or.inr ⟨hu3, hu4⟩)))
    · exact hhom
  · exact hhom

end

end HC4.RationalRigidity
