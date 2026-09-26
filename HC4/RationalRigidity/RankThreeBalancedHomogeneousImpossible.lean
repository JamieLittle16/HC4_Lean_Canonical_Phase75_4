import HC4.RationalRigidity.RankThreeHomogeneousEndpointUnits
import Mathlib.Tactic

/-!
# A18.5.63: the balanced singular rank-three terminal is impossible

The homogeneous terminal endgame is now finite.

A18.5.56 says the primitive far endpoint is `sp` or `rq`.  A18.5.62 forces
the corresponding omitted starting coordinate to be one.  A18.5.59 supplies
one fixed transverse coordinate, while A18.5.54 supplies ordinary degree
preservation.  In either endpoint shape, the unit equality and homogeneity
turn any surviving fixed coordinate into a second fixed coordinate.

But A18.5.54 already proves that two fixed transverse coordinates are
incompatible with a genuine balanced singular rank-three boundary edge.
Hence no such terminal exists.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Balanced singular supported rank-three terminal impossibility.** -/
theorem supported_balanced_rankThree_edge_impossible
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
    (hdet : hessianDeterminant F = 0) : False := by
  have hendpoint :=
    supported_balanced_rankThree_homogeneous_endpoint_sp_or_rq
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet
  have hdegree := supported_balanced_rankThree_edge_ordinaryDegreePreserving
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  have hfixed :=
    supported_balanced_rankThree_homogeneous_direction_has_fixed_transverse
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet

  rcases hendpoint with hsp | hrq
  · have hv3one :=
      supported_balanced_rankThree_homogeneous_sp_forces_v3_one
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet hsp
    rcases hfixed with hu2 | hu3 | hu4
    · have hu4eq : u4 = v4 := by
        rcases hsp with ⟨_hu2pos, hu3zero, _hu4pos⟩
        omega
      exact supported_balanced_rankThree_two_fixed_impossible
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet
        (Or.inr (Or.inl ⟨hu2, hu4eq⟩))
    · rcases hsp with ⟨_hu2pos, hu3zero, _hu4pos⟩
      rw [hu3zero, hv3one] at hu3
      omega
    · have hu2eq : u2 = v2 := by
        rcases hsp with ⟨_hu2pos, hu3zero, _hu4pos⟩
        omega
      exact supported_balanced_rankThree_two_fixed_impossible
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet
        (Or.inr (Or.inl ⟨hu2eq, hu4⟩))

  · have hv4one :=
      supported_balanced_rankThree_homogeneous_rq_forces_v4_one
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet hrq
    rcases hfixed with hu2 | hu3 | hu4
    · have hu3eq : u3 = v3 := by
        rcases hrq with ⟨_hu2pos, _hu3pos, hu4zero⟩
        omega
      exact supported_balanced_rankThree_two_fixed_impossible
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet
        (Or.inl ⟨hu2, hu3eq⟩)
    · have hu2eq : u2 = v2 := by
        rcases hrq with ⟨_hu2pos, _hu3pos, hu4zero⟩
        omega
      exact supported_balanced_rankThree_two_fixed_impossible
        (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
        hsupp hstart hend hdet
        (Or.inl ⟨hu2eq, hu3⟩)
    · rcases hrq with ⟨_hu2pos, _hu3pos, hu4zero⟩
      rw [hu4zero, hv4one] at hu4
      omega

end

end HC4.RationalRigidity
