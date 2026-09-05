import HC4.RationalRigidity.RankThreeBalancedHomogeneousDirection
import Mathlib.Tactic

/-!
# A18.5.55: the balanced rank-three terminal is an honest homogeneous edge

A18.5.54 proves that the primitive affine direction of every genuine balanced
singular supported rank-three terminal preserves ordinary total degree.  The
line itself is

    e_j = (M-j) v + j u,

with `v=(0,v2,v3,v4)` and, by A18.5.44, `u1=1`.  Hence equality of the two
endpoint ordinary degrees makes every supported exponent have the same degree

    M * (v2 + v3 + v4).

This file turns the endpoint arithmetic into the actual
`MvPolynomial.IsHomogeneous` certificate consumed by the mature homogeneous
Newton/torus infrastructure.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Degree of one honest rank-three line exponent when the primitive endpoint
direction preserves ordinary total degree. -/
theorem rankThreeLineExponent_degree_of_ordinaryDegreePreserving
    {v2 v3 v4 u1 u2 u3 u4 M j : ℕ}
    (hj : j ≤ M)
    (hu1 : u1 = 1)
    (hdeg : 1 + u2 + u3 + u4 = v2 + v3 + v4) :
    (rankThreeLineExponentFinsupp
      v2 v3 v4 u1 u2 u3 u4 M j).degree =
      M * (v2 + v3 + v4) := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [rankThreeLineExponentFinsupp, Fin.sum_univ_four, hu1]
    calc
      j + ((M - j) * v2 + j * u2) +
          ((M - j) * v3 + j * u3) +
          ((M - j) * v4 + j * u4) =
          (M - j) * (v2 + v3 + v4) +
            j * (1 + u2 + u3 + u4) := by ring
      _ = (M - j) * (v2 + v3 + v4) +
            j * (v2 + v3 + v4) := by rw [hdeg]
      _ = (M - j + j) * (v2 + v3 + v4) := by ring
      _ = M * (v2 + v3 + v4) := by rw [Nat.sub_add_cancel hj]
  · intro i
    simp

/-- **Actual homogeneous terminal edge.**

Every genuine balanced singular supported rank-three terminal polynomial is
ordinary homogeneous.  No top-degree component or replacement polynomial is
introduced: this is the original supported edge itself. -/
theorem supported_balanced_rankThree_edge_isHomogeneous
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b F)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0) :
    F.IsHomogeneous (M * (v2 + v3 + v4)) := by
  have hshape := supported_rankThree_edge_primitive_endpoint_shape
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  have hu1one : u1 = 1 := hshape.1
  have hdegree := supported_balanced_rankThree_edge_ordinaryDegreePreserving
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  intro d hd
  have hdmem : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hd
  rcases hsupp d hdmem with ⟨j, hj, rfl⟩
  have hdegj := rankThreeLineExponent_degree_of_ordinaryDegreePreserving
    hj hu1one hdegree
  rw [Finsupp.degree_eq_weight_one] at hdegj
  exact hdegj

end

end HC4.RationalRigidity
