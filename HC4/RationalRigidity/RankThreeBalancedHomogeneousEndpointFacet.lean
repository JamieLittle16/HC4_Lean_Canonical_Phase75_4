import HC4.RationalRigidity.RankThreeBalancedHomogeneousEndpoint
import HC4.Newton.BoundaryStrata
import Mathlib.Tactic

/-!
# A18.5.57: the homogeneous terminal reaches a genuine `sp`/`rq` rank-three facet

A18.5.56 leaves exactly two primitive far-endpoint shapes.  Because the line
length and every surviving endpoint coordinate are positive, the actual far
exponent is not merely on the toric boundary: it lies in the relative interior
of the corresponding facet.

Thus the homogeneous rank-three terminal runs from the retained `qs` side to a
genuine rank-three point of `sp` or `rq`.  In particular the extreme-ray
remainder from the older boundary-stratum interface has disappeared.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Newton
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Actual far endpoint lies in a classified rank-three facet.** -/
theorem supported_balanced_rankThree_homogeneous_endpoint_rankThree_sp_or_rq
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
    (hdet : hessianDeterminant F = 0) :
    let eM := rankThreeLineExponentFinsupp
      v2 v3 v4 u1 u2 u3 u4 M M
    RankThreeOnFacet .sp (toToricExponent eM) ∨
      RankThreeOnFacet .rq (toToricExponent eM) := by
  dsimp only
  rcases supported_balanced_rankThree_homogeneous_endpoint_sp_or_rq
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet with hsp | hrq
  · rcases hsp with ⟨hu2, hu3, hu4⟩
    left
    simp only [RankThreeOnFacet, toToricExponent_x1,
      toToricExponent_x2, toToricExponent_x3, toToricExponent_x4]
    constructor
    · simp [rankThreeLineExponentFinsupp_apply, hu3]
    constructor
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu1
    constructor
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu2
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu4
  · rcases hrq with ⟨hu2, hu3, hu4⟩
    right
    simp only [RankThreeOnFacet, toToricExponent_x1,
      toToricExponent_x2, toToricExponent_x3, toToricExponent_x4]
    constructor
    · simp [rankThreeLineExponentFinsupp_apply, hu4]
    constructor
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu1
    constructor
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu2
    · simpa [rankThreeLineExponentFinsupp_apply] using Nat.mul_pos hM hu3

end

end HC4.RationalRigidity
