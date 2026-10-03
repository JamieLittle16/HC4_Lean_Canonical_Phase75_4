import HC4.RationalRigidity.RankThreeSupportedDirectionSplit
import HC4.RationalRigidity.RankThreeBalancedDegreeOneImpossible
import Mathlib.Tactic

/-!
# A18.5.51: balanced rank-three terminals are direction-degenerate

A18.5.45 reduces an actual supported singular rank-three edge to five finite
alternatives: degree one, three vanishing affine-direction coordinates, or
ordinary-degree preservation.  A18.5.50 eliminates the degree-one branch for
a balanced edge.

Thus every genuine balanced supported terminal is forced directly into one of
the four geometric direction degeneracies consumed by the final Newton
restart/terminal dispatch.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Balanced supported rank-three direction degeneracy.** -/
theorem supported_balanced_rankThree_edge_directionDegenerate
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
    u2 = v2 ∨ u3 = v3 ∨ u4 = v4 ∨
      1 + u2 + u3 + u4 = v2 + v3 + v4 := by
  rcases supported_rankThree_edge_degreeOne_or_directionDegenerate
      (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet with
    hMone | hdegenerate
  · subst M
    exact False.elim
      (supported_balanced_rankThree_degreeOne_impossible
        (K := K) ha hb hv2 hv3 hv4 hu1 hbalanced
        hsupp hstart hend hdet)
  · exact hdegenerate

end

end HC4.RationalRigidity
