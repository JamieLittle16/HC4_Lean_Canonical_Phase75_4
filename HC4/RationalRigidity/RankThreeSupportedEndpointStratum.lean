import HC4.RationalRigidity.RankThreeSupportedEndpointBoundary
import HC4.Newton.BoundaryStrata
import Mathlib.Tactic

/-!
# A18.5.43: classify the actual terminal endpoint in the symmetric cone

A18.5.42 proves that the opposite endpoint of a singular supported rank-three
edge reaches the toric boundary.  The original Newton edge has not lost its
symmetric torus-balance provenance.  We can therefore apply the already-green
boundary-strata classifier directly to that *actual endpoint*.

Consequently the endpoint is either

* rank three in the relative interior of its new facet; or
* on one of the two extreme transition rays of that facet.

This is the exact finite split between the remaining rank-three pencil case
and the complementary/ray case.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Newton
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Balanced endpoint stratum theorem for an actual supported terminal.** -/
theorem supported_rankThree_edge_endpoint_stratum
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
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
    u1 = 1 ∧
      ((∃ G : ToricFacet,
          RankThreeOnFacet G
            (toToricExponent
              (rankThreeLineExponentFinsupp
                v2 v3 v4 u1 u2 u3 u4 M M))) ∨
       (∃ G H : ToricFacet,
          AdjacentFacets G H ∧
          OnRay a b G H
            (toToricExponent
              (rankThreeLineExponentFinsupp
                v2 v3 v4 u1 u2 u3 u4 M M)))) := by
  let eM := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M M
  have hendpoint := supported_rankThree_edge_endpoint_zero
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  have heMmem : eM ∈ F.support := by
    exact MvPolynomial.mem_support_iff.mpr hend
  have hBalMv : IsBalancedExponent a b eM := hbalanced eM heMmem
  have hBal : Balanced a b (toToricExponent eM) :=
    (isBalancedExponent_iff_balanced a b eM).1 hBalMv
  have hbdryMv : MvExponentOnBoundary eM := by
    rw [mvExponentOnBoundary_iff_coordinate_zero]
    rcases hendpoint.2 with hu2 | hu3 | hu4
    · exact Or.inr (Or.inl (by
        dsimp [eM]
        simp [rankThreeLineExponentFinsupp_apply, hu2]))
    · exact Or.inr (Or.inr (Or.inl (by
        dsimp [eM]
        simp [rankThreeLineExponentFinsupp_apply, hu3])))
    · exact Or.inr (Or.inr (Or.inr (by
        dsimp [eM]
        simp [rankThreeLineExponentFinsupp_apply, hu4])))
  have hstratum := boundary_rankThree_or_extremeRay
    ha hb hcop hBal hbdryMv
  simpa [eM] using And.intro hendpoint.1 hstratum

end

end HC4.RationalRigidity
