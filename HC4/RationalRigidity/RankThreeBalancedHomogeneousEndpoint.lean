import HC4.RationalRigidity.RankThreeBalancedHomogeneousEdge
import Mathlib.Tactic

/-!
# A18.5.56: a homogeneous balanced rank-three terminal ends on `sp` or `rq`

A18.5.44 leaves four primitive possibilities for the far endpoint direction:
`p`, a sparse `r` direction, `sp`, or `rq`.  A18.5.54--55 add the decisive
ordinary-homogeneity relation.

The first two primitive shapes are incompatible with the retained balance
relations and positivity of the starting transverse exponents:

* the `p` endpoint has ordinary degree two, while the starting endpoint has
  three positive transverse coordinates;
* at a sparse `r` endpoint, balance gives `a = b * u3`.  Combining this with
  starting balance gives `v2 = v3 + u3 * v4`; homogeneity would then identify
  `1 + u3` with a quantity at least `u3 + 3`.

Thus the only genuine homogeneous terminal endpoints are the two adjacent
classified toric facets `sp` and `rq`.  This is the exact finite reduction
needed before applying the mature facet normal-form machinery.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Homogeneous endpoint facet reduction.**

Every genuine balanced singular supported rank-three terminal has primitive
far endpoint on `sp` or `rq`; the `p` and sparse-`r` primitive endpoints are
arithmetically impossible. -/
theorem supported_balanced_rankThree_homogeneous_endpoint_sp_or_rq
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
    (0 < u2 ∧ u3 = 0 ∧ 0 < u4) ∨
      (0 < u2 ∧ 0 < u3 ∧ u4 = 0) := by
  let e0 := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M 0
  let eM := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M M
  have he0mem : e0 ∈ F.support := MvPolynomial.mem_support_iff.mpr hstart
  have heMmem : eM ∈ F.support := MvPolynomial.mem_support_iff.mpr hend
  have hBal0raw : IsBalancedExponent a b e0 := hbalanced e0 he0mem
  have hBalMraw : IsBalancedExponent a b eM := hbalanced eM heMmem

  have hBaseLine :
      b * (M * v2) = b * (M * v3) + a * (M * v4) := by
    simpa [e0, IsBalancedExponent,
      rankThreeLineExponentFinsupp_apply] using hBal0raw
  have hBase : b * v2 = b * v3 + a * v4 := by
    have hfac : M * (b * v2) = M * (b * v3 + a * v4) := by
      calc
        M * (b * v2) = b * (M * v2) := by ring
        _ = b * (M * v3) + a * (M * v4) := hBaseLine
        _ = M * (b * v3 + a * v4) := by ring
    exact Nat.mul_left_cancel hM hfac

  have hshape := supported_rankThree_edge_primitive_endpoint_shape
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  have hu1one : u1 = 1 := hshape.1
  have hEndLine :
      a * (M * u1) + b * (M * u2) =
        b * (M * u3) + a * (M * u4) := by
    simpa [eM, IsBalancedExponent,
      rankThreeLineExponentFinsupp_apply] using hBalMraw
  have hEnd : a + b * u2 = b * u3 + a * u4 := by
    rw [hu1one] at hEndLine
    have hfac : M * (a + b * u2) = M * (b * u3 + a * u4) := by
      calc
        M * (a + b * u2) = a * (M * 1) + b * (M * u2) := by ring
        _ = b * (M * u3) + a * (M * u4) := hEndLine
        _ = M * (b * u3 + a * u4) := by ring
    exact Nat.mul_left_cancel hM hfac

  have hdegree := supported_balanced_rankThree_edge_ordinaryDegreePreserving
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet

  rcases hshape.2 with hp | hr | hsp | hrq
  · rcases hp with ⟨hu2zero, hu3zero, hu4one⟩
    rw [hu2zero, hu3zero, hu4one] at hdegree
    omega
  · rcases hr with ⟨hu2zero, hu3pos, hu4zero⟩
    have hab : a = b * u3 := by
      simpa [hu2zero, hu4zero] using hEnd
    have hfac : b * v2 = b * (v3 + u3 * v4) := by
      calc
        b * v2 = b * v3 + a * v4 := hBase
        _ = b * (v3 + u3 * v4) := by rw [hab]; ring
    have hv2eq : v2 = v3 + u3 * v4 :=
      Nat.mul_left_cancel hb hfac
    have hu3le : u3 ≤ u3 * v4 := by
      have hv4one : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
      simpa using Nat.mul_le_mul_left u3 hv4one
    rw [hu2zero, hu4zero] at hdegree
    omega
  · exact Or.inl hsp
  · exact Or.inr hrq

end

end HC4.RationalRigidity
