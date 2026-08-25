import HC4.RationalRigidity.RankThreeBalancedHomogeneousEdge
import HC4.Toric.Facets
import Mathlib.Tactic

/-!
# A18.5.56: the homogeneous balanced terminal lies on `sp` or `rq`

A18.5.55 proves that every genuine balanced singular supported rank-three
terminal is ordinary homogeneous.  A18.5.44 had four possible primitive far
endpoint shapes: `p`, sparse `r`, `sp`, or `rq`.

Ordinary-degree preservation immediately excludes `p`, because the initial
endpoint has three strictly positive transverse coordinates and therefore
ordinary degree at least three, whereas `p=(1,0,0,1)` has degree two.

The sparse `r` shape is also impossible.  In that case the endpoint balance
is `a = b*u3`, while the initial balance is

    b*v2 = b*v3 + a*v4.

Cancelling the positive `b` gives `v2 = v3 + u3*v4`.  Since `v3,v4>0`, the
initial ordinary degree is strictly larger than `1+u3`, contradicting the
homogeneous endpoint degree.

Thus the only surviving primitive endpoint shapes are the two genuine
rank-three toric facets `sp` and `rq`.  This is the finite facet hand-off for
the final classification splice; no general Gordan--Noether theorem is used.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Homogeneous terminal facet reduction.**

A genuine balanced singular supported rank-three edge has primitive far
endpoint on exactly one of the two rank-three toric boundary types retained by
the classified `s`/`r` branches: `sp` (`u3 = 0`) or `rq` (`u4 = 0`). -/
theorem supported_balanced_rankThree_homogeneous_endpoint_sp_or_rq
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
    (0 < u2 ∧ u3 = 0 ∧ 0 < u4) ∨
      (0 < u2 ∧ 0 < u3 ∧ u4 = 0) := by
  let e0 := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M 0
  let eM := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M M

  have he0mem : e0 ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hstart
  have heMmem : eM ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hend
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

  have hdegree := supported_balanced_rankThree_edge_ordinaryDegreePreserving
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet

  rcases hshape.2 with hp | hr | hsp | hrq
  · rcases hp with ⟨hu2zero, hu3zero, hu4one⟩
    have hdegreeP : 2 = v2 + v3 + v4 := by
      simpa [hu2zero, hu3zero, hu4one] using hdegree
    omega
  · rcases hr with ⟨hu2zero, hu3pos, hu4zero⟩
    have hEndR : a = b * u3 := by
      simpa [hu2zero, hu4zero] using hEnd
    have hv2eq : v2 = v3 + u3 * v4 := by
      have hfac : b * v2 = b * (v3 + u3 * v4) := by
        calc
          b * v2 = b * v3 + a * v4 := hBase
          _ = b * v3 + (b * u3) * v4 := by rw [hEndR]
          _ = b * (v3 + u3 * v4) := by ring
      exact Nat.mul_left_cancel hb hfac
    have hu3le : u3 ≤ u3 * v4 := by
      have hv4one : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
      have hmul := Nat.mul_le_mul_left u3 hv4one
      simpa using hmul
    have hdegreeR : 1 + u3 = v2 + v3 + v4 := by
      simpa [hu2zero, hu4zero] using hdegree
    omega
  · exact Or.inl hsp
  · exact Or.inr hrq

end

end HC4.RationalRigidity
