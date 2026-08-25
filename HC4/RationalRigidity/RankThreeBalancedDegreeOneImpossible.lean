import HC4.RationalRigidity.RankThreePrimitiveEndpointShape
import HC4.Polynomial.RankThreeDegreeOnePencilRealisation
import HC4.Polynomial.RankThreeWeightedBoundaryPencils
import Mathlib.Tactic

/-!
# A18.5.50: balanced degree-one rank-three terminals are impossible

The scalar terminal direction theorem has a special `D=1` branch.  On an
actual supported Newton edge, A18.5.48 turns that branch into the literal
coefficient-weighted pencil of its two endpoint exponents.  A18.5.44 reduces
the balanced primitive far endpoint to four shapes.

The two two-zero shapes are excluded by the weighted sparse determinant
identities.  In each one-zero shape A18.5.49 forces a base exponent to equal
one and yields an endpoint cross-product relation.  Combining that relation
with the symmetric balance equation at both endpoints gives a positive
integer equal to zero.

Thus the degree-one branch of the rank-three terminal direction split cannot
occur for a genuine balanced supported edge.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Balanced degree-one rank-three terminal impossibility.** -/
theorem supported_balanced_rankThree_degreeOne_impossible
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b F)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 1 F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 1 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 1 1) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 1 F
  have hc0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    rw [coeff_zero_rankThreeLineCoefficientPolynomial]
    exact hstart
  have hc1 : phi.coeff 1 ≠ 0 := by
    dsimp [phi]
    rw [coeff_M_rankThreeLineCoefficientPolynomial]
    exact hend

  have hpencil :
      (weightedRankThreeEndpointPencil
        (K := K)
        (v2 : K) (v3 : K) (v4 : K)
        (u1 : K) (u2 : K) (u3 : K) (u4 : K)
        (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using
      (supported_rankThree_degreeOne_endpointPencil_det_zero
        (K := K) hu1 hsupp hdet)

  let e0 := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 1 0
  let e1 := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 1 1
  have he0mem : e0 ∈ F.support := MvPolynomial.mem_support_iff.mpr hstart
  have he1mem : e1 ∈ F.support := MvPolynomial.mem_support_iff.mpr hend
  have hBal0raw : IsBalancedExponent a b e0 := hbalanced e0 he0mem
  have hBal1raw : IsBalancedExponent a b e1 := hbalanced e1 he1mem
  have hBal0 : b * v2 = b * v3 + a * v4 := by
    simpa [e0, IsBalancedExponent, rankThreeLineExponentFinsupp_apply] using hBal0raw
  have hBal1 : a * u1 + b * u2 = b * u3 + a * u4 := by
    simpa [e1, IsBalancedExponent, rankThreeLineExponentFinsupp_apply] using hBal1raw

  have hshape := supported_rankThree_edge_primitive_endpoint_shape
    (K := K) ha hb hv2 hv3 hv4 (by omega : 0 < (1 : ℕ)) hu1
    hbalanced hsupp hstart hend hdet
  have hu1one : u1 = 1 := hshape.1
  rcases hshape.2 with hp | hr | hsp | hrq
  · rcases hp with ⟨hu2, hu3, hu4⟩
    subst u1
    subst u2
    subst u3
    subst u4
    exact
      (weightedPTransitionRankThreeEndpointPencil_det_ne_zero
        (K := K) hv2 hv3 hc0 hc1) hpencil
  · rcases hr with ⟨hu2, hu3pos, hu4⟩
    subst u1
    subst u2
    subst u4
    exact
      (weightedSparseRankThreeEndpointPencil_det_ne_zero
        (K := K) hv2 hv4 hu3pos hc0 hc1) hpencil
  · rcases hsp with ⟨hu2pos, hu3, hu4pos⟩
    subst u1
    subst u3
    have hrigid := thirdZero_weightedPencil_base_eq_one_and_cross
      (K := K)
      (A := v2) (B := v3) (C := v4)
      (Q := u2) (S := u4)
      hv3 hu2pos hu4pos hc0 hc1 hpencil
    have hv3one : v3 = 1 := hrigid.1
    have hcross : v2 * u4 = v4 * u2 := hrigid.2
    have hsNat : b * v2 = b + a * v4 := by
      simpa [hv3one] using hBal0
    have heNat : a + b * u2 = a * u4 := by
      simpa using hBal1
    have hsZ :
        (b : ℤ) * (v2 : ℤ) = (b : ℤ) + (a : ℤ) * (v4 : ℤ) := by
      exact_mod_cast hsNat
    have heZ :
        (a : ℤ) + (b : ℤ) * (u2 : ℤ) = (a : ℤ) * (u4 : ℤ) := by
      exact_mod_cast heNat
    have hcrossZ :
        (v2 : ℤ) * (u4 : ℤ) = (v4 : ℤ) * (u2 : ℤ) := by
      exact_mod_cast hcross
    have hzeroZ :
        (a : ℤ) * (v4 : ℤ) + (b : ℤ) * (u4 : ℤ) = 0 := by
      linear_combination
        (v4 : ℤ) * heZ + (b : ℤ) * hcrossZ - (u4 : ℤ) * hsZ
    have hav4 : (0 : ℤ) < (a : ℤ) * (v4 : ℤ) := by
      exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hv4)
    have hbu4 : (0 : ℤ) < (b : ℤ) * (u4 : ℤ) := by
      exact mul_pos (by exact_mod_cast hb) (by exact_mod_cast hu4pos)
    linarith
  · rcases hrq with ⟨hu2pos, hu3pos, hu4⟩
    subst u1
    subst u4
    have hrigid := fourthZero_weightedPencil_base_eq_one_and_cross
      (K := K)
      (A := v2) (B := v3) (C := v4)
      (Q := u2) (R := u3)
      hv4 hu2pos hu3pos hc0 hc1 hpencil
    have hv4one : v4 = 1 := hrigid.1
    have hcross : v2 * u3 = v3 * u2 := hrigid.2
    have hsNat : b * v2 = b * v3 + a := by
      simpa [hv4one] using hBal0
    have heNat : a + b * u2 = b * u3 := by
      simpa using hBal1
    have hsZ :
        (b : ℤ) * (v2 : ℤ) = (b : ℤ) * (v3 : ℤ) + (a : ℤ) := by
      exact_mod_cast hsNat
    have heZ :
        (a : ℤ) + (b : ℤ) * (u2 : ℤ) = (b : ℤ) * (u3 : ℤ) := by
      exact_mod_cast heNat
    have hcrossZ :
        (v2 : ℤ) * (u3 : ℤ) = (v3 : ℤ) * (u2 : ℤ) := by
      exact_mod_cast hcross
    have hzeroZ :
        (a : ℤ) * (v2 : ℤ) + (a : ℤ) * (u2 : ℤ) = 0 := by
      linear_combination
        (v2 : ℤ) * heZ - (u2 : ℤ) * hsZ + (b : ℤ) * hcrossZ
    have hav2 : (0 : ℤ) < (a : ℤ) * (v2 : ℤ) := by
      exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hv2)
    have hau2 : (0 : ℤ) < (a : ℤ) * (u2 : ℤ) := by
      exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hu2pos)
    linarith

end

end HC4.RationalRigidity
