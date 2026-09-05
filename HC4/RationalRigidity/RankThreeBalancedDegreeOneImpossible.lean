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

The implementation here deliberately classifies the primitive endpoint before
constructing the weighted determinant pencil.  This prevents Lean from
rewriting a large generic matrix determinant through endpoint equalities.
Each of the four terminal shapes is compiled behind its own small interface.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/- A specialised `M = 1` wrapper around the generic supported-endpoint
boundary theorem. -/
set_option maxHeartbeats 1000000 in
theorem supported_rankThree_degreeOne_endpoint_zero_compact
    {v2 v3 v4 u1 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hu1 : 0 < u1)
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
    (hdet : hessianDeterminant F = 0) :
    u1 = 1 ∧ (u2 = 0 ∨ u3 = 0 ∨ u4 = 0) := by
  exact supported_rankThree_edge_endpoint_zero
    (K := K)
    (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
    (M := 1) (F := F)
    hv2 hv3 hv4 (by decide) hu1 hsupp hstart hend hdet

/- A primitive `u₁ = 1` wrapper around the degree-one endpoint-pencil
realisation. -/
set_option maxHeartbeats 1000000 in
theorem supported_rankThree_primitive_degreeOne_pencil_det_zero_compact
    {v2 v3 v4 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 u4 1 F)
    (hdet : hessianDeterminant F = 0) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 1 u2 u3 u4 1 F
    (weightedRankThreeEndpointPencil
      (K := K)
      (v2 : K) (v3 : K) (v4 : K)
      (1 : K) (u2 : K) (u3 : K) (u4 : K)
      (phi.coeff 0) (phi.coeff 1)).det = 0 := by
  simpa only [Nat.cast_one] using
    (supported_rankThree_degreeOne_endpointPencil_det_zero
      (K := K)
      (v2 := v2) (v3 := v3) (v4 := v4)
      (u1 := 1) (u2 := u2) (u3 := u3) (u4 := u4)
      (F := F) (by decide) hsupp hdet)

/- The primitive `p` endpoint is impossible once the degree-one edge has been
specialised before forming its weighted pencil. -/
set_option maxHeartbeats 400000 in
theorem supported_rankThree_primitive_p_pencil_impossible
    {v2 v3 v4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 0 0 1 1 F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 0 0 1 1 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 0 0 1 1 1) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := rankThreeLineCoefficientPolynomial v2 v3 v4 1 0 0 1 1 F
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
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) 0 0 1 (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using
      (supported_rankThree_primitive_degreeOne_pencil_det_zero_compact
        (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
        (u2 := 0) (u3 := 0) (u4 := 1) (F := F) hsupp hdet)
  exact
    (weightedPTransitionRankThreeEndpointPencil_det_ne_zero
      (K := K) hv2 hv3 hc0 hc1) hpencil

/- The sparse primitive endpoint is likewise impossible after specialising the
endpoint first. -/
set_option maxHeartbeats 400000 in
theorem supported_rankThree_primitive_sparse_pencil_impossible
    {v2 v3 v4 u3 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv4 : 0 < v4) (hu3 : 0 < u3)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 0 u3 0 1 F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 0 u3 0 1 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 0 u3 0 1 1) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := rankThreeLineCoefficientPolynomial v2 v3 v4 1 0 u3 0 1 F
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
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) 0 (u3 : K) 0 (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using
      (supported_rankThree_primitive_degreeOne_pencil_det_zero_compact
        (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
        (u2 := 0) (u3 := u3) (u4 := 0) (F := F) hsupp hdet)
  exact
    (weightedSparseRankThreeEndpointPencil_det_ne_zero
      (K := K) hv2 hv4 hu3 hc0 hc1) hpencil

/- The third-coordinate-zero one-zero branch is pure finite arithmetic once
A18.5.49 has supplied the base equality and cross product. -/
set_option maxHeartbeats 600000 in
theorem balanced_primitive_rankThree_thirdZero_pencil_impossible
    {a b v2 v3 v4 u2 u4 : ℕ}
    {c0 c1 : K}
    (ha : 0 < a) (hb : 0 < b)
    (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hu2 : 0 < u2) (hu4 : 0 < u4)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hBal0 : b * v2 = b * v3 + a * v4)
    (hBal1 : a + b * u2 = a * u4)
    (hpencil :
      (weightedRankThreeEndpointPencil
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) 0 (u4 : K) c0 c1).det = 0) :
    False := by
  have hrigid := thirdZero_weightedPencil_base_eq_one_and_cross
    (K := K)
    (A := v2) (B := v3) (C := v4)
    (Q := u2) (S := u4) (c0 := c0) (c1 := c1)
    hv3 hu2 hu4 hc0 hc1 hpencil
  have hv3one : v3 = 1 := hrigid.1
  have hcross : v2 * u4 = v4 * u2 := hrigid.2
  have hsNat : b * v2 = b + a * v4 := by
    simpa [hv3one] using hBal0
  have hsZ :
      (b : ℤ) * (v2 : ℤ) = (b : ℤ) + (a : ℤ) * (v4 : ℤ) := by
    exact_mod_cast hsNat
  have heZ :
      (a : ℤ) + (b : ℤ) * (u2 : ℤ) = (a : ℤ) * (u4 : ℤ) := by
    exact_mod_cast hBal1
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
    exact mul_pos (by exact_mod_cast hb) (by exact_mod_cast hu4)
  linarith

/- The fourth-coordinate-zero one-zero branch is the cyclic counterpart. -/
set_option maxHeartbeats 600000 in
theorem balanced_primitive_rankThree_fourthZero_pencil_impossible
    {a b v2 v3 v4 u2 u3 : ℕ}
    {c0 c1 : K}
    (ha : 0 < a)
    (hv2 : 0 < v2) (hv4 : 0 < v4)
    (hu2 : 0 < u2) (hu3 : 0 < u3)
    (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hBal0 : b * v2 = b * v3 + a * v4)
    (hBal1 : a + b * u2 = b * u3)
    (hpencil :
      (weightedRankThreeEndpointPencil
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) 0 c0 c1).det = 0) :
    False := by
  have hrigid := fourthZero_weightedPencil_base_eq_one_and_cross
    (K := K)
    (A := v2) (B := v3) (C := v4)
    (Q := u2) (R := u3) (c0 := c0) (c1 := c1)
    hv4 hu2 hu3 hc0 hc1 hpencil
  have hv4one : v4 = 1 := hrigid.1
  have hcross : v2 * u3 = v3 * u2 := hrigid.2
  have hsNat : b * v2 = b * v3 + a := by
    simpa [hv4one] using hBal0
  have hsZ :
      (b : ℤ) * (v2 : ℤ) = (b : ℤ) * (v3 : ℤ) + (a : ℤ) := by
    exact_mod_cast hsNat
  have heZ :
      (a : ℤ) + (b : ℤ) * (u2 : ℤ) = (b : ℤ) * (u3 : ℤ) := by
    exact_mod_cast hBal1
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
    exact mul_pos (by exact_mod_cast ha) (by exact_mod_cast hu2)
  linarith

/- The supported third-zero branch compiles its pencil only after the shape is
fixed, then passes just scalar data to the arithmetic helper. -/
set_option maxHeartbeats 500000 in
theorem supported_rankThree_primitive_thirdZero_pencil_impossible
    {a b v2 v3 v4 u2 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hu2 : 0 < u2) (hu4 : 0 < u4)
    (hBal0 : b * v2 = b * v3 + a * v4)
    (hBal1 : a + b * u2 = a * u4)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 0 u4 1 F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 u2 0 u4 1 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 u2 0 u4 1 1) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := rankThreeLineCoefficientPolynomial v2 v3 v4 1 u2 0 u4 1 F
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
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) 0 (u4 : K) (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using
      (supported_rankThree_primitive_degreeOne_pencil_det_zero_compact
        (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
        (u2 := u2) (u3 := 0) (u4 := u4) (F := F) hsupp hdet)
  exact balanced_primitive_rankThree_thirdZero_pencil_impossible
    (K := K) ha hb hv3 hv4 hu2 hu4 hc0 hc1 hBal0 hBal1 hpencil

/- The supported fourth-zero branch is the cyclic analogue. -/
set_option maxHeartbeats 500000 in
theorem supported_rankThree_primitive_fourthZero_pencil_impossible
    {a b v2 v3 v4 u2 u3 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (hv2 : 0 < v2) (hv4 : 0 < v4)
    (hu2 : 0 < u2) (hu3 : 0 < u3)
    (hBal0 : b * v2 = b * v3 + a * v4)
    (hBal1 : a + b * u2 = b * u3)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 0 1 F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 u2 u3 0 1 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp v2 v3 v4 1 u2 u3 0 1 1) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := rankThreeLineCoefficientPolynomial v2 v3 v4 1 u2 u3 0 1 F
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
        (K := K) (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) 0 (phi.coeff 0) (phi.coeff 1)).det = 0 := by
    simpa [phi] using
      (supported_rankThree_primitive_degreeOne_pencil_det_zero_compact
        (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
        (u2 := u2) (u3 := u3) (u4 := 0) (F := F) hsupp hdet)
  exact balanced_primitive_rankThree_fourthZero_pencil_impossible
    (K := K) ha hv2 hv4 hu2 hu3 hc0 hc1 hBal0 hBal1 hpencil

/- **Balanced degree-one rank-three terminal impossibility.**  The final
assembly carries no determinant-valued term across the endpoint-shape split. -/
set_option maxHeartbeats 500000 in
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
  have hendpoint := supported_rankThree_degreeOne_endpoint_zero_compact
    (K := K)
    (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
    (F := F)
    hv2 hv3 hv4 hu1 hsupp hstart hend hdet
  have hzero : u2 = 0 ∨ u3 = 0 ∨ u4 = 0 := hendpoint.2
  have hu1one : u1 = 1 := hendpoint.1
  subst u1

  let e0 := rankThreeLineExponentFinsupp v2 v3 v4 1 u2 u3 u4 1 0
  let e1 := rankThreeLineExponentFinsupp v2 v3 v4 1 u2 u3 u4 1 1
  have he0mem : e0 ∈ F.support := MvPolynomial.mem_support_iff.mpr hstart
  have he1mem : e1 ∈ F.support := MvPolynomial.mem_support_iff.mpr hend
  have hBal0raw : IsBalancedExponent a b e0 := hbalanced e0 he0mem
  have hBal1raw : IsBalancedExponent a b e1 := hbalanced e1 he1mem
  have hBal0 : b * v2 = b * v3 + a * v4 := by
    simpa [e0, IsBalancedExponent, rankThreeLineExponentFinsupp_apply] using hBal0raw
  have hBal1 : a + b * u2 = b * u3 + a * u4 := by
    simpa [e1, IsBalancedExponent, rankThreeLineExponentFinsupp_apply] using hBal1raw
  have hBalPrimitive : Balanced a b ⟨1, u2, u3, u4⟩ := by
    change a * 1 + b * u2 = b * u3 + a * u4
    simpa using hBal1
  have hshape := balanced_unit_transverseBoundary_shape ha hb hBalPrimitive hzero

  rcases hshape with hp | hr | hsp | hrq
  · rcases hp with ⟨hu2, hu3, hu4⟩
    subst u2
    subst u3
    subst u4
    exact supported_rankThree_primitive_p_pencil_impossible
      (K := K) hv2 hv3 hsupp hstart hend hdet
  · rcases hr with ⟨hu2, hu3pos, hu4⟩
    subst u2
    subst u4
    exact supported_rankThree_primitive_sparse_pencil_impossible
      (K := K) hv2 hv4 hu3pos hsupp hstart hend hdet
  · rcases hsp with ⟨hu2pos, hu3, hu4pos⟩
    subst u3
    have hBal1' : a + b * u2 = a * u4 := by
      simpa using hBal1
    exact supported_rankThree_primitive_thirdZero_pencil_impossible
      (K := K) ha hb hv3 hv4 hu2pos hu4pos hBal0 hBal1'
      hsupp hstart hend hdet
  · rcases hrq with ⟨hu2pos, hu3pos, hu4⟩
    subst u4
    have hBal1' : a + b * u2 = b * u3 := by
      simpa using hBal1
    exact supported_rankThree_primitive_fourthZero_pencil_impossible
      (K := K) ha hv2 hv4 hu2pos hu3pos hBal0 hBal1'
      hsupp hstart hend hdet

end

end HC4.RationalRigidity
