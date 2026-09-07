import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetActivePivot

/-!
# A nonzero three-coordinate Hessian minor on the actual ray

The two-coordinate active pivot alone does not certify that the constant
Schur block is nonzero. Here the three-coordinate minor on (1,2,3) detects
the original rank-three endpoint: its constant longitudinal coefficient is
c0^3*A*B*C*(A+B+C-1). This is nonzero for positive integral A,B,C.
This concerns the actual ray Hessian, not the original zero-clock blocker.
-/
namespace HC4.Valuation
noncomputable section
open HC4.Polynomial HC4.Newton
open scoped Matrix
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The principal three-coordinate minor complementary to coordinate zero. -/
def rayTransverseHessianMinor (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (Matrix.of fun i j : Fin 3 => hessian F i.succ j.succ).det

private theorem ray_transverse_entry
    {A B C P Q R : ℕ} {F : MvPolynomial (Fin 4) K}
    (hs : IsSupportedOnRankThreeLine A B C 1 P Q R 1 F)
    (i j : Fin 3) :
    let phi := rankThreeLineCoefficientPolynomial A B C 1 P Q R 1 F
    rankThreeLineSpecialisation (hessian F i.succ j.succ) =
      weightedRankThreeEndpointPencil (A : K) (B : K) (C : K)
        1 (P : K) (Q : K) (R : K) (phi.coeff 0) (phi.coeff 1) i.succ j.succ := by
  let phi := rankThreeLineCoefficientPolynomial A B C 1 P Q R 1 F
  have hd : phi.natDegree ≤ 1 :=
    rankThreeLineCoefficientPolynomial_natDegree_le A B C 1 P Q R 1 F
  have hF : F = rankThreeLinePolynomial A B C 1 P Q R 1 phi :=
    eq_rankThreeLinePolynomial_of_supported (by decide) hs
  have hm := rankThreeLineSpecialisation_eulerScaledHessian
    (K := K) (v2 := A) (v3 := B) (v4 := C)
    (u1 := 1) (u2 := P) (u3 := Q) (u4 := R)
    (M := 1) (phi := phi) hd
  have hp := eq_C_add_C_mul_X_of_natDegree_le_one phi hd
  rw [hp, rankThreePolynomialMomentHessian_one_linear_eq_endpointPencil] at hm
  have he : rankThreeLineSpecialisation (eulerScaledHessian F i.succ j.succ) =
      weightedRankThreeEndpointPencil (A : K) (B : K) (C : K)
        1 (P : K) (Q : K) (R : K) (phi.coeff 0) (phi.coeff 1) i.succ j.succ := by
    rw [hF, hp]
    have hij := congrFun (congrFun hm i.succ) j.succ
    simpa [Polynomial.coe_compRingHom_apply] using hij
  rw [eulerScaledHessian_apply] at he
  have hx (k : Fin 3) :
      rankThreeLineSpecialisation (K := K) (MvPolynomial.X k.succ) = 1 := by
    fin_cases k <;> simp [rankThreeLineSpecialisation]
  simpa only [map_mul, hx, one_mul, hessian_apply] using he

/-- The constant longitudinal coefficient sees only the original endpoint. -/
theorem rayTransverseHessianMinor_specialisation_coeff_zero
    {A B C P Q R : ℕ} {F : MvPolynomial (Fin 4) K}
    (hs : IsSupportedOnRankThreeLine A B C 1 P Q R 1 F) :
    let c := (rankThreeLineCoefficientPolynomial A B C 1 P Q R 1 F).coeff 0
    (rankThreeLineSpecialisation (rayTransverseHessianMinor F)).coeff 0 =
      c ^ 3 * (A : K) * (B : K) * (C : K) * ((A : K) + (B : K) + (C : K) - 1) := by
  unfold rayTransverseHessianMinor
  rw [Matrix.det_fin_three]
  simp only [map_sub, map_add, map_mul]
  simp only [ray_transverse_entry hs]
  simp [weightedRankThreeEndpointPencil, vectorHessianCore]
  ring

private theorem endpoint_three_scalar_ne_zero
    {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    {c : K} (hc : c ≠ 0) :
    c ^ 3 * (A : K) * (B : K) * (C : K) * ((A : K) + (B : K) + (C : K) - 1) ≠ 0 := by
  have ha : (A : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA
  have hb : (B : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hd : (C : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hC
  have hs : (A : K) + (B : K) + (C : K) - 1 ≠ 0 := by
    intro hz
    have he : (A : K) + (B : K) + (C : K) = 1 := sub_eq_zero.mp hz
    have hn : A + B + C = 1 := by exact_mod_cast he
    omega
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hc) ha) hb) hd) hs

variable [IsAlgClosed K]
namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData (K := K) state}

/-- The coefficient at the original endpoint is the actual nonzero ray coefficient. -/
theorem qsRayDegreeOneCoefficientPolynomial_coeff_zero_ne
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.qsRayDegreeOneCoefficientPolynomial.coeff 0 ≠ 0 := by
  have hv0 := ((mvRankThreeOnFacet_iff .qs C.ray.facetExponent).1 hthree).1
  have he : rankThreeLineExponentFinsupp
      (C.ray.facetExponent 1) (C.ray.facetExponent 2) (C.ray.facetExponent 3)
      1 (C.ray.outsideExponent 1) (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3) 1 0 = C.ray.facetExponent := by
    ext i
    fin_cases i <;> simp [rankThreeLineExponentFinsupp_apply, hv0]
  rw [qsRayDegreeOneCoefficientPolynomial, coeff_zero_rankThreeLineCoefficientPolynomial, he]
  exact MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face

/-- The actual ray has a nonzero three-coordinate Hessian minor. No extra
rank hypothesis on its Hessian is assumed. -/
theorem qs_ray_transverseHessianMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent) :
    rayTransverseHessianMinor C.ray.face ≠ 0 := by
  have hc := C.qsRayDegreeOneCoefficientPolynomial_coeff_zero_ne hthree
  rcases (mvRankThreeOnFacet_iff .qs C.ray.facetExponent).1 hthree with ⟨_, ha, hb, hd⟩
  have hn := endpoint_three_scalar_ne_zero (K := K) ha hb hd hc
  intro hz
  apply hn
  have he := rayTransverseHessianMinor_specialisation_coeff_zero
    (C.qs_ray_degreeOne_supportedLine hthree)
  rw [hz, map_zero, Polynomial.coeff_zero] at he
  exact he.symm

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
