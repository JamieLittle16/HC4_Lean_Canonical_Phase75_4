import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSingleton
import HC4.Polynomial.RankTwoToRankThreeRoofLinearCoefficient
import Mathlib.Tactic

/-!
# The singleton first deficit layer opens an honest rank-three roof block

The central total-deficit family has a rank-two constant Hessian layer with
active coordinates `0,3`.  The first positive layer is now known to be one
honest source monomial, lying on exactly one deficit axis, and its nonzero
deficit is at least two.

If the first monomial has deficits `(D,0)`, its `(1,1)` Hessian entry is
nonzero.  The generic three-by-three parameter-gap bridge therefore shows that
the active `(0,1,3)` Hessian determinant of the complete honest Rees family
is nonzero.  The `(0,D)` case is symmetric with active coordinates
`(0,2,3)`.

This is a genuine family-level rank-two to rank-three promotion.  It does not
change repair state and it retains all higher parameter layers.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Active coordinate order for the roof missing source coordinate `2`. -/
def firstDeficitLeftActiveIndex : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3

/-- Active coordinate order for the roof missing source coordinate `1`. -/
def firstDeficitRightActiveIndex : Fin 3 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 3

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

private theorem eq_monomial_of_support_singleton
    (Q : MvPolynomial (Fin 4) K)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ Q.support)
    (huniq : ∀ f ∈ Q.support, f = e) :
    Q = MvPolynomial.monomial e (MvPolynomial.coeff e Q) := by
  apply MvPolynomial.ext
  intro f
  by_cases hfe : f = e
  · subst f
    simp
  · have hfnot : f ∉ Q.support := by
      intro hf
      exact hfe (huniq f hf)
    have hfzero : MvPolynomial.coeff f Q = 0 :=
      MvPolynomial.notMem_support_iff.mp hfnot
    rw [hfzero]
    simp [hfe]

private theorem hessian_monomial_diagonal_ne_zero_of_two_le
    {e : Fin 4 →₀ ℕ} {z : K} {i : Fin 4}
    (hz : z ≠ 0) (hi : 2 ≤ e i) :
    HC4.Polynomial.hessian
        (MvPolynomial.monomial e z) i i ≠ 0 := by
  intro hzero
  have hmat := HC4.Polynomial.eval_one_hessian_monomial
    (K := K) e z
  have hii := congrFun (congrFun hmat i) i
  change
    MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (HC4.Polynomial.hessian
          (MvPolynomial.monomial e z) i i) =
      (z • HC4.Polynomial.exponentHessianCore (K := K) e) i i at hii
  have hzright :
      (z • HC4.Polynomial.exponentHessianCore (K := K) e) i i = 0 := by
    calc
      _ = MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
          (HC4.Polynomial.hessian
            (MvPolynomial.monomial e z) i i) := hii.symm
      _ = 0 := by rw [hzero]; simp
  have hei0 : (e i : K) ≠ 0 := by
    exact_mod_cast (show e i ≠ 0 by omega)
  have heim1 : (e i : K) - 1 ≠ 0 := by
    intro h
    have heq : (e i : K) = 1 := sub_eq_zero.mp h
    have heqNat : e i = 1 := by exact_mod_cast heq
    omega
  have hcore :
      (e i : K) * (e i : K) - (e i : K) ≠ 0 := by
    rw [show
      (e i : K) * (e i : K) - (e i : K) =
        (e i : K) * ((e i : K) - 1) by ring]
    exact mul_ne_zero hei0 heim1
  have hscalar :
      z * ((e i : K) * (e i : K) - (e i : K)) ≠ 0 :=
    mul_ne_zero hz hcore
  apply hscalar
  simpa [HC4.Polynomial.exponentHessianCore] using hzright

/-- Three-by-three parameter Hessian block on source coordinates `0,1,3`. -/
noncomputable def firstDeficitLeftActiveHessian :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  fun i j =>
    parameterFirstHessian P.centralDeficitFamily
      (firstDeficitLeftActiveIndex i)
      (firstDeficitLeftActiveIndex j)

/-- Three-by-three parameter Hessian block on source coordinates `0,2,3`. -/
noncomputable def firstDeficitRightActiveHessian :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  fun i j =>
    parameterFirstHessian P.centralDeficitFamily
      (firstDeficitRightActiveIndex i)
      (firstDeficitRightActiveIndex j)

private theorem leftActive_gap
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow G.firstDeficitOrder
      (G.firstDeficitLeftActiveHessian i j) := by
  intro n hnpos hnlt
  unfold firstDeficitLeftActiveHessian
  rw [parameterFirstHessian_coeff]
  rw [familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    P.centralDeficitFamily
    (centralDeficitFamily_hasPositiveActualLayer G) hnpos hnlt]
  simp [HC4.Polynomial.hessian_apply]

private theorem rightActive_gap
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow G.firstDeficitOrder
      (G.firstDeficitRightActiveHessian i j) := by
  intro n hnpos hnlt
  unfold firstDeficitRightActiveHessian
  rw [parameterFirstHessian_coeff]
  rw [familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    P.centralDeficitFamily
    (centralDeficitFamily_hasPositiveActualLayer G) hnpos hnlt]
  simp [HC4.Polynomial.hessian_apply]

private theorem layer_zero_eq_exposure
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
  rw [centralDeficitFamily_layer_zero_eq G hthree houtThree,
    G.exposure_face_eq]

/-- In the left-axis branch, the complete honest parameter Hessian has a
nonzero active three-by-three determinant. -/
theorem firstDeficitLeftActiveHessian_det_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ G.firstDeficitLayer.support)
    (he1 : e 1 = G.firstDeficitOrder)
    (he2 : e 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = e) :
    G.firstDeficitLeftActiveHessian.det ≠ 0 := by
  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a := H0 (0 : Fin 4) 0
  let b := H0 (0 : Fin 4) 3
  let c := H0 (3 : Fin 4) 0
  let d := H0 (3 : Fin 4) 3
  have hbase : ∀ r s,
      (G.firstDeficitLeftActiveHessian r s).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase a b c d r s := by
    intro r s
    unfold firstDeficitLeftActiveHessian
    rw [parameterFirstHessian_coeff, G.layer_zero_eq_exposure hthree houtThree]
    dsimp [a, b, c, d, H0]
    fin_cases r <;> fin_cases s <;>
      simp [firstDeficitLeftActiveIndex,
        HC4.Polynomial.rankTwoRoofZeroKernelBase,
        G.exposure_face_eq, HC4.Polynomial.hessian_apply,
        MvPolynomial.pderiv_monomial,
        G.central_one_zero, G.central_two_zero]
  have hactive : a * d - b * c ≠ 0 := by
    dsimp [a, b, c, d, H0]
    simpa [HC4.Polynomial.hessianPrincipalMinor] using
      G.exposure_rankTwo_minor
  let z := MvPolynomial.coeff e G.firstDeficitLayer
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hmono :
      G.firstDeficitLayer = MvPolynomial.monomial e z :=
    eq_monomial_of_support_singleton G.firstDeficitLayer he huniq
  have hDtwo := firstDeficitOrder_two_le G hthree houtThree
  have he1two : 2 ≤ e 1 := by omega
  have hdiag :
      HC4.Polynomial.hessian G.firstDeficitLayer
        (1 : Fin 4) 1 ≠ 0 := by
    rw [hmono]
    exact hessian_monomial_diagonal_ne_zero_of_two_le hz he1two
  intro hdet
  have hzero :=
    HC4.Polynomial.middleDiagonal_eq_zero_of_polynomialMatrix3_gap
      (G.firstDeficitOrder_pos)
      G.firstDeficitLeftActiveHessian
      (fun r s => G.leftActive_gap r s)
      a b c d hbase hactive hdet
  unfold firstDeficitLeftActiveHessian at hzero
  simp [firstDeficitLeftActiveIndex] at hzero
  rw [parameterFirstHessian_coeff] at hzero
  exact hdiag (by simpa [firstDeficitLayer] using hzero)

/-- Symmetric right-axis branch: active coordinates `0,2,3`. -/
theorem firstDeficitRightActiveHessian_det_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ G.firstDeficitLayer.support)
    (he1 : e 1 = 0)
    (he2 : e 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = e) :
    G.firstDeficitRightActiveHessian.det ≠ 0 := by
  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a := H0 (0 : Fin 4) 0
  let b := H0 (0 : Fin 4) 3
  let c := H0 (3 : Fin 4) 0
  let d := H0 (3 : Fin 4) 3
  have hbase : ∀ r s,
      (G.firstDeficitRightActiveHessian r s).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase a b c d r s := by
    intro r s
    unfold firstDeficitRightActiveHessian
    rw [parameterFirstHessian_coeff, G.layer_zero_eq_exposure hthree houtThree]
    dsimp [a, b, c, d, H0]
    fin_cases r <;> fin_cases s <;>
      simp [firstDeficitRightActiveIndex,
        HC4.Polynomial.rankTwoRoofZeroKernelBase,
        G.exposure_face_eq, HC4.Polynomial.hessian_apply,
        MvPolynomial.pderiv_monomial,
        G.central_one_zero, G.central_two_zero]
  have hactive : a * d - b * c ≠ 0 := by
    dsimp [a, b, c, d, H0]
    simpa [HC4.Polynomial.hessianPrincipalMinor] using
      G.exposure_rankTwo_minor
  let z := MvPolynomial.coeff e G.firstDeficitLayer
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hmono :
      G.firstDeficitLayer = MvPolynomial.monomial e z :=
    eq_monomial_of_support_singleton G.firstDeficitLayer he huniq
  have hDtwo := firstDeficitOrder_two_le G hthree houtThree
  have he2two : 2 ≤ e 2 := by omega
  have hdiag :
      HC4.Polynomial.hessian G.firstDeficitLayer
        (2 : Fin 4) 2 ≠ 0 := by
    rw [hmono]
    exact hessian_monomial_diagonal_ne_zero_of_two_le hz he2two
  intro hdet
  have hzero :=
    HC4.Polynomial.middleDiagonal_eq_zero_of_polynomialMatrix3_gap
      (G.firstDeficitOrder_pos)
      G.firstDeficitRightActiveHessian
      (fun r s => G.rightActive_gap r s)
      a b c d hbase hactive hdet
  unfold firstDeficitRightActiveHessian at hzero
  simp [firstDeficitRightActiveIndex] at hzero
  rw [parameterFirstHessian_coeff] at hzero
  exact hdiag (by simpa [firstDeficitLayer] using hzero)

/-- **Certified first-deficit rank-three roof alternative.** -/
theorem firstDeficit_activeRankThree
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftActiveHessian.det ≠ 0 ∨
      G.firstDeficitRightActiveHessian.det ≠ 0 := by
  rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
    hleft | hright
  · rcases hleft with ⟨e, he, he1, he2, huniq⟩
    exact Or.inl
      (G.firstDeficitLeftActiveHessian_det_ne_zero
        hthree houtThree he he1 he2 huniq)
  · rcases hright with ⟨e, he, he1, he2, huniq⟩
    exact Or.inr
      (G.firstDeficitRightActiveHessian_det_ne_zero
        hthree houtThree he he1 he2 huniq)

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
