import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitRees
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Polynomial.RankTwoKernelSecondVariation
import HC4.Polynomial.CentralDeficitBinarySpecialisation
import HC4.Polynomial.MonomialHessianPrincipalMinor
import Mathlib.Tactic

/-!
# The first positive central-deficit layer has singular binary Hessian

The source-honest total-deficit Rees family has layer zero equal to the
central monomial, identically zero four-variable Hessian determinant, a
nonzero active (0,3) Hessian minor on layer zero, and a canonical least
positive parameter layer.

Move the parameter outside, specialise source coordinates by

    (x0,x1,x2,x3) |-> (1,U,V,1),

and apply the exact rank-two second-variation gap theorem.  The arbitrary
second-order source layer is retained but disappears algebraically.  The
conclusion is that the first positive layer, viewed as an honest binary
polynomial in U,V, has vanishing binary Hessian determinant.

This is the source-honest replacement for the failed generic stationary
source/profile determinant comparison.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

noncomputable def firstDeficitOrder : ℕ :=
  firstPositiveActualParameterOrder P.centralDeficitFamily
    G.centralDeficitFamily_hasPositiveActualLayer

noncomputable def firstDeficitLayer : MvPolynomial (Fin 4) K :=
  familyParameterLayer P.centralDeficitFamily G.firstDeficitOrder

noncomputable def firstDeficitBinaryFace : MvPolynomial (Fin 2) K :=
  centralDeficitBinarySpecialisation (K := K) G.firstDeficitLayer

theorem firstDeficitOrder_pos :
    0 < G.firstDeficitOrder := by
  exact firstPositiveActualParameterOrder_pos
    P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer

theorem firstDeficitLayer_ne_zero :
    G.firstDeficitLayer ≠ 0 := by
  exact firstPositiveActualParameterLayer_ne_zero
    P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer

theorem firstDeficitLayer_support
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ G.firstDeficitLayer.support) :
    e ∈ P.carrier.support ∧ e 1 + e 2 = G.firstDeficitOrder := by
  simpa [firstDeficitLayer] using
    (P.centralDeficitFamily_layer_mem_iff G.firstDeficitOrder e).1 he

theorem firstDeficitLayer_deficit_injective
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ G.firstDeficitLayer.support)
    (hf : f ∈ G.firstDeficitLayer.support)
    (hproj :
      binaryDeficitExponent f = binaryDeficitExponent e) :
    f = e := by
  have hec := (G.firstDeficitLayer_support he).1
  have hfc := (G.firstDeficitLayer_support hf).1
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hproj
  have h2 := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hproj
  exact F.support_eq_of_deficits_eq hthree houtThree hfc hec
    (by simpa using h1) (by simpa using h2)

theorem firstDeficitBinaryFace_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitBinaryFace ≠ 0 := by
  exact centralDeficitBinarySpecialisation_ne_zero_of_injective
    G.firstDeficitLayer G.firstDeficitLayer_ne_zero
    (by
      intro e he f hf hproj
      exact G.firstDeficitLayer_deficit_injective
        hthree houtThree he hf hproj)

theorem firstDeficitBinaryFace_isHomogeneous :
    G.firstDeficitBinaryFace.IsHomogeneous G.firstDeficitOrder := by
  apply centralDeficitBinarySpecialisation_isHomogeneous
  intro e he
  exact (G.firstDeficitLayer_support he).2

noncomputable def binaryParameterHessian :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  (Polynomial.mapRingHom
      (centralDeficitBinarySpecialisation (K := K))).mapMatrix
    (parameterFirstHessian P.centralDeficitFamily)

theorem binaryParameterHessian_coeff
    (n : ℕ) (i j : Fin 4) :
    (G.binaryParameterHessian i j).coeff n =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily n) i j) := by
  change
    ((parameterFirstHessian P.centralDeficitFamily i j).map
      (centralDeficitBinarySpecialisation (K := K))).coeff n = _
  rw [Polynomial.coeff_map, parameterFirstHessian_coeff]

theorem binaryParameterHessian_det_zero :
    G.binaryParameterHessian.det = 0 := by
  let phi := centralDeficitBinarySpecialisation (K := K)
  let Phi := Polynomial.mapRingHom phi
  have hdet0 :
      (parameterFirstHessian P.centralDeficitFamily).det = 0 := by
    rw [parameterFirstHessian_det, P.centralDeficitFamily_hessian_zero]
    simp
  have hmap :=
    Phi.map_det (parameterFirstHessian P.centralDeficitFamily)
  change
    (Phi.mapMatrix
      (parameterFirstHessian P.centralDeficitFamily)).det = 0
  rw [← hmap, hdet0]
  simp

theorem binaryParameterHessian_gap
    (i j : Fin 4) :
    HasNoPositiveParameterCoeffBelow G.firstDeficitOrder
      (G.binaryParameterHessian i j) := by
  intro n hnpos hnlt
  rw [G.binaryParameterHessian_coeff]
  have hz :
      familyParameterLayer P.centralDeficitFamily n = 0 :=
    familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
      P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer
      hnpos hnlt
  rw [hz]
  simp [HC4.Polynomial.hessian_apply]

theorem central_active_exponents_pos :
    0 < G.central 0 ∧ 0 < G.central 3 := by
  have hminor := G.exposure_rankTwo_minor
  rw [G.exposure_face_eq] at hminor
  constructor
  · by_contra hnot
    have h0 : G.central 0 = 0 := Nat.eq_zero_of_not_pos hnot
    apply hminor
    unfold HC4.Polynomial.hessianPrincipalMinor
    simp [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial, h0]
  · by_contra hnot
    have h3 : G.central 3 = 0 := Nat.eq_zero_of_not_pos hnot
    apply hminor
    unfold HC4.Polynomial.hessianPrincipalMinor
    simp [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial, h3]

noncomputable def centralBinaryCore :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
    ((MvPolynomial.coeff G.central P.carrier) •
      exponentHessianCore (K := K) G.central)

theorem centralBinaryCore_eq_rankTwoBase :
    G.centralBinaryCore =
      rankTwoZeroKernelBase
        (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
        (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [centralBinaryCore, rankTwoZeroKernelBase,
      exponentHessianCore, G.central_one_zero, G.central_two_zero]

theorem centralBinaryCore_activeDet_ne_zero :
    G.centralBinaryCore 0 0 * G.centralBinaryCore 3 3 -
        G.centralBinaryCore 0 3 * G.centralBinaryCore 3 0 ≠ 0 := by
  let z := MvPolynomial.coeff G.central P.carrier
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp G.central_mem
  rcases G.central_active_exponents_pos with ⟨h0, h3⟩
  have h0K : ((G.central 0 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h0)
  have h3K : ((G.central 3 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h3)
  have hsum : 1 < G.central 0 + G.central 3 := by omega
  have hlast :
      1 - (G.central 0 : K) - (G.central 3 : K) ≠ 0 := by
    intro h
    have heq : (G.central 0 : K) + (G.central 3 : K) = 1 := by
      linear_combination h
    have hnat : G.central 0 + G.central 3 = 1 := by
      exact_mod_cast heq
    omega
  have hscalar :
      z ^ 2 * (G.central 0 : K) * (G.central 3 : K) *
          (1 - (G.central 0 : K) - (G.central 3 : K)) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact pow_ne_zero 2 hz
    · exact h0K
    · exact h3K
    · exact hlast
  have hC :
      (MvPolynomial.C
        (z ^ 2 * (G.central 0 : K) * (G.central 3 : K) *
          (1 - (G.central 0 : K) - (G.central 3 : K))) :
        MvPolynomial (Fin 2) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hscalar
  simpa [centralBinaryCore, exponentHessianCore, z,
    G.central_one_zero, G.central_two_zero] using hC

theorem binaryParameterHessian_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (fun i j => (G.binaryParameterHessian i j).coeff 0) =
      G.centralBinaryCore := by
  apply Matrix.ext
  intro i j
  rw [G.binaryParameterHessian_coeff]
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  have hcore :=
    centralDeficitBinarySpecialisation_hessian_monomial_of_deficits_zero
      (K := K) G.central (MvPolynomial.coeff G.central P.carrier)
      G.central_one_zero G.central_two_zero
  exact congrFun (congrFun hcore i) j

theorem firstDeficitBinaryFace_hessian_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
      G.firstDeficitBinaryFace = 0 := by
  let B : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 2) K) :=
    fun i j => (G.binaryParameterHessian i j).coeff G.firstDeficitOrder
  have hbase :
      ∀ i j,
        (G.binaryParameterHessian i j).coeff 0 =
          rankTwoZeroKernelBase
            (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
            (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) i j := by
    intro i j
    have h0 := congrFun
      (congrFun (G.binaryParameterHessian_coeff_zero hthree houtThree) i) j
    rw [G.centralBinaryCore_eq_rankTwoBase] at h0
    exact h0
  have hkernel :=
    kernelBlock_det_eq_zero_of_polynomialMatrix_gap_domain
      G.firstDeficitOrder_pos G.binaryParameterHessian
      (fun i j => G.binaryParameterHessian_gap i j)
      (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
      (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3)
      hbase
      (by
        norm_num :
        (2 : MvPolynomial (Fin 2) K) ≠ 0)
      G.centralBinaryCore_activeDet_ne_zero
      G.binaryParameterHessian_det_zero
  change B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 at hkernel
  have hB :
      ∀ i j,
        B i j =
          centralDeficitBinarySpecialisation (K := K)
            (HC4.Polynomial.hessian G.firstDeficitLayer i j) := by
    intro i j
    dsimp [B]
    simpa [firstDeficitLayer] using
      G.binaryParameterHessian_coeff G.firstDeficitOrder i j
  unfold firstDeficitBinaryFace
  unfold binaryDirectionalHessianDet directionalSecondDerivative
    directionalMixedDerivative
  simp only [← HC4.Polynomial.hessian_apply]
  rw [hessian_zero_zero_centralDeficitBinarySpecialisation,
    hessian_one_one_centralDeficitBinarySpecialisation,
    hessian_zero_one_centralDeficitBinarySpecialisation,
    hessian_one_zero_centralDeficitBinarySpecialisation]
  simpa [hB] using hkernel

end QsOtherFacetPrLeftVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
