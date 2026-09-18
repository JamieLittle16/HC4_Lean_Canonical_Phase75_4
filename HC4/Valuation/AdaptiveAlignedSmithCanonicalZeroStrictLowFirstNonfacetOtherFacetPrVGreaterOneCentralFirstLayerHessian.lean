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
  familyParameterLayer P.centralDeficitFamily firstDeficitOrder G

noncomputable def firstDeficitBinaryFace : MvPolynomial (Fin 2) K :=
  HC4.Polynomial.centralDeficitBinarySpecialisation (K := K) firstDeficitLayer G

theorem firstDeficitOrder_pos :
    0 < firstDeficitOrder G := by
  exact firstPositiveActualParameterOrder_pos
    P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer

theorem firstDeficitLayer_ne_zero :
    firstDeficitLayer G ≠ 0 := by
  exact firstPositiveActualParameterLayer_ne_zero
    P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer

theorem firstDeficitLayer_support
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ firstDeficitLayer G.support) :
    e ∈ P.carrier.support ∧ e 1 + e 2 = firstDeficitOrder G := by
  simpa [firstDeficitLayer] using
    (P.centralDeficitFamily_layer_mem_iff firstDeficitOrder G e).1 he

theorem firstDeficitLayer_deficit_injective
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ firstDeficitLayer G.support)
    (hf : f ∈ firstDeficitLayer G.support)
    (hproj :
      HC4.Polynomial.binaryDeficitExponent f = HC4.Polynomial.binaryDeficitExponent e) :
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
    firstDeficitBinaryFace G ≠ 0 := by
  exact HC4.Polynomial.HC4.Polynomial.centralDeficitBinarySpecialisation_ne_zero_of_injective
    firstDeficitLayer G G.firstDeficitLayer_ne_zero
    (by
      intro e he f hf hproj
      exact G.firstDeficitLayer_deficit_injective
        hthree houtThree he hf hproj)

theorem firstDeficitBinaryFace_isHomogeneous :
    firstDeficitBinaryFace G.IsHomogeneous firstDeficitOrder G := by
  apply HC4.Polynomial.HC4.Polynomial.centralDeficitBinarySpecialisation_isHomogeneous
  intro e he
  exact (G.firstDeficitLayer_support he).2

include G in
noncomputable def binaryParameterHessian :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  (Polynomial.mapRingHom
      (HC4.Polynomial.centralDeficitBinarySpecialisation (K := K))).mapMatrix
    (parameterFirstHessian P.centralDeficitFamily)

theorem binaryParameterHessian_coeff
    (n : ℕ) (i j : Fin 4) :
    (binaryParameterHessian G i j).coeff n =
      HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian
          (familyParameterLayer P.centralDeficitFamily n) i j) := by
  change
    ((parameterFirstHessian P.centralDeficitFamily i j).map
      (HC4.Polynomial.centralDeficitBinarySpecialisation (K := K))).coeff n = _
  rw [Polynomial.coeff_map, parameterFirstHessian_coeff]

theorem binaryParameterHessian_det_zero :
    binaryParameterHessian G.det = 0 := by
  let phi := HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
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
    HasNoPositiveParameterCoeffBelow firstDeficitOrder G
      (binaryParameterHessian G i j) := by
  intro n hnpos hnlt
  rw [G.binaryParameterHessian_coeff]
  have hz :
      familyParameterLayer P.centralDeficitFamily n = 0 :=
    familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
      P.centralDeficitFamily G.centralDeficitFamily_hasPositiveActualLayer
      hnpos hnlt
  rw [hz]
  simp [HC4.Polynomial.hessian_apply]

theorem central_active_exponents_pos
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    0 < G.central 0 ∧ 0 < G.central 3 := by
  have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
    exact_mod_cast F.locked.ell_pos
  have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
  have hnOneZ : (0 : ℤ) < (F.highest.n : ℤ) - 1 := by
    exact_mod_cast (show 1 < F.highest.n by omega)
  have hcWall := F.support_deficit_wall hthree houtThree G.central_mem
  rw [G.central_one_zero, G.central_two_zero] at hcWall
  norm_num at hcWall
  have hc0GtOne : 1 < G.central 0 := by
    by_contra hnot
    have hc0Le : G.central 0 ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (G.central 0) with hc0Zero | hc0PosNat
    · rw [hc0Zero] at hcWall
      norm_num at hcWall
      have hnPosZ : (0 : ℤ) < (F.highest.n : ℤ) := by omega
      have hrightPos :
          (0 : ℤ) < (F.locked.ell : ℤ) * (F.highest.n : ℤ) :=
        mul_pos hellZ hnPosZ
      nlinarith only [hcWall, hnOneZ, hrightPos]
    · have hc0Eq : G.central 0 = 1 := by omega
      rw [hc0Eq] at hcWall
      norm_num at hcWall
      rcases hcWall with hellZero | hnOneZero
      · exact (Nat.ne_of_gt F.locked.ell_pos) hellZero
      · exact (ne_of_gt hnOneZ) hnOneZero
  have hc0Pos : 0 < G.central 0 := by omega
  have hcurve := (F.support_staircase_equations
    hthree houtThree G.central_mem).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hcurve
  push_cast at hcurve
  rw [G.central_one_zero, G.central_two_zero] at hcurve
  norm_num at hcurve
  have hc3Z :
      (G.central 3 : ℤ) =
        (F.V : ℤ) * ((G.central 0 : ℤ) - 1) := by
    nlinarith only [hcurve]
  have hVPos : 0 < F.V := lt_trans Nat.zero_lt_one F.V_gt_one
  have hVZ : (0 : ℤ) < (F.V : ℤ) := by exact_mod_cast hVPos
  have hc0MinusOneZ : (0 : ℤ) < (G.central 0 : ℤ) - 1 := by
    exact_mod_cast hc0GtOne
  have hc3ZPos : (0 : ℤ) < (G.central 3 : ℤ) := by
    rw [hc3Z]
    exact mul_pos hVZ hc0MinusOneZ
  have hc3Pos : 0 < G.central 3 := by exact_mod_cast hc3ZPos
  exact ⟨hc0Pos, hc3Pos⟩

noncomputable def centralBinaryCore :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
    ((MvPolynomial.coeff G.central P.carrier) •
      HC4.Polynomial.exponentHessianCore (K := K) G.central)

theorem centralBinaryCore_eq_rankTwoBase :
    G.centralBinaryCore =
      HC4.Polynomial.rankTwoZeroKernelBase
        (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
        (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [centralBinaryCore, HC4.Polynomial.rankTwoZeroKernelBase,
      HC4.Polynomial.exponentHessianCore, G.central_one_zero, G.central_two_zero]

theorem centralBinaryCore_activeDet_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralBinaryCore 0 0 * G.centralBinaryCore 3 3 -
        G.centralBinaryCore 0 3 * G.centralBinaryCore 3 0 ≠ 0 := by
  let z := MvPolynomial.coeff G.central P.carrier
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp G.central_mem
  rcases G.central_active_exponents_pos hthree houtThree with ⟨h0, h3⟩
  have h0K : ((G.central 0 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h0)
  have h3K : ((G.central 3 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h3)
  have hsum : 1 < G.central 0 + G.central 3 := by omega
  have hlast :
      1 - (G.central 0 : K) - (G.central 3 : K) ≠ 0 := by
    intro h
    have heq : (G.central 0 : K) + (G.central 3 : K) = 1 := by
      linear_combination -h
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
  simpa [centralBinaryCore, HC4.Polynomial.exponentHessianCore, z,
    G.central_one_zero, G.central_two_zero] using hC

theorem binaryParameterHessian_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (fun i j => (binaryParameterHessian G i j).coeff 0) =
      G.centralBinaryCore := by
  apply Matrix.ext
  intro i j
  rw [G.binaryParameterHessian_coeff]
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  have hcore :=
    HC4.Polynomial.HC4.Polynomial.centralDeficitBinarySpecialisation_hessian_monomial_of_deficits_zero
      (K := K) G.central (MvPolynomial.coeff G.central P.carrier)
      G.central_one_zero G.central_two_zero
  exact congrFun (congrFun hcore i) j

theorem firstDeficitBinaryFace_hessian_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
      firstDeficitBinaryFace G = 0 := by
  let B : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 2) K) :=
    fun i j => (binaryParameterHessian G i j).coeff firstDeficitOrder G
  have hbase :
      ∀ i j,
        (binaryParameterHessian G i j).coeff 0 =
          HC4.Polynomial.rankTwoZeroKernelBase
            (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
            (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) i j := by
    intro i j
    have h0 := congrFun
      (congrFun (G.binaryParameterHessian_coeff_zero hthree houtThree) i) j
    rw [G.centralBinaryCore_eq_rankTwoBase] at h0
    exact h0
  have hkernel :=
    HC4.Polynomial.kernelBlock_det_eq_zero_of_polynomialMatrix_gap_domain
      G.firstDeficitOrder_pos binaryParameterHessian G
      (fun i j => G.binaryParameterHessian_gap i j)
      (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
      (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3)
      hbase
      (by
        norm_num :
        (2 : MvPolynomial (Fin 2) K) ≠ 0)
      (G.centralBinaryCore_activeDet_ne_zero hthree houtThree)
      G.binaryParameterHessian_det_zero
  change B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 at hkernel
  have hB :
      ∀ i j,
        B i j =
          HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
            (HC4.Polynomial.hessian firstDeficitLayer G i j) := by
    intro i j
    dsimp [B]
    simpa [firstDeficitLayer] using
      G.binaryParameterHessian_coeff firstDeficitOrder G i j
  unfold firstDeficitBinaryFace
  unfold binaryDirectionalHessianDet directionalSecondDerivative
    directionalMixedDerivative
  simp only [← HC4.Polynomial.hessian_apply]
  rw [HC4.Polynomial.hessian_zero_zero_HC4.Polynomial.centralDeficitBinarySpecialisation,
    HC4.Polynomial.hessian_one_one_HC4.Polynomial.centralDeficitBinarySpecialisation,
    HC4.Polynomial.hessian_zero_one_HC4.Polynomial.centralDeficitBinarySpecialisation,
    HC4.Polynomial.hessian_one_zero_HC4.Polynomial.centralDeficitBinarySpecialisation]
  simpa [hB] using hkernel

end QsOtherFacetPrLeftVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
