import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSingleton
import HC4.Polynomial.RankTwoToRankThreeRoofLinearCoefficient
import Mathlib.Tactic

/-!
# The first positive deficit layer opens the central Hessian to rank three

The central total-deficit Rees family has a rank-two layer-zero Hessian with
active coordinates `0,3`.  The first positive source layer is now known to be
one honest monomial on exactly one deficit roof, with order `D >= 2`.

On the corresponding three-coordinate roof, the constant Hessian block has a
one-dimensional kernel and the first positive layer has a nonzero diagonal
entry in that kernel direction.  The generic three-by-three parameter-gap
lemma therefore makes the roof determinant nonzero.

The result keeps the source monomial and its orientation.  This provenance is
needed by the next step, which waits for the honest opposite deficit direction
to open the remaining rank-three kernel.  No repair state is changed here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

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

/-- Source indices `(0,1,3)`, i.e. the roof with deficit coordinate `2=0`. -/
def firstDeficitRoofOneIndex : Fin 3 → Fin 4 :=
  ![(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)]

/-- Source indices `(0,2,3)`, i.e. the roof with deficit coordinate `1=0`. -/
def firstDeficitRoofTwoIndex : Fin 3 → Fin 4 :=
  ![(0 : Fin 4), (2 : Fin 4), (3 : Fin 4)]

/-- Binary-specialised parameter Hessian restricted to the first roof. -/
noncomputable def firstDeficitRoofOneMatrix
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  (binaryParameterHessian G).submatrix
    firstDeficitRoofOneIndex firstDeficitRoofOneIndex

/-- Binary-specialised parameter Hessian restricted to the second roof. -/
noncomputable def firstDeficitRoofTwoMatrix
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  (binaryParameterHessian G).submatrix
    firstDeficitRoofTwoIndex firstDeficitRoofTwoIndex

theorem firstDeficitRoofOne_gap
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow G.firstDeficitOrder
      (firstDeficitRoofOneMatrix G i j) := by
  exact binaryParameterHessian_gap G
    (firstDeficitRoofOneIndex i) (firstDeficitRoofOneIndex j)

theorem firstDeficitRoofTwo_gap
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow G.firstDeficitOrder
      (firstDeficitRoofTwoMatrix G i j) := by
  exact binaryParameterHessian_gap G
    (firstDeficitRoofTwoIndex i) (firstDeficitRoofTwoIndex j)

theorem firstDeficitRoofOne_coeff_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∀ i j,
      (firstDeficitRoofOneMatrix G i j).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
          (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) i j := by
  intro i j
  have h0 := congrFun
    (congrFun (binaryParameterHessian_coeff_zero G hthree houtThree)
      (firstDeficitRoofOneIndex i))
    (firstDeficitRoofOneIndex j)
  rw [centralBinaryCore_eq_rankTwoBase G] at h0
  fin_cases i <;> fin_cases j <;>
    simpa [firstDeficitRoofOneMatrix, firstDeficitRoofOneIndex,
      HC4.Polynomial.rankTwoRoofZeroKernelBase,
      HC4.Polynomial.rankTwoZeroKernelBase] using h0

theorem firstDeficitRoofTwo_coeff_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∀ i j,
      (firstDeficitRoofTwoMatrix G i j).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
          (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3) i j := by
  intro i j
  have h0 := congrFun
    (congrFun (binaryParameterHessian_coeff_zero G hthree houtThree)
      (firstDeficitRoofTwoIndex i))
    (firstDeficitRoofTwoIndex j)
  rw [centralBinaryCore_eq_rankTwoBase G] at h0
  fin_cases i <;> fin_cases j <;>
    simpa [firstDeficitRoofTwoMatrix, firstDeficitRoofTwoIndex,
      HC4.Polynomial.rankTwoRoofZeroKernelBase,
      HC4.Polynomial.rankTwoZeroKernelBase] using h0

/-- A singleton first layer on the `e₂=0` roof has a nonzero first roof
diagonal at the exact first-deficit order. -/
theorem firstDeficitRoofOne_middleDiagonal_ne_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} {A : K}
    (hA : A ≠ 0)
    (hlayer : G.firstDeficitLayer = MvPolynomial.monomial e A)
    (he1 : e 1 = G.firstDeficitOrder)
    (he2 : e 2 = 0) :
    (firstDeficitRoofOneMatrix G 1 1).coeff G.firstDeficitOrder ≠ 0 := by
  have hface :
      G.firstDeficitBinaryFace =
        MvPolynomial.monomial (HC4.Polynomial.binaryDeficitExponent e) A := by
    unfold firstDeficitBinaryFace
    rw [hlayer]
    exact HC4.Polynomial.centralDeficitBinarySpecialisation_monomial_eq e A
  have hD : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  have hbinary :
      2 ≤ HC4.Polynomial.binaryDeficitExponent e (0 : Fin 2) := by
    simpa [HC4.Polynomial.binaryDeficitExponent_zero, he1] using hD
  have hsecond :
      directionalSecondDerivative (0 : Fin 2) G.firstDeficitBinaryFace ≠ 0 := by
    rw [hface]
    exact directionalSecondDerivative_monomial_ne_zero_of_two_le
      (K := K) (0 : Fin 2) hA hbinary
  have hsource :
      HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
          (HC4.Polynomial.hessian G.firstDeficitLayer 1 1) ≠ 0 := by
    rw [← HC4.Polynomial.hessian_zero_zero_centralDeficitBinarySpecialisation]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using hsecond
  change (binaryParameterHessian G 1 1).coeff G.firstDeficitOrder ≠ 0
  rw [binaryParameterHessian_coeff G]
  simpa [firstDeficitLayer] using hsource

/-- Symmetric singleton first layer on the `e₁=0` roof. -/
theorem firstDeficitRoofTwo_middleDiagonal_ne_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} {A : K}
    (hA : A ≠ 0)
    (hlayer : G.firstDeficitLayer = MvPolynomial.monomial e A)
    (he1 : e 1 = 0)
    (he2 : e 2 = G.firstDeficitOrder) :
    (firstDeficitRoofTwoMatrix G 1 1).coeff G.firstDeficitOrder ≠ 0 := by
  have hface :
      G.firstDeficitBinaryFace =
        MvPolynomial.monomial (HC4.Polynomial.binaryDeficitExponent e) A := by
    unfold firstDeficitBinaryFace
    rw [hlayer]
    exact HC4.Polynomial.centralDeficitBinarySpecialisation_monomial_eq e A
  have hD : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  have hbinary :
      2 ≤ HC4.Polynomial.binaryDeficitExponent e (1 : Fin 2) := by
    simpa [HC4.Polynomial.binaryDeficitExponent_one, he2] using hD
  have hsecond :
      directionalSecondDerivative (1 : Fin 2) G.firstDeficitBinaryFace ≠ 0 := by
    rw [hface]
    exact directionalSecondDerivative_monomial_ne_zero_of_two_le
      (K := K) (1 : Fin 2) hA hbinary
  have hsource :
      HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
          (HC4.Polynomial.hessian G.firstDeficitLayer 2 2) ≠ 0 := by
    rw [← HC4.Polynomial.hessian_one_one_centralDeficitBinarySpecialisation]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using hsecond
  change (binaryParameterHessian G 2 2).coeff G.firstDeficitOrder ≠ 0
  rw [binaryParameterHessian_coeff G]
  simpa [firstDeficitLayer] using hsource

/-- Provenance-rich first-deficit rank-three event. -/
inductive FirstDeficitRankThreeRoofGeometry
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) : Prop
  | roofOne
      (e : Fin 4 →₀ ℕ) (A : K)
      (coefficient_ne_zero : A ≠ 0)
      (layer_eq : G.firstDeficitLayer = MvPolynomial.monomial e A)
      (one_eq : e 1 = G.firstDeficitOrder)
      (two_zero : e 2 = 0)
      (minor_ne_zero : (firstDeficitRoofOneMatrix G).det ≠ 0)
  | roofTwo
      (e : Fin 4 →₀ ℕ) (A : K)
      (coefficient_ne_zero : A ≠ 0)
      (layer_eq : G.firstDeficitLayer = MvPolynomial.monomial e A)
      (one_zero : e 1 = 0)
      (two_eq : e 2 = G.firstDeficitOrder)
      (minor_ne_zero : (firstDeficitRoofTwoMatrix G).det ≠ 0)

/-- **The first honest deficit layer opens the central rank-two Hessian to
rank three on exactly one source roof.** -/
theorem firstDeficitRankThreeRoofGeometry
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    FirstDeficitRankThreeRoofGeometry G := by
  rcases G.firstDeficitLayer_eq_monomial_axis hthree houtThree with
    hleft | hright
  · rcases hleft with ⟨e, A, hA, hlayer, he1, he2⟩
    have hdiag :=
      firstDeficitRoofOne_middleDiagonal_ne_zero
        G hthree houtThree hA hlayer he1 he2
    have hminor :=
      HC4.Polynomial.polynomialMatrix3_gap_det_ne_zero_of_middleDiagonal
        (G.firstDeficitOrder_pos)
        (firstDeficitRoofOneMatrix G)
        (firstDeficitRoofOne_gap G)
        (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
        (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3)
        (firstDeficitRoofOne_coeff_zero G hthree houtThree)
        (centralBinaryCore_activeDet_ne_zero G hthree houtThree)
        hdiag
    exact .roofOne e A hA hlayer he1 he2 hminor
  · rcases hright with ⟨e, A, hA, hlayer, he1, he2⟩
    have hdiag :=
      firstDeficitRoofTwo_middleDiagonal_ne_zero
        G hthree houtThree hA hlayer he1 he2
    have hminor :=
      HC4.Polynomial.polynomialMatrix3_gap_det_ne_zero_of_middleDiagonal
        (G.firstDeficitOrder_pos)
        (firstDeficitRoofTwoMatrix G)
        (firstDeficitRoofTwo_gap G)
        (G.centralBinaryCore 0 0) (G.centralBinaryCore 0 3)
        (G.centralBinaryCore 3 0) (G.centralBinaryCore 3 3)
        (firstDeficitRoofTwo_coeff_zero G hthree houtThree)
        (centralBinaryCore_activeDet_ne_zero G hthree houtThree)
        hdiag
    exact .roofTwo e A hA hlayer he1 he2 hminor

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
