import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitStaggeredSource
import Mathlib.Tactic

/-!
# Assemble the source-honest staggered first-kernel break

The preceding two files separated the live endpoint into:

* a complete, determinant-preserving four-block whose active three coordinates
  are the already-certified first-deficit rank-three roof; and
* exact source-layer statements saying that the missing Hessian row vanishes
  before the least opposite-opening order and genuinely breaks at that order.

This file packages those facts as
`StaggeredSingularFirstKernelBreakFourBlockData`.  The generic staggered
matrix theorem then forces the later diagonal coefficient to vanish and
produces a concrete nonzero mixed principal minor at the opposite-opening
order.

This is a genuine family-level rank-three-to-rank-two-kernel event.  No repair
state is changed and no auxiliary parameter order is identified with a
zero-defect blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem coeff_zero_det_fin_three
    {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    M.det.coeff 0 =
      (Matrix.of fun i j => (M i j).coeff 0).det := by
  have h := (Polynomial.evalRingHom (0 : R)).map_det M
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

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

/-- The active-three determinant has zero constant coefficient in the left
orientation because the central layer is independent of source coordinate
`1`. -/
theorem firstDeficitLeftStaggeredBlock_active_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (firstKernelBreakActiveThreeDet
      G.firstDeficitLeftStaggeredBlock).coeff 0 = 0 := by
  rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq,
    coeff_zero_det_fin_three]
  apply Matrix.det_eq_zero_of_row_eq_zero (1 : Fin 3)
  intro j
  change
    (parameterFirstHessian P.centralDeficitFamily
      (firstDeficitLeftActiveIndex (1 : Fin 3))
      (firstDeficitLeftActiveIndex j)).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  fin_cases j <;>
    simp [-standardTwoZero_pderiv_two_eq_A,
      -standardTwoZero_pderiv_three_eq_C,
      firstDeficitLeftActiveIndex,
      HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial,
      standardTwoZeroA, standardTwoZeroC,
      G.central_one_zero, G.central_two_zero]

/-- Symmetric zero constant coefficient in the right orientation. -/
theorem firstDeficitRightStaggeredBlock_active_coeff_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (firstKernelBreakActiveThreeDet
      G.firstDeficitRightStaggeredBlock).coeff 0 = 0 := by
  rw [G.firstDeficitRightStaggeredBlock_activeThree_eq,
    coeff_zero_det_fin_three]
  apply Matrix.det_eq_zero_of_row_eq_zero (1 : Fin 3)
  intro j
  change
    (parameterFirstHessian P.centralDeficitFamily
      (firstDeficitRightActiveIndex (1 : Fin 3))
      (firstDeficitRightActiveIndex j)).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  fin_cases j <;>
    simp [-standardTwoZero_pderiv_two_eq_A,
      -standardTwoZero_pderiv_three_eq_C,
      firstDeficitRightActiveIndex,
      HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial,
      standardTwoZeroA, standardTwoZeroC,
      G.central_one_zero, G.central_two_zero]

/-- All active-three determinant coefficients below the first deficit order
vanish in the left orientation, including the constant coefficient. -/
theorem firstDeficitLeftStaggeredBlock_active_lower_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∀ n : ℕ, n < G.firstDeficitOrder →
      (firstKernelBreakActiveThreeDet
        G.firstDeficitLeftStaggeredBlock).coeff n = 0 := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    exact G.firstDeficitLeftStaggeredBlock_active_coeff_zero
      hthree houtThree
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
    exact G.firstDeficitLeftActiveHessian_det_gap n hnpos hn

/-- Right-oriented active determinant gap. -/
theorem firstDeficitRightStaggeredBlock_active_lower_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∀ n : ℕ, n < G.firstDeficitOrder →
      (firstKernelBreakActiveThreeDet
        G.firstDeficitRightStaggeredBlock).coeff n = 0 := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    exact G.firstDeficitRightStaggeredBlock_active_coeff_zero
      hthree houtThree
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
    exact G.firstDeficitRightActiveHessian_det_gap n hnpos hn

theorem leftBlock_q_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitLeftStaggeredBlock.q.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (2 : Fin 4) (opposite 1 + opposite 2) hminimal hn (0 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 0 2).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (0 : Fin 4) 2]
    exact hrow
  simpa [firstDeficitLeftStaggeredBlock,
    firstDeficitLeftStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem leftBlock_s_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitLeftStaggeredBlock.s.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (2 : Fin 4) (opposite 1 + opposite 2) hminimal hn (1 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 1 2).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (1 : Fin 4) 2]
    exact hrow
  simpa [firstDeficitLeftStaggeredBlock,
    firstDeficitLeftStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem leftBlock_y_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitLeftStaggeredBlock.y.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (2 : Fin 4) (opposite 1 + opposite 2) hminimal hn (3 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 3 2).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (3 : Fin 4) 2]
    exact hrow
  simpa [firstDeficitLeftStaggeredBlock,
    firstDeficitLeftStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem leftBlock_z_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitLeftStaggeredBlock.z.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (2 : Fin 4) (opposite 1 + opposite 2) hminimal hn (2 : Fin 4)
  simpa [firstDeficitLeftStaggeredBlock,
    firstDeficitLeftStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hrow

theorem rightBlock_q_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitRightStaggeredBlock.q.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (1 : Fin 4) (opposite 1 + opposite 2) hminimal hn (0 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 0 1).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (0 : Fin 4) 1]
    exact hrow
  simpa [firstDeficitRightStaggeredBlock,
    firstDeficitRightStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem rightBlock_s_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitRightStaggeredBlock.s.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (1 : Fin 4) (opposite 1 + opposite 2) hminimal hn (2 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 2 1).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (2 : Fin 4) 1]
    exact hrow
  simpa [firstDeficitRightStaggeredBlock,
    firstDeficitRightStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem rightBlock_y_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitRightStaggeredBlock.y.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (1 : Fin 4) (opposite 1 + opposite 2) hminimal hn (3 : Fin 4)
  have hsym :
      (parameterFirstHessian P.centralDeficitFamily 3 1).coeff n = 0 := by
    rw [parameterFirstHessian_symmetric
      P.centralDeficitFamily (3 : Fin 4) 1]
    exact hrow
  simpa [firstDeficitRightStaggeredBlock,
    firstDeficitRightStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hsym

theorem rightBlock_z_coeff_eq_zero_before
    {opposite : Fin 4 →₀ ℕ}
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2)
    {n : ℕ} (hn : n < opposite 1 + opposite 2) :
    G.firstDeficitRightStaggeredBlock.z.coeff n = 0 := by
  have hrow :=
    missingHessianRow_coeff_eq_zero_of_lt
      (1 : Fin 4) (opposite 1 + opposite 2) hminimal hn (1 : Fin 4)
  simpa [firstDeficitRightStaggeredBlock,
    firstDeficitRightStaggeredMatrix,
    GeneralFourBlock.ofSymmetricMatrix] using hrow

/-- The later source row break becomes exactly one of `q,s,y,z` in the left
staggered block. -/
theorem firstDeficitLeftStaggeredBlock_kernel_break
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hfirstTwo : 2 ≤ G.firstDeficitOrder) :
    G.firstDeficitLeftStaggeredBlock.q.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitLeftStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitLeftStaggeredBlock.y.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitLeftStaggeredBlock.z.coeff
          (opposite 1 + opposite 2) ≠ 0 := by
  rcases G.exists_missingHessianRow_coeff_ne_zero_at
      (2 : Fin 4) hop hop2 hstrict hfirstTwo with
    ⟨i, hi⟩
  fin_cases i
  · left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 0 2).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (0 : Fin 4) 2]
      exact hi
    simpa [firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs
  · right; left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 1 2).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (1 : Fin 4) 2]
      exact hi
    simpa [firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs
  · right; right; right
    simpa [firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hi
  · right; right; left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 3 2).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (3 : Fin 4) 2]
      exact hi
    simpa [firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs

/-- Symmetric right staggered kernel break. -/
theorem firstDeficitRightStaggeredBlock_kernel_break
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hfirstTwo : 2 ≤ G.firstDeficitOrder) :
    G.firstDeficitRightStaggeredBlock.q.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitRightStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitRightStaggeredBlock.y.coeff
          (opposite 1 + opposite 2) ≠ 0 ∨
      G.firstDeficitRightStaggeredBlock.z.coeff
          (opposite 1 + opposite 2) ≠ 0 := by
  rcases G.exists_missingHessianRow_coeff_ne_zero_at
      (1 : Fin 4) hop hop1 hstrict hfirstTwo with
    ⟨i, hi⟩
  fin_cases i
  · left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 0 1).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (0 : Fin 4) 1]
      exact hi
    simpa [firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs
  · right; right; right
    simpa [firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hi
  · right; left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 2 1).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (2 : Fin 4) 1]
      exact hi
    simpa [firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs
  · right; right; left
    have hs :
        (parameterFirstHessian P.centralDeficitFamily 3 1).coeff
            (opposite 1 + opposite 2) ≠ 0 := by
      rw [parameterFirstHessian_symmetric
        P.centralDeficitFamily (3 : Fin 4) 1]
      exact hi
    simpa [firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hs

/-- Constant left staggered entry `b` vanishes because the central
source monomial has zero exponent in coordinate `1`. -/
theorem firstDeficitLeftStaggeredBlock_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.b.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (0 : Fin 4) 1).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_one_zero]

/-- Constant left staggered entry `d` vanishes. -/
theorem firstDeficitLeftStaggeredBlock_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.d.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (1 : Fin 4) 1).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_one_zero]

/-- Constant left staggered entry `r` vanishes. -/
theorem firstDeficitLeftStaggeredBlock_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.r.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (1 : Fin 4) 3).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_one_zero]

/-- Constant right staggered entry `b` vanishes because the central
source monomial has zero exponent in coordinate `2`. -/
theorem firstDeficitRightStaggeredBlock_base_b_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.b.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (0 : Fin 4) 2).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_two_zero]

/-- Constant right staggered entry `d` vanishes. -/
theorem firstDeficitRightStaggeredBlock_base_d_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.d.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (2 : Fin 4) 2).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_two_zero]

/-- Constant right staggered entry `r` vanishes. -/
theorem firstDeficitRightStaggeredBlock_base_r_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.r.coeff 0 = 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily
      (2 : Fin 4) 3).coeff 0 = 0
  rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C,
    HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_monomial,
    standardTwoZeroA, standardTwoZeroC,
    G.central_two_zero]

/-- The constant outer active minor in either staggered orientation is the
retained central `(0,3)` principal Hessian minor. -/
theorem firstDeficitLeftStaggeredBlock_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitLeftStaggeredBlock.a.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.x.coeff 0 -
        G.firstDeficitLeftStaggeredBlock.p.coeff 0 *
          G.firstDeficitLeftStaggeredBlock.p.coeff 0 ≠ 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily 0 0).coeff 0 *
          (parameterFirstHessian P.centralDeficitFamily 3 3).coeff 0 -
        (parameterFirstHessian P.centralDeficitFamily 0 3).coeff 0 *
          (parameterFirstHessian P.centralDeficitFamily 0 3).coeff 0 ≠ 0
  repeat' rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  rw [← G.exposure_face_eq]
  simpa [HC4.Polynomial.hessianPrincipalMinor,
    parameterFirstHessian_symmetric] using G.exposure_rankTwo_minor

theorem firstDeficitRightStaggeredBlock_base_outer_minor_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitRightStaggeredBlock.a.coeff 0 *
          G.firstDeficitRightStaggeredBlock.x.coeff 0 -
        G.firstDeficitRightStaggeredBlock.p.coeff 0 *
          G.firstDeficitRightStaggeredBlock.p.coeff 0 ≠ 0 := by
  change
    (parameterFirstHessian P.centralDeficitFamily 0 0).coeff 0 *
          (parameterFirstHessian P.centralDeficitFamily 3 3).coeff 0 -
        (parameterFirstHessian P.centralDeficitFamily 0 3).coeff 0 *
          (parameterFirstHessian P.centralDeficitFamily 0 3).coeff 0 ≠ 0
  repeat' rw [parameterFirstHessian_coeff,
    centralDeficitFamily_layer_zero_eq G hthree houtThree]
  rw [← G.exposure_face_eq]
  simpa [HC4.Polynomial.hessianPrincipalMinor,
    parameterFirstHessian_symmetric] using G.exposure_rankTwo_minor

/-- Exact left-oriented staggered certificate with source order projections exposed
as equalities.  The theorem is opaque to downstream modules, avoiding
reduction through the proof-carrying record. -/
theorem exists_leftStaggeredBreakData
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∃ E : StaggeredSingularFirstKernelBreakFourBlockData
        (MvPolynomial (Fin 4) K),
      E.block = G.firstDeficitLeftStaggeredBlock ∧
      E.activeOrder = G.firstDeficitOrder ∧
      E.kernelOrder = opposite 1 + opposite 2 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  refine ⟨{
    block := G.firstDeficitLeftStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitLeftStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := ?_
    q_lower_zero := ?_
    s_lower_zero := ?_
    y_lower_zero := ?_
    z_lower_zero := ?_
    determinantCore_eq_zero :=
      G.firstDeficitLeftStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitLeftStaggeredBlock_kernel_break
        hop hop2 hstrict hfirstTwo
  }, rfl, rfl, rfl⟩
  · rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
    exact G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
  · intro n hn
    exact G.leftBlock_q_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_s_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_y_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.leftBlock_z_coeff_eq_zero_before hminimal hn

/-- Right-oriented mirror of `exists_leftStaggeredBreakData`. -/
theorem exists_rightStaggeredBreakData
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∃ E : StaggeredSingularFirstKernelBreakFourBlockData
        (MvPolynomial (Fin 4) K),
      E.block = G.firstDeficitRightStaggeredBlock ∧
      E.activeOrder = G.firstDeficitOrder ∧
      E.kernelOrder = opposite 1 + opposite 2 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  refine ⟨{
    block := G.firstDeficitRightStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitRightStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := ?_
    q_lower_zero := ?_
    s_lower_zero := ?_
    y_lower_zero := ?_
    z_lower_zero := ?_
    determinantCore_eq_zero :=
      G.firstDeficitRightStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitRightStaggeredBlock_kernel_break
        hop hop1 hstrict hfirstTwo
  }, rfl, rfl, rfl⟩
  · rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
    exact G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
  · intro n hn
    exact G.rightBlock_q_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_s_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_y_coeff_eq_zero_before hminimal hn
  · intro n hn
    exact G.rightBlock_z_coeff_eq_zero_before hminimal hn

/-- **Source-honest staggered first-kernel-break certificate.** -/
theorem firstDeficit_staggeredFirstKernelBreak
    (geometry : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
      (StaggeredSingularFirstKernelBreakFourBlockData
        (MvPolynomial (Fin 4) K)) := by
  have hfirstTwo : 2 ≤ geometry.firstDeficitOrder :=
    firstDeficitOrder_two_le geometry hthree houtThree
  rcases geometry.firstDeficit_oppositeOpening hthree houtThree with ⟨O⟩
  cases O with
  | left first opposite hfirst hfirst1 hfirst2 huniq hop hop2 hstrict hminimal =>
      refine ⟨{
        block := geometry.firstDeficitLeftStaggeredBlock
        activeOrder := geometry.firstDeficitOrder
        kernelOrder := opposite 1 + opposite 2
        activeOrder_pos := geometry.firstDeficitOrder_pos
        active_lt_kernel := hstrict
        active_lower_zero :=
          geometry.firstDeficitLeftStaggeredBlock_active_lower_zero
            hthree houtThree
        active_coeff_ne_zero := ?_
        q_lower_zero := ?_
        s_lower_zero := ?_
        y_lower_zero := ?_
        z_lower_zero := ?_
        determinantCore_eq_zero :=
          geometry.firstDeficitLeftStaggeredBlock_determinantCore_eq_zero
        kernel_break :=
          geometry.firstDeficitLeftStaggeredBlock_kernel_break
            hop hop2 hstrict hfirstTwo
      }⟩
      · rw [geometry.firstDeficitLeftStaggeredBlock_activeThree_eq]
        exact geometry.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
          hthree houtThree hfirst hfirst1 hfirst2 huniq
      · intro n hn
        exact geometry.leftBlock_q_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.leftBlock_s_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.leftBlock_y_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.leftBlock_z_coeff_eq_zero_before hminimal hn
  | right first opposite hfirst hfirst1 hfirst2 huniq hop hop1 hstrict hminimal =>
      refine ⟨{
        block := geometry.firstDeficitRightStaggeredBlock
        activeOrder := geometry.firstDeficitOrder
        kernelOrder := opposite 1 + opposite 2
        activeOrder_pos := geometry.firstDeficitOrder_pos
        active_lt_kernel := hstrict
        active_lower_zero :=
          geometry.firstDeficitRightStaggeredBlock_active_lower_zero
            hthree houtThree
        active_coeff_ne_zero := ?_
        q_lower_zero := ?_
        s_lower_zero := ?_
        y_lower_zero := ?_
        z_lower_zero := ?_
        determinantCore_eq_zero :=
          geometry.firstDeficitRightStaggeredBlock_determinantCore_eq_zero
        kernel_break :=
          geometry.firstDeficitRightStaggeredBlock_kernel_break
            hop hop1 hstrict hfirstTwo
      }⟩
      · rw [geometry.firstDeficitRightStaggeredBlock_activeThree_eq]
        exact geometry.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
          hthree houtThree hfirst hfirst1 hfirst2 huniq
      · intro n hn
        exact geometry.rightBlock_q_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.rightBlock_s_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.rightBlock_y_coeff_eq_zero_before hminimal hn
      · intro n hn
        exact geometry.rightBlock_z_coeff_eq_zero_before hminimal hn

/-- The generic staggered theorem immediately forces a genuine nonzero
principal two-by-two coefficient-layer minor at the later opening order. -/
theorem firstDeficit_exists_staggeredRankTwoMinor
    (geometry : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ E : StaggeredSingularFirstKernelBreakFourBlockData
        (MvPolynomial (Fin 4) K),
      (E.block.a.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
          E.block.q.coeff E.kernelOrder * E.block.q.coeff E.kernelOrder ≠ 0) ∨
      (E.block.d.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
          E.block.s.coeff E.kernelOrder * E.block.s.coeff E.kernelOrder ≠ 0) ∨
      (E.block.x.coeff E.kernelOrder * E.block.z.coeff E.kernelOrder -
          E.block.y.coeff E.kernelOrder * E.block.y.coeff E.kernelOrder ≠ 0) := by
  rcases geometry.firstDeficit_staggeredFirstKernelBreak hthree houtThree with ⟨E⟩
  exact ⟨E, E.exists_nonzero_principalMinor_at_kernelOrder⟩


/-- In the left orientation, the diagonal coefficient of the still-missing
coordinate vanishes at the exact opposite-opening order.  This is the
source-facing form of the generic staggered diagonal cancellation, with the
actual opposite monomial and its order retained. -/
theorem firstDeficitLeftStaggeredBlock_kernelDiagonal_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    G.firstDeficitLeftStaggeredBlock.z.coeff
        (opposite 1 + opposite 2) = 0 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  let E : StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := {
    block := G.firstDeficitLeftStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitLeftStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := by
      rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
      exact G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
        hthree houtThree hfirst hfirst1 hfirst2 huniq
    q_lower_zero := by
      intro n hn
      exact G.leftBlock_q_coeff_eq_zero_before hminimal hn
    s_lower_zero := by
      intro n hn
      exact G.leftBlock_s_coeff_eq_zero_before hminimal hn
    y_lower_zero := by
      intro n hn
      exact G.leftBlock_y_coeff_eq_zero_before hminimal hn
    z_lower_zero := by
      intro n hn
      exact G.leftBlock_z_coeff_eq_zero_before hminimal hn
    determinantCore_eq_zero :=
      G.firstDeficitLeftStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitLeftStaggeredBlock_kernel_break
        hop hop2 hstrict hfirstTwo
  }
  exact E.kernelDiagonal_coeff_kernelOrder_eq_zero

/-- Right-oriented source-facing diagonal cancellation at the selected
opposite-opening order. -/
theorem firstDeficitRightStaggeredBlock_kernelDiagonal_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    G.firstDeficitRightStaggeredBlock.z.coeff
        (opposite 1 + opposite 2) = 0 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  let E : StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := {
    block := G.firstDeficitRightStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitRightStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := by
      rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
      exact G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
        hthree houtThree hfirst hfirst1 hfirst2 huniq
    q_lower_zero := by
      intro n hn
      exact G.rightBlock_q_coeff_eq_zero_before hminimal hn
    s_lower_zero := by
      intro n hn
      exact G.rightBlock_s_coeff_eq_zero_before hminimal hn
    y_lower_zero := by
      intro n hn
      exact G.rightBlock_y_coeff_eq_zero_before hminimal hn
    z_lower_zero := by
      intro n hn
      exact G.rightBlock_z_coeff_eq_zero_before hminimal hn
    determinantCore_eq_zero :=
      G.firstDeficitRightStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitRightStaggeredBlock_kernel_break
        hop hop1 hstrict hfirstTwo
  }
  exact E.kernelDiagonal_coeff_kernelOrder_eq_zero

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
