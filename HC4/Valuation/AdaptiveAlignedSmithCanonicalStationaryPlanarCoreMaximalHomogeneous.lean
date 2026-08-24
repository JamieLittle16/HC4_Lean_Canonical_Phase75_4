import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreBinaryPlanarisation
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# Maximal homogeneous layer of the stationary binary core

After exact binary planarisation, the difficult stationary wall core is an
honest binary polynomial `Q` with vanishing Hessian determinant.  This file
selects its maximal ordinary homogeneous component and proves that the
singular-Hessian equation descends to that component.  In degree at least two,
the green binary Hesse theorem then identifies the maximal component with a
scalar multiple of a power of one linear form.

This is the canonical direction that the next cross-degree argument will lock
all lower active degrees to.  No JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Ordinary integer weight on the two binary coordinates. -/
def binaryOrdinaryIntegerWeight (_ : Fin 2) : ℤ := 1

/-- Integer ordinary weight is the cast of `Finsupp.degree`. -/
theorem binaryOrdinaryIntegerWeight_eq_degree
    (d : Fin 2 →₀ ℕ) :
    Finsupp.weight binaryOrdinaryIntegerWeight d = (d.degree : ℤ) := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype]
  · simp [binaryOrdinaryIntegerWeight]
  · intro i
    simp
  · intro i
    simp

/-- Exact ordinary-degree component of a binary polynomial. -/
noncomputable def binaryOrdinaryDegreeComponent
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ) : MvPolynomial (Fin 2) K :=
  HC4.Polynomial.initialForm binaryOrdinaryIntegerWeight D Q

/-- Every binary ordinary-degree component is homogeneous in the usual sense. -/
theorem binaryOrdinaryDegreeComponent_isHomogeneous
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ) :
    (binaryOrdinaryDegreeComponent Q D).IsHomogeneous D := by
  intro d hd
  unfold binaryOrdinaryDegreeComponent at hd
  rw [HC4.Polynomial.coeff_initialForm] at hd
  split at hd
  · have hint :
        Finsupp.weight binaryOrdinaryIntegerWeight d = (D : ℤ) := ‹_›
    have hdeg : d.degree = D := by
      have hw := binaryOrdinaryIntegerWeight_eq_degree d
      rw [hint] at hw
      exact_mod_cast hw.symm
    have hweightOne :
        Finsupp.weight (1 : Fin 2 → ℕ) d = d.degree :=
      (congrFun Finsupp.degree_eq_weight_one d).symm
    exact hweightOne.trans hdeg
  · exact (hd rfl).elim

/-- A nonzero binary polynomial has a maximal ordinary degree whose exact
component is nonzero and which bounds every support monomial. -/
theorem exists_maximal_binaryOrdinaryDegreeComponent
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0) :
    ∃ D : ℕ,
      binaryOrdinaryDegreeComponent Q D ≠ 0 ∧
      (∀ d ∈ Q.support, d.degree ≤ D) := by
  classical
  have hsupp : Q.support.Nonempty := by
    exact MvPolynomial.support_nonempty.mpr hQ
  rcases Finset.exists_max_image Q.support Finsupp.degree hsupp with
    ⟨d, hd, hmax⟩
  refine ⟨d.degree, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg
      (fun P : MvPolynomial (Fin 2) K => MvPolynomial.coeff d P) hzero
    change MvPolynomial.coeff d
      (binaryOrdinaryDegreeComponent Q d.degree) = 0 at hcoeff
    unfold binaryOrdinaryDegreeComponent at hcoeff
    rw [HC4.Polynomial.coeff_initialForm,
      binaryOrdinaryIntegerWeight_eq_degree] at hcoeff
    simp at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
  · intro q hq
    exact hmax q hq

/-- On two variables, the project Hessian determinant is exactly the binary
directional determinant in coordinates `(0,1)`. -/
theorem hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet
    (Q : MvPolynomial (Fin 2) K) :
    HC4.Polynomial.hessianDeterminant Q =
      binaryDirectionalHessianDet (0 : Fin 2) 1 Q := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [Matrix.det_fin_two]
  simp only [HC4.Polynomial.hessian_apply]
  unfold binaryDirectionalHessianDet directionalSecondDerivative
    directionalMixedDerivative
  rw [pderiv_comm_backport 1 0 Q]
  ring

/-- Vanishing of the full binary Hessian determinant descends to a maximal
ordinary homogeneous component. -/
theorem binaryOrdinaryDegreeComponent_det_zero_of_maximal
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
      (binaryOrdinaryDegreeComponent Q D) = 0 := by
  have hweight : HC4.Polynomial.IsWeightLE
      binaryOrdinaryIntegerWeight D Q := by
    intro d hd
    rw [binaryOrdinaryIntegerWeight_eq_degree]
    exact_mod_cast hmax d hd
  have hfull : HC4.Polynomial.hessianDeterminant Q = 0 := by
    rw [hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet]
    exact hdet
  have hcomponent :=
    HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
      binaryOrdinaryIntegerWeight D Q hweight hfull
  rw [hessianDeterminant_finTwo_eq_binaryDirectionalHessianDet] at hcomponent
  exact hcomponent

/-- Maximal-layer normal form for a nonzero singular-Hessian binary polynomial.
The low-degree case is retained explicitly; in every nonlinear case the top
homogeneous layer is exactly a scalar multiple of one linear-form power. -/
inductive BinarySingularHessianMaximalLayerFrontier
    (Q : MvPolynomial (Fin 2) K) : Type (u + 1)
  | lowDegree
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
  | nonlinearLinearPower
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)

/-- Construct the canonical maximal homogeneous layer of any nonzero binary
singular-Hessian polynomial. -/
theorem binarySingularHessian_maximalLayerFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianMaximalLayerFrontier Q) := by
  rcases exists_maximal_binaryOrdinaryDegreeComponent Q hQ with
    ⟨D, hHne, hmax⟩
  let H := binaryOrdinaryDegreeComponent Q D
  by_cases hD : 2 ≤ D
  · have hhom : H.IsHomogeneous D := by
      exact binaryOrdinaryDegreeComponent_isHomogeneous Q D
    have hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0 := by
      exact binaryOrdinaryDegreeComponent_det_zero_of_maximal Q D hmax hdet
    rcases binaryHomogeneous_eq_linearFormPow_of_hessianDet_zero
        H D hhom hHne hD hHdet with ⟨a, c, hnormal⟩
    exact ⟨.nonlinearLinearPower D H hD rfl hHne hmax a c hnormal⟩
  · have hDlow : D ≤ 1 := by omega
    exact ⟨.lowDegree D H hDlow rfl hHne hmax⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The transverse HC4 binary core equipped with its canonical maximal
homogeneous layer. -/
structure DirectClosingCanonicalSquareBinaryMaximalLayerData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Type (u + 1) where
  binaryData : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq
  maximalLayer : BinarySingularHessianMaximalLayerFrontier binaryData.binaryFace

/-- Every transverse stationary binary core has a canonical maximal-layer
certificate. -/
theorem DirectClosingCanonicalSquareBinaryStationaryCoreData.toMaximalLayerData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq) :
    Nonempty (DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) := by
  rcases binarySingularHessian_maximalLayerFrontier
      D.binaryFace D.binaryFace_ne_zero D.binary_det_zero with ⟨M⟩
  exact ⟨{ binaryData := D, maximalLayer := M }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
