import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreMaximalHomogeneous
import HC4.Polynomial.WeightBounds
import Mathlib.Tactic

/-!
# Exact top-layer peeling for the stationary binary core

The maximal-homogeneous theorem produces the top ordinary component `H_D` of
an honest binary stationary core.  Before using the mixed homogeneous part of
`det Hess Q = 0`, we isolate the exact remainder

    R = Q - H_D.

The existing weighted-initial-form API shows that `R` is strictly below `D`.
Hence either `R = 0`, in which case the full binary core is already its top
linear-power layer, or `R` has a canonical maximal active degree `E < D`.

This file packages that dichotomy so the next cross-degree argument receives
an exact pair of consecutive active layers and does not have to repeat any
support/degree bookkeeping.  No JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Exact residual frontier below a chosen maximal ordinary homogeneous layer.
The `nextLayer` branch records the maximal homogeneous component of the strict
lower remainder and, crucially, the strict inequality `E < D`. -/
inductive BinaryMaximalLayerResidualFrontier
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (H : MvPolynomial (Fin 2) K) : Type (u + 1)
  | collapsed
      (Q_eq_H : Q = H)
  | nextLayer
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)

/-- A support-level maximal ordinary degree gives the corresponding weak
integer-weight bound. -/
theorem isWeightLE_binaryOrdinary_of_degree_le
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D) :
    IsWeightLE binaryOrdinaryIntegerWeight D Q := by
  intro d hd
  rw [binaryOrdinaryIntegerWeight_eq_degree]
  exact_mod_cast hmax d hd

/-- **Canonical peeling below a maximal binary homogeneous layer.**

If `H` is the exact degree-`D` component and `D` bounds the support of `Q`,
then the remainder `Q-H` is strictly below `D`.  It therefore either vanishes
or has a canonical maximal active degree `E < D` with a nonzero homogeneous
component `G`. -/
theorem binaryMaximalLayer_residualFrontier
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (H : MvPolynomial (Fin 2) K)
    (H_eq : H = binaryOrdinaryDegreeComponent Q D)
    (hmax : ∀ d ∈ Q.support, d.degree ≤ D) :
    Nonempty (BinaryMaximalLayerResidualFrontier Q D H) := by
  let R : MvPolynomial (Fin 2) K := Q - H
  have hQLE : IsWeightLE binaryOrdinaryIntegerWeight D Q :=
    isWeightLE_binaryOrdinary_of_degree_le Q D hmax
  have hRlt0 :
      IsWeightLT binaryOrdinaryIntegerWeight D
        (Q - binaryOrdinaryDegreeComponent Q D) := by
    exact sub_initialForm_isWeightLT hQLE
  have hRlt : IsWeightLT binaryOrdinaryIntegerWeight D R := by
    simpa [R, H_eq] using hRlt0
  by_cases hRzero : R = 0
  · have hQH : Q = H := by
      have : Q - H = 0 := by simpa [R] using hRzero
      exact sub_eq_zero.mp this
    exact ⟨.collapsed hQH⟩
  · rcases exists_maximal_binaryOrdinaryDegreeComponent R hRzero with
      ⟨E, hGne0, hRmax⟩
    let G : MvPolynomial (Fin 2) K := binaryOrdinaryDegreeComponent R E
    have hElt : E < D := by
      by_contra hnot
      have hDE : D ≤ E := Nat.le_of_not_gt hnot
      have hzero : binaryOrdinaryDegreeComponent R E = 0 := by
        unfold binaryOrdinaryDegreeComponent
        apply initialForm_eq_zero_of_isWeightLT hRlt
        exact_mod_cast hDE
      exact hGne0 hzero
    have hGne : G ≠ 0 := by
      simpa [G] using hGne0
    have hGhom : G.IsHomogeneous E := by
      simpa [G] using binaryOrdinaryDegreeComponent_isHomogeneous R E
    exact ⟨.nextLayer R rfl hRzero E G hElt rfl hGne hRmax hGhom⟩

/-- Specialise the peeling theorem to the nonlinear linear-power branch of
the green maximal-layer frontier.  The top normal form is retained by the
constructor `M`; this theorem supplies only the exact lower residual data
needed by the next mixed-determinant argument. -/
theorem BinarySingularHessianMaximalLayerFrontier.nonlinear_residualFrontier
    {Q : MvPolynomial (Fin 2) K}
    (M : BinarySingularHessianMaximalLayerFrontier Q) :
    (match M with
      | .lowDegree .. => True
      | .nonlinearLinearPower D H _ H_eq _ hmax _ _ _ =>
          Nonempty (BinaryMaximalLayerResidualFrontier Q D H)) := by
  cases M with
  | lowDegree => trivial
  | nonlinearLinearPower D H hD H_eq H_ne hmax a c hnormal =>
      exact binaryMaximalLayer_residualFrontier Q D H H_eq hmax

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The actual HC4 transverse binary core inherits the exact top-layer peeling
frontier from its canonical maximal layer. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.residualFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    (match D.maximalLayer with
      | .lowDegree .. => True
      | .nonlinearLinearPower m H _ H_eq _ hmax _ _ _ =>
          Nonempty
            (BinaryMaximalLayerResidualFrontier
              D.binaryData.binaryFace m H)) := by
  cases D.maximalLayer with
  | lowDegree =>
      trivial
  | nonlinearLinearPower m H hD H_eq H_ne_zero hmax a c normalForm =>
      exact binaryMaximalLayer_residualFrontier
        D.binaryData.binaryFace m H H_eq hmax

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
