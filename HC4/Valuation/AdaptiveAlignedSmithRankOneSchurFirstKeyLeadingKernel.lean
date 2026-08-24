import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurSourceCoordinateKernel
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyInterface
import Mathlib.Tactic

/-!
# Leading source-coordinate kernel on the first transverse key

Stage 4B7 returns the nonzero denominator-cleared Schur kernel to the literal
source coordinates of the honest special fibre

    F₀ = polynomialFamilySpecialFiber C.family.

Stage 4B1 independently selects its first positive transverse exact component

    Q = initialForm wt (-m) F₀,

for the transverse-order weight

    wt(x₀)=0,  wt(x₁)=wt(x₂)=wt(x₃)=-1.

There is one subtle point in passing the full polynomial kernel equation

    Hess(F₀) * W = 0

to `Q`: the four polynomial coordinates of `W` need not have the same top
weight.  The correct derivative-compatible profile is shifted by the source
coordinate weight.  We therefore select canonically

    beta = max { weight(d) - wt(j) | d in support(W_j) }.

Then every `W_j` is weakly bounded by `beta + wt(j)`, and at least one exact
component at that bound is nonzero.  Let

    V_j = initialForm wt (beta + wt(j)) W_j.

The vector `V` is nonzero.

For a transverse row `i = 1,2,3`, the transverse-degree-zero part of `F₀`
has zero `i`-derivative.  Hence every Hessian entry in that row is bounded by

    -m - wt(i) - wt(j).

The existing exact top-product theorem therefore gives, term by term,

    in_(beta-m-wt(i)) (H_ij(F₀) W_j)
      = H_ij(Q) V_j.

Taking that exact component in the full kernel equation proves

    (Hess Q * V)_i = 0

for all three transverse rows.

Thus this file is the promised initial-form source/kernel compatibility
lemma.  It does not classify the leading vector and it does not assume a
constant projective direction.  Those are subsequent geometric steps.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Canonical derivative-shifted top weight of a polynomial vector -/

/-- All source weights occurring in a polynomial vector after subtracting the
weight of the vector coordinate.  This shift is exactly the one for which
Hessian multiplication has a common row weight. -/
noncomputable def shiftedSourceVectorWeightSupport
    (W : Fin 4 → MvPolynomial (Fin 4) K) : Finset ℤ := by
  classical
  exact
    (Finset.univ : Finset (Fin 4)).biUnion fun j =>
      (W j).support.image fun d =>
        Finsupp.weight pureLongitudinalTransverseWeight d -
          pureLongitudinalTransverseWeight j

/-- Every supported monomial of one vector coordinate contributes its shifted
weight to the common finite support. -/
theorem shiftedSourceVectorWeight_mem
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ (W j).support) :
    Finsupp.weight pureLongitudinalTransverseWeight d -
        pureLongitudinalTransverseWeight j ∈
      shiftedSourceVectorWeightSupport W := by
  classical
  unfold shiftedSourceVectorWeightSupport
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- A nonzero polynomial vector has nonempty shifted weight support. -/
theorem shiftedSourceVectorWeightSupport_nonempty
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    (shiftedSourceVectorWeightSupport W).Nonempty := by
  have hj : ∃ j : Fin 4, W j ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hW
    funext j
    exact hnone j
  rcases hj with ⟨j, hj⟩
  rcases MvPolynomial.support_nonempty.mpr hj with ⟨d, hd⟩
  exact
    ⟨Finsupp.weight pureLongitudinalTransverseWeight d -
        pureLongitudinalTransverseWeight j,
      shiftedSourceVectorWeight_mem W j d hd⟩

/-- Canonical maximal derivative-shifted source weight of a nonzero polynomial
vector. -/
noncomputable def shiftedSourceVectorTopWeight
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) : ℤ :=
  (shiftedSourceVectorWeightSupport W).max'
    (shiftedSourceVectorWeightSupport_nonempty W hW)

/-- The selected shifted top weight is actually attained. -/
theorem shiftedSourceVectorTopWeight_mem
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    shiftedSourceVectorTopWeight W hW ∈
      shiftedSourceVectorWeightSupport W := by
  unfold shiftedSourceVectorTopWeight
  exact
    Finset.max'_mem
      (shiftedSourceVectorWeightSupport W)
      (shiftedSourceVectorWeightSupport_nonempty W hW)

/-- Every vector coordinate has the weak upper bound dictated by the common
shifted top weight. -/
theorem shiftedSourceVector_component_isWeightLE
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (j : Fin 4) :
    IsWeightLE pureLongitudinalTransverseWeight
      (shiftedSourceVectorTopWeight W hW +
        pureLongitudinalTransverseWeight j)
      (W j) := by
  intro d hd
  have hmem := shiftedSourceVectorWeight_mem W j d hd
  have hle :
      Finsupp.weight pureLongitudinalTransverseWeight d -
          pureLongitudinalTransverseWeight j ≤
        shiftedSourceVectorTopWeight W hW := by
    unfold shiftedSourceVectorTopWeight
    exact
      Finset.le_max'
        (shiftedSourceVectorWeightSupport W)
        (Finsupp.weight pureLongitudinalTransverseWeight d -
          pureLongitudinalTransverseWeight j)
        hmem
  omega

/-- Exact leading vector at the canonical derivative-shifted source weight. -/
noncomputable def shiftedSourceVectorLeading
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  fun j =>
    initialForm pureLongitudinalTransverseWeight
      (shiftedSourceVectorTopWeight W hW +
        pureLongitudinalTransverseWeight j)
      (W j)

/-- At least one coordinate attains the selected shifted top weight, so the
leading vector is nonzero. -/
theorem shiftedSourceVectorLeading_ne_zero
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    shiftedSourceVectorLeading W hW ≠ 0 := by
  classical
  have htop := shiftedSourceVectorTopWeight_mem W hW
  unfold shiftedSourceVectorWeightSupport at htop
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at htop
  rcases htop with ⟨j, hj⟩
  rcases Finset.mem_image.mp hj with ⟨d, hd, hweight⟩
  have hw :
      Finsupp.weight pureLongitudinalTransverseWeight d =
        shiftedSourceVectorTopWeight W hW +
          pureLongitudinalTransverseWeight j := by
    omega
  have hcoeffW : MvPolynomial.coeff d (W j) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcomponent :
      MvPolynomial.coeff d (shiftedSourceVectorLeading W hW j) =
        MvPolynomial.coeff d (W j) := by
    rw [shiftedSourceVectorLeading, coeff_initialForm]
    simp [hw]
  intro hzero
  have hjzero := congrFun hzero j
  have hcoeffzero :
      MvPolynomial.coeff d (shiftedSourceVectorLeading W hW j) = 0 := by
    rw [hjzero]
    simp
  rw [hcomponent] at hcoeffzero
  exact hcoeffW hcoeffzero

/-! ## Initial-form compatibility with transverse Hessian rows -/

/-- In a transverse Hessian row, the degree-zero transverse source component
contributes nothing.  Therefore the first-positive-transverse remainder bound
is inherited by every entry in that row. -/
theorem transverseHessianRow_isWeightLE_firstPositive
    (F : MvPolynomial (Fin 4) K)
    (hpos : (positiveTransverseSourceSupport F).Nonempty)
    (i : Fin 3)
    (j : Fin 4) :
    IsWeightLE pureLongitudinalTransverseWeight
      (-(firstPositiveTransverseSourceDegree F hpos : ℤ) -
        pureLongitudinalTransverseWeight i.succ -
        pureLongitudinalTransverseWeight j)
      (HC4.Polynomial.hessian F i.succ j) := by
  let m := firstPositiveTransverseSourceDegree F hpos
  let Fzero := initialForm pureLongitudinalTransverseWeight 0 F
  let R := F - Fzero
  have hRLE :
      IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ)) R := by
    simpa [m, Fzero, R] using
      remainder_isWeightLE_neg_firstPositiveTransverseSourceDegree F hpos
  have htrans : MvPolynomial.pderiv i.succ Fzero = 0 := by
    simpa [Fzero] using
      pderiv_transverse_initialForm_zero_eq_zero F i
  have hentry :
      HC4.Polynomial.hessian F i.succ j =
        HC4.Polynomial.hessian R i.succ j := by
    have hdecomp : F = R + Fzero := by
      dsimp [R, Fzero]
      ring
    rw [hdecomp]
    simp [HC4.Polynomial.hessian_apply, htrans]
  rw [hentry]
  simpa [m] using hRLE.hessian_entry i.succ j

/-- **Stage 4B8 initial-form kernel bridge.**

For any nonzero polynomial full Hessian-kernel vector of `F`, take the
canonical derivative-shifted leading source component.  Every transverse row
of the Hessian of the first positive transverse key kills that nonzero
leading vector. -/
theorem firstPositiveTransverseKey_transverseRows_kernel
    (F : MvPolynomial (Fin 4) K)
    (hpos : (positiveTransverseSourceSupport F).Nonempty)
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (hkernel : (HC4.Polynomial.hessian F).mulVec W = 0) :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian
          (initialForm pureLongitudinalTransverseWeight
            (-(firstPositiveTransverseSourceDegree F hpos : ℤ)) F)).mulVec
        (shiftedSourceVectorLeading W hW) i.succ = 0 := by
  intro i
  let m := firstPositiveTransverseSourceDegree F hpos
  let Q := initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) F
  let beta := shiftedSourceVectorTopWeight W hW
  let V := shiftedSourceVectorLeading W hW
  have hterm :
      ∀ j : Fin 4,
        initialForm pureLongitudinalTransverseWeight
            (beta - (m : ℤ) - pureLongitudinalTransverseWeight i.succ)
            (HC4.Polynomial.hessian F i.succ j * W j) =
          HC4.Polynomial.hessian Q i.succ j * V j := by
    intro j
    have hHLE := transverseHessianRow_isWeightLE_firstPositive
      F hpos i j
    have hWLE := shiftedSourceVector_component_isWeightLE W hW j
    have hmul := initialForm_mul_eq_mul_initialForm_of_isWeightLE
      (K := K) hHLE hWLE
    have hshift :
        (-(m : ℤ) - pureLongitudinalTransverseWeight i.succ -
              pureLongitudinalTransverseWeight j) +
            (beta + pureLongitudinalTransverseWeight j) =
          beta - (m : ℤ) - pureLongitudinalTransverseWeight i.succ := by
      ring
    rw [hshift] at hmul
    have hHtop := hessian_initialForm_entry
      pureLongitudinalTransverseWeight (-(m : ℤ)) F i.succ j
    change
      HC4.Polynomial.hessian Q i.succ j =
        initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ) - pureLongitudinalTransverseWeight i.succ -
            pureLongitudinalTransverseWeight j)
          (HC4.Polynomial.hessian F i.succ j) at hHtop
    change
      initialForm pureLongitudinalTransverseWeight
          (beta - (m : ℤ) - pureLongitudinalTransverseWeight i.succ)
          (HC4.Polynomial.hessian F i.succ j * W j) =
        initialForm pureLongitudinalTransverseWeight
            (-(m : ℤ) - pureLongitudinalTransverseWeight i.succ -
              pureLongitudinalTransverseWeight j)
            (HC4.Polynomial.hessian F i.succ j) *
          initialForm pureLongitudinalTransverseWeight
            (beta + pureLongitudinalTransverseWeight j) (W j) at hmul
    rw [← hHtop] at hmul
    simpa [V, shiftedSourceVectorLeading, beta] using hmul
  have hrow :
      ∑ j : Fin 4, HC4.Polynomial.hessian F i.succ j * W j = 0 := by
    have hi := congrFun hkernel i.succ
    simpa [Matrix.mulVec, dotProduct] using hi
  have hsum :
      ∑ j : Fin 4, HC4.Polynomial.hessian Q i.succ j * V j = 0 := by
    calc
      ∑ j : Fin 4, HC4.Polynomial.hessian Q i.succ j * V j =
          ∑ j : Fin 4,
            initialForm pureLongitudinalTransverseWeight
              (beta - (m : ℤ) - pureLongitudinalTransverseWeight i.succ)
              (HC4.Polynomial.hessian F i.succ j * W j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact (hterm j).symm
      _ = initialForm pureLongitudinalTransverseWeight
            (beta - (m : ℤ) - pureLongitudinalTransverseWeight i.succ)
            (∑ j : Fin 4, HC4.Polynomial.hessian F i.succ j * W j) := by
              rw [map_sum]
      _ = 0 := by rw [hrow]; simp
  simpa [Q, V, Matrix.mulVec, dotProduct] using hsum

/-! ## Carrier-facing package -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The first source key together with the canonical nonzero leading piece of
an honest source-coordinate Stage-3 kernel.  Only the three transverse Hessian
rows are asserted here; the longitudinal row contains the degree-zero source
pivot and belongs to the subsequent projective analysis. -/
structure FirstKeyLeadingTransverseKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  hpos :
    (positiveTransverseSourceSupport
      (polynomialFamilySpecialFiber C.family)).Nonempty
  sourceKernel : C.SourceCoordinateSpecialKernelData
  leadingVector : Fin 4 → MvPolynomial (Fin 4) K
  leading_eq :
    leadingVector =
      shiftedSourceVectorLeading
        sourceKernel.vector sourceKernel.vector_ne_zero
  leading_ne_zero : leadingVector ≠ 0
  transverseKernel :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian
          (initialForm pureLongitudinalTransverseWeight
            (-(firstPositiveTransverseSourceDegree
              (polynomialFamilySpecialFiber C.family) hpos : ℤ))
            (polynomialFamilySpecialFiber C.family))).mulVec
        leadingVector i.succ = 0

/-- Every Stage-4B1 first-key carrier has a canonical nonzero leading
source-kernel vector on the first transverse key.  This combines B7 with the
initial-form bridge above and introduces no new geometric hypothesis. -/
theorem HasFirstTransverseSourceKey.exists_leadingTransverseKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    Nonempty C.FirstKeyLeadingTransverseKernelData := by
  rcases hkey with ⟨hpos, hmpos, hQne, hQhom, hQhessian⟩
  rcases C.exists_sourceCoordinateSpecialKernelData with ⟨D⟩
  let V := shiftedSourceVectorLeading D.vector D.vector_ne_zero
  refine ⟨{
    hpos := hpos
    sourceKernel := D
    leadingVector := V
    leading_eq := rfl
    leading_ne_zero := ?_
    transverseKernel := ?_
  }⟩
  · simpa [V] using
      shiftedSourceVectorLeading_ne_zero D.vector D.vector_ne_zero
  · intro i
    dsimp [V]
    exact
      firstPositiveTransverseKey_transverseRows_kernel
        (polynomialFamilySpecialFiber C.family)
        hpos D.vector D.vector_ne_zero D.kernel i

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
