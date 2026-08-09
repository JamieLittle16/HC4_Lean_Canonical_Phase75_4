import HC4.Newton.TerminalPositiveWeightLinearBlocks
import Mathlib.Tactic

/-!
# Evaluation of positive triangular components

Phase 93.31 proves a support dichotomy for a weight-`t` component:

* a same-weight linear monomial; or
* a monomial involving only variables of weight strictly below `t`.

This module converts that support statement into the pointwise identity
needed for the recursive injectivity proof.

If two points agree on all variables of weight `< t`, then the nonlinear
part evaluates equally at the two points.  Hence the difference of the
component values is exactly the difference of its full linear part.

For a determinant-matched terminal gradient, Phase 93.32 identifies that
linear part with row-vector multiplication by the permuted terminal
Hessian.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Full degree-one part of a four-variable polynomial. -/
def fourVariableLinearPart
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  ∑ j : Fin 4,
    MvPolynomial.monomial
      (Finsupp.single j 1)
      (MvPolynomial.coeff
        (Finsupp.single j 1) P)

/-- The degree-one exponent `single i 1` remembers its coordinate. -/
theorem single_one_eq_iff
    (i j : Fin 4) :
    Finsupp.single i 1 =
        Finsupp.single j 1 ↔
      i = j := by
  constructor
  · intro h
    by_contra hij
    have happ :=
      congrArg
        (fun m : Fin 4 →₀ ℕ => m i)
        h
    simp [hij] at happ
  · intro hij
    simpa [hij]

/-- The linear part reproduces every degree-one coefficient. -/
theorem coeff_fourVariableLinearPart_single
    (P : MvPolynomial (Fin 4) K)
    (j : Fin 4) :
    MvPolynomial.coeff
        (Finsupp.single j 1)
        (fourVariableLinearPart P) =
      MvPolynomial.coeff
        (Finsupp.single j 1) P := by
  fin_cases j <;>
    simp [fourVariableLinearPart,
      Fin.sum_univ_four,
      MvPolynomial.coeff_monomial,
      single_one_eq_iff]

/-- A non-linear exponent has zero coefficient in the full linear part. -/
theorem coeff_fourVariableLinearPart_eq_zero_of_not_single
    (P : MvPolynomial (Fin 4) K)
    (m : Fin 4 →₀ ℕ)
    (hnot :
      ∀ j : Fin 4,
        m ≠ Finsupp.single j 1) :
    MvPolynomial.coeff m
        (fourVariableLinearPart P) = 0 := by
  have hnot' :
      ∀ j : Fin 4,
        Finsupp.single j 1 ≠ m := by
    intro j h
    exact hnot j h.symm
  simp [fourVariableLinearPart,
    Fin.sum_univ_four,
    MvPolynomial.coeff_monomial,
    hnot']

/-- A polynomial is supported strictly below terminal weight `t`. -/
def HasStrictlyLowerWeightSupport
    (lambda : Fin 4 -> ℤ)
    (t : ℤ)
    (P : MvPolynomial (Fin 4) K) : Prop :=
  ∀ m : Fin 4 →₀ ℕ,
    MvPolynomial.coeff m P ≠ 0 ->
      ∀ j : Fin 4,
        m j ≠ 0 ->
          lambda j < t

/-- Removing the full linear part from a triangular component leaves only
strictly lower-weight monomials. -/
theorem triangularSupport_residual_strictlyLower
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (htri :
      HasPositiveWeightTriangularSupport
        lambda t P) :
    HasStrictlyLowerWeightSupport
      lambda t
      (P - fourVariableLinearPart P) := by
  intro m hmres j hmj
  by_cases hsingle :
      ∃ k : Fin 4,
        m = Finsupp.single k 1
  · rcases hsingle with ⟨k, rfl⟩
    exfalso
    apply hmres
    simp [coeff_fourVariableLinearPart_single]
  · have hlin0 :
        MvPolynomial.coeff m
            (fourVariableLinearPart P) = 0 :=
      coeff_fourVariableLinearPart_eq_zero_of_not_single
        P m (by
          intro k hk
          exact hsingle ⟨k, hk⟩)
    have hmP :
        MvPolynomial.coeff m P ≠ 0 := by
      intro hmP0
      apply hmres
      simp [hmP0, hlin0]
    rcases htri m hmP with hlinear | hlower
    · rcases hlinear with ⟨k, hk, _⟩
      exact (hsingle ⟨k, hk⟩).elim
    · exact hlower j hmj

/-- A monomial supported only in coordinates where two points agree has
the same value at those points. -/
theorem eval_monomial_eq_of_eq_on_exponent_support
    (m : Fin 4 →₀ ℕ)
    (a : K)
    (p q : Fin 4 -> K)
    (heq :
      ∀ j : Fin 4,
        m j ≠ 0 ->
          p j = q j) :
    MvPolynomial.eval p
        (MvPolynomial.monomial m a) =
      MvPolynomial.eval q
        (MvPolynomial.monomial m a) := by
  rw [MvPolynomial.eval_monomial,
      MvPolynomial.eval_monomial]
  apply congrArg (fun z : K => a * z)
  apply Finsupp.prod_congr
  intro j hj
  rw [heq j (Finsupp.mem_support_iff.mp hj)]

/-- A strictly-lower-weight polynomial evaluates equally at two points that
already agree in all strictly lower-weight coordinates. -/
theorem eval_eq_of_strictlyLowerWeightSupport
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hsupp :
      HasStrictlyLowerWeightSupport
        lambda t P)
    (p q : Fin 4 -> K)
    (hlow :
      ∀ j : Fin 4,
        lambda j < t ->
          p j = q j) :
    MvPolynomial.eval p P =
      MvPolynomial.eval q P := by
  rw [MvPolynomial.as_sum P]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply eval_monomial_eq_of_eq_on_exponent_support
  intro j hmj
  exact hlow j
    (hsupp m
      (MvPolynomial.mem_support_iff.mp hm)
      j hmj)

/-- Evaluation of the full linear part is the expected four-coordinate
linear combination. -/
theorem eval_fourVariableLinearPart
    (P : MvPolynomial (Fin 4) K)
    (p : Fin 4 -> K) :
    MvPolynomial.eval p
        (fourVariableLinearPart P) =
      ∑ j : Fin 4,
        MvPolynomial.coeff
            (Finsupp.single j 1) P *
          p j := by
  simp [fourVariableLinearPart,
    MvPolynomial.eval_monomial]

/-- **Triangular evaluation difference.**

Once the two points agree below weight `t`, every nonlinear term cancels,
so only the full linear part remains in their value difference. -/
theorem triangularSupport_eval_sub_eq_linear
    {lambda : Fin 4 -> ℤ}
    {t : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (htri :
      HasPositiveWeightTriangularSupport
        lambda t P)
    (p q : Fin 4 -> K)
    (hlow :
      ∀ j : Fin 4,
        lambda j < t ->
          p j = q j) :
    MvPolynomial.eval p P -
        MvPolynomial.eval q P =
      ∑ j : Fin 4,
        MvPolynomial.coeff
            (Finsupp.single j 1) P *
          (p j - q j) := by
  let L := fourVariableLinearPart P
  let R := P - L
  have hR :
      HasStrictlyLowerWeightSupport
        lambda t R := by
    dsimp [R, L]
    exact triangularSupport_residual_strictlyLower htri
  have hReval :
      MvPolynomial.eval p R =
        MvPolynomial.eval q R :=
    eval_eq_of_strictlyLowerWeightSupport
      hR p q hlow
  have hdecomp :
      P = R + L := by
    simp [R, L]
  have hlinearDiff :
      MvPolynomial.eval p P -
          MvPolynomial.eval q P =
        MvPolynomial.eval p L -
          MvPolynomial.eval q L := by
    rw [hdecomp]
    simp only [map_add]
    rw [hReval]
    ring
  rw [hlinearDiff]
  rw [eval_fourVariableLinearPart,
      eval_fourVariableLinearPart]
  simp [Fin.sum_univ_four]
  ring

/-- Difference vector of two four-dimensional points. -/
def terminalPointDifference
    (p q : Fin 4 -> K) :
    Fin 4 -> K :=
  fun j => p j - q j

/-- For one determinant-matched terminal-gradient component, agreement at
all lower weights makes its pointwise difference exactly the corresponding
linear Hessian equation. -/
theorem terminalPermutedGradient_eval_sub_eq_vecMul
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {π : Equiv.Perm (Fin 4)}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda)
    (p q : Fin 4 -> K)
    (i : Fin 4)
    (hlow :
      ∀ j : Fin 4,
        lambda j < lambda i ->
          p j = q j) :
    terminalPermutedGradientEval π F p i -
        terminalPermutedGradientEval π F q i =
      Matrix.vecMul
        (terminalPointDifference p q)
        (terminalPermutedHessianMatrix π F) i := by
  have htri :
      HasPositiveWeightTriangularSupport
        lambda (lambda i)
        (terminalPermutedGradient π F i) :=
    positiveTerminalFace_hasTriangularPermutedGradient
      hface hπ hpos i
  have heval :=
    triangularSupport_eval_sub_eq_linear
      htri p q hlow
  change
    terminalPermutedGradientEval π F p i -
        terminalPermutedGradientEval π F q i =
      _ at heval
  rw [heval]
  simp [Matrix.vecMul, dotProduct,
    terminalPointDifference,
    terminalPermutedHessian_eq_linearCoeff,
    Fin.sum_univ_four]
  ring

/-- Restrict a point difference to one terminal weight level. -/
def terminalWeightSliceDifference
    (lambda : Fin 4 -> ℤ)
    (t : ℤ)
    (p q : Fin 4 -> K) :
    Fin 4 -> K :=
  fun j =>
    if lambda j = t
    then p j - q j
    else 0

/-- The weight-slice difference is supported on its declared weight. -/
theorem terminalWeightSliceDifference_supported
    (lambda : Fin 4 -> ℤ)
    (t : ℤ)
    (p q : Fin 4 -> K) :
    IsSupportedOnTerminalWeight
      lambda t
      (terminalWeightSliceDifference
        lambda t p q) := by
  intro j hj
  simp [terminalWeightSliceDifference, hj]

/-- On an output coordinate of weight `t`, cross-weight Hessian entries
make the full point difference and its weight-`t` slice give the same
linear equation. -/
theorem terminalPointDifference_vecMul_eq_weightSlice
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {π : Equiv.Perm (Fin 4)}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    (p q : Fin 4 -> K)
    {t : ℤ}
    {i : Fin 4}
    (hi : lambda i = t) :
    Matrix.vecMul
        (terminalPointDifference p q)
        (terminalPermutedHessianMatrix π F) i =
      Matrix.vecMul
        (terminalWeightSliceDifference
          lambda t p q)
        (terminalPermutedHessianMatrix π F) i := by
  classical
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjt : lambda j = t
  · simp [terminalPointDifference,
      terminalWeightSliceDifference, hjt]
  · have hji :
        lambda j ≠ lambda i := by
      intro hEq
      apply hjt
      calc
        lambda j = lambda i := hEq
        _ = t := hi
    rw [terminalPermutedHessian_entry_eq_zero_of_weight_ne
      hface hπ hji]
    simp [terminalPointDifference,
      terminalWeightSliceDifference, hjt]

end

end HC4.Newton
