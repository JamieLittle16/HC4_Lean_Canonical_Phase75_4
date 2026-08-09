import HC4.Newton.TerminalTwoZeroJC2Endpoint
import HC4.Polynomial.DerivativeWeight
import Mathlib.Tactic

/-!
# The determinant-matched permuted gradient

The non-scalar terminal face carries a permutation `π` satisfying

    lambda (π i) + lambda i = d.

This permutation is already supplied by the nonzero determinant term from
Phase 93.27.  It gives a canonical replacement for the fixed hyperbolic
involution used in the manuscript.

Define

    G_i = pderiv (π i) F.

If `F` has weighted degree `d`, then `G_i` has weighted degree

    d - lambda (π i) = lambda i.

Thus `G` is weight-preserving.

Pointwise, `G` is merely the gradient with its output coordinates
permuted, so injectivity of `G` is exactly equivalent to injectivity of the
original gradient.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The custom integral weighted degree agrees with Mathlib's
`Finsupp.weight` for integer weights. -/
theorem integralWeightedDegree_eq_finsuppWeight
    (lambda : Fin 4 -> ℤ)
    (m : Fin 4 →₀ ℕ) :
    integralWeightedDegree lambda m =
      Finsupp.weight lambda m := by
  simp [integralWeightedDegree,
    Finsupp.weight_apply]

/-- Convert the terminal support-level homogeneity predicate to Mathlib's
weighted-homogeneous predicate. -/
theorem integralWeightedHomogeneous_to_mathlib
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hhom :
      IsIntegralWeightedHomogeneous lambda d P) :
    MvPolynomial.IsWeightedHomogeneous lambda P d := by
  intro m hm
  rw [← integralWeightedDegree_eq_finsuppWeight]
  exact hhom m hm

/-- Convert Mathlib weighted homogeneity back to the terminal support-level
form used by the restart modules. -/
theorem mathlibWeightedHomogeneous_to_integral
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {P : MvPolynomial (Fin 4) K}
    (hhom :
      MvPolynomial.IsWeightedHomogeneous lambda P d) :
    IsIntegralWeightedHomogeneous lambda d P := by
  intro m hm
  rw [integralWeightedDegree_eq_finsuppWeight]
  exact hhom hm

/-- Polynomial map obtained by permuting the output coordinates of the
gradient according to a determinant matching. -/
def terminalPermutedGradient
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    Fin 4 -> MvPolynomial (Fin 4) K :=
  fun i => MvPolynomial.pderiv (π i) F

/-- Pointwise evaluation of the permuted gradient. -/
def terminalPermutedGradientEval
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    (Fin 4 -> K) -> (Fin 4 -> K) :=
  fun p i =>
    MvPolynomial.eval p
      (terminalPermutedGradient π F i)

/-- Each component of the determinant-matched permuted gradient preserves
the corresponding terminal weight. -/
theorem terminalPermutedGradient_component_weight
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {π : Equiv.Perm (Fin 4)}
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    (i : Fin 4) :
    IsIntegralWeightedHomogeneous
      lambda (lambda i)
      (terminalPermutedGradient π F i) := by
  have hmath :
      MvPolynomial.IsWeightedHomogeneous
        lambda F d :=
    integralWeightedHomogeneous_to_mathlib hhom
  have hderiv :
      MvPolynomial.IsWeightedHomogeneous
        lambda
        (MvPolynomial.pderiv (π i) F)
        (d - lambda (π i)) :=
    HC4.Polynomial.pderiv_isWeightedHomogeneous
      hmath (π i)
  have hdegree :
      d - lambda (π i) = lambda i := by
    have h := hπ i
    linarith
  apply mathlibWeightedHomogeneous_to_integral
  simpa [terminalPermutedGradient, hdegree] using hderiv

/-- Evaluating the permuted gradient is literally evaluating the original
gradient at the permuted output coordinate. -/
theorem terminalPermutedGradientEval_apply
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (p : Fin 4 -> K)
    (i : Fin 4) :
    terminalPermutedGradientEval π F p i =
      mvGradientMap F p (π i) := rfl

/-- Injectivity of the permuted gradient implies injectivity of the original
gradient. -/
theorem mvGradientMap_injective_of_permuted
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hinj :
      Function.Injective
        (terminalPermutedGradientEval π F)) :
    Function.Injective (mvGradientMap F) := by
  intro p q hpq
  apply hinj
  funext i
  exact congrFun hpq (π i)

/-- Conversely, output permutation cannot destroy injectivity. -/
theorem terminalPermutedGradientEval_injective_of_gradient
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hinj :
      Function.Injective (mvGradientMap F)) :
    Function.Injective
      (terminalPermutedGradientEval π F) := by
  intro p q hpq
  apply hinj
  funext j
  have h :=
    congrFun hpq (π.symm j)
  simpa [terminalPermutedGradientEval,
    terminalPermutedGradient] using h

/-- Exact injectivity equivalence under a determinant-matching output
permutation. -/
theorem terminalPermutedGradient_injective_iff
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    Function.Injective
        (terminalPermutedGradientEval π F) ↔
      Function.Injective (mvGradientMap F) := by
  constructor
  · exact mvGradientMap_injective_of_permuted π F
  · exact terminalPermutedGradientEval_injective_of_gradient π F

end

end HC4.Newton
