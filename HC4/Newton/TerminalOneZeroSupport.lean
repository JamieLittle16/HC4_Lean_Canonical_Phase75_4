import HC4.Newton.TerminalOneZeroPattern
import HC4.Newton.TerminalPermutedGradient
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Support geometry of the standard one-zero terminal face

Assume

    wt = (0,d,a,d-a),   0 < a < d,

and `F` has weighted degree `d`.

Differentiating in the degree-`d` coordinate `X₁` produces a polynomial of
weighted degree zero.  Since `X₁,X₂,X₃` all have strictly positive weight,
every supported monomial of `pderiv 1 F` has zero exponent in those three
variables.

Thus

    pderiv 1 F

depends only on the zero-weight variable `X₀`.  In particular

    ∂₁₁F = ∂₂₁F = ∂₃₁F = 0.

This is the sparse Hessian row behind the one-zero determinant factorisation.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Support-level dependence on only the zero-weight coordinate `X₀`. -/
def DependsOnlyOnStandardZeroCoordinate
    (P : MvPolynomial (Fin 4) K) : Prop :=
  ∀ m : Fin 4 →₀ ℕ,
    MvPolynomial.coeff m P ≠ 0 ->
      m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0

/-- Explicit integral weighted degree for `(0,d,a,d-a)`. -/
theorem integralWeightedDegree_standardOneZero
    (d a : ℤ)
    (m : Fin 4 →₀ ℕ) :
    integralWeightedDegree
        (standardOneZeroTerminalWeight d a) m =
      (m 1 : ℤ) * d +
      (m 2 : ℤ) * a +
      (m 3 : ℤ) * (d - a) := by
  unfold integralWeightedDegree
  rw [Finsupp.sum_fintype]
  · simp [standardOneZeroTerminalWeight,
      Fin.sum_univ_four]
  · intro i
    simp

/-- The `X₁` derivative has terminal weighted degree zero. -/
theorem standardOneZero_pderiv_one_weight_zero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    IsIntegralWeightedHomogeneous
      (standardOneZeroTerminalWeight d a) 0
      (MvPolynomial.pderiv 1 F) := by
  have hmath :
      MvPolynomial.IsWeightedHomogeneous
        (standardOneZeroTerminalWeight d a)
        F d :=
    integralWeightedHomogeneous_to_mathlib hhom
  have hderiv :
      MvPolynomial.IsWeightedHomogeneous
        (standardOneZeroTerminalWeight d a)
        (MvPolynomial.pderiv 1 F)
        (d - standardOneZeroTerminalWeight d a 1) :=
    HC4.Polynomial.pderiv_isWeightedHomogeneous
      hmath 1
  apply mathlibWeightedHomogeneous_to_integral
  simpa [standardOneZeroTerminalWeight] using hderiv

/-- Any degree-zero monomial for the standard one-zero weight uses only
`X₀`. -/
theorem standardOneZero_weight_zero_support_only_zeroCoordinate
    {d a : ℤ}
    (ha : 0 < a)
    (had : a < d)
    {P : MvPolynomial (Fin 4) K}
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) 0 P) :
    DependsOnlyOnStandardZeroCoordinate P := by
  intro m hm
  have hdegree := hhom m hm
  rw [integralWeightedDegree_standardOneZero] at hdegree
  have hd : 0 < d := lt_trans ha had
  have hda : 0 < d - a := by omega
  have h1nonneg :
      0 ≤ (m 1 : ℤ) * d :=
    mul_nonneg (by positivity) (le_of_lt hd)
  have h2nonneg :
      0 ≤ (m 2 : ℤ) * a :=
    mul_nonneg (by positivity) (le_of_lt ha)
  have h3nonneg :
      0 ≤ (m 3 : ℤ) * (d - a) :=
    mul_nonneg (by positivity) (le_of_lt hda)
  have hterm1 :
      (m 1 : ℤ) * d = 0 := by
    linarith
  have hterm2 :
      (m 2 : ℤ) * a = 0 := by
    linarith
  have hterm3 :
      (m 3 : ℤ) * (d - a) = 0 := by
    linarith
  have hm1z : (m 1 : ℤ) = 0 :=
    (mul_eq_zero.mp hterm1).resolve_right
      (ne_of_gt hd)
  have hm2z : (m 2 : ℤ) = 0 :=
    (mul_eq_zero.mp hterm2).resolve_right
      (ne_of_gt ha)
  have hm3z : (m 3 : ℤ) = 0 :=
    (mul_eq_zero.mp hterm3).resolve_right
      (ne_of_gt hda)
  constructor
  · exact_mod_cast hm1z
  · constructor
    · exact_mod_cast hm2z
    · exact_mod_cast hm3z

/-- `pderiv 1 F` depends only on the unique zero-weight coordinate. -/
theorem standardOneZero_pderiv_one_zeroCoordinateSupported
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    DependsOnlyOnStandardZeroCoordinate
      (MvPolynomial.pderiv 1 F) := by
  exact
    standardOneZero_weight_zero_support_only_zeroCoordinate
      ha had
      (standardOneZero_pderiv_one_weight_zero hhom)

/-- The sparse positive part of the Hessian row/column belonging to `X₁`. -/
theorem standardOneZero_pderiv_one_crossHessian_zero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    MvPolynomial.pderiv 1
        (MvPolynomial.pderiv 1 F) = 0 ∧
      MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 1 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 1 F) = 0 := by
  have hsupp :=
    standardOneZero_pderiv_one_zeroCoordinateSupported
      ha had hhom
  refine ⟨?_, ?_, ?_⟩
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        1 (MvPolynomial.pderiv 1 F)
        (fun m hm => (hsupp m hm).1)
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        2 (MvPolynomial.pderiv 1 F)
        (fun m hm => (hsupp m hm).2.1)
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        3 (MvPolynomial.pderiv 1 F)
        (fun m hm => (hsupp m hm).2.2)

end

end HC4.Newton
