import HC4.Newton.TerminalTwoZeroPattern
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Support geometry of the two-zero terminal boundary

Assume the terminal weight has the standard form

    (0,0,d,d),   d > 0,

and `F` has weighted degree `d`.

Then every supported monomial contains exactly one copy in total of the
positive-weight variables `X₂,X₃`:

    m₂ + m₃ = 1.

Equivalently `F` is weighted homogeneous of degree one for the auxiliary
natural weight `(0,0,1,1)`.

Weighted Euler then gives the exact identity

    X₂ * pderiv 2 F + X₃ * pderiv 3 F = F.

Moreover the two coefficient polynomials `pderiv 2 F` and `pderiv 3 F`
depend only on `X₀,X₁`, and the positive-positive Hessian block vanishes.

This is the polynomial support content of the planar Hessian-doubling
normal form, still inside the original four-variable polynomial ring.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Auxiliary natural weight that only counts the two positive variables. -/
def standardPositivePairWeight : Fin 4 -> ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- A polynomial depends only on the standard zero-weight pair `X₀,X₁` at
the support level. -/
def DependsOnlyOnStandardZeroPair
    (P : MvPolynomial (Fin 4) K) : Prop :=
  ∀ m : Fin 4 →₀ ℕ,
    MvPolynomial.coeff m P ≠ 0 ->
      m 2 = 0 ∧ m 3 = 0

/-- Explicit integral weighted degree for `(0,0,d,d)`. -/
theorem integralWeightedDegree_standardTwoZero
    (d : ℤ)
    (m : Fin 4 →₀ ℕ) :
    integralWeightedDegree
        (standardTwoZeroTerminalWeight d) m =
      ((m 2 : ℤ) + (m 3 : ℤ)) * d := by
  unfold integralWeightedDegree
  rw [Finsupp.sum_fintype]
  · simp [standardTwoZeroTerminalWeight,
      Fin.sum_univ_four]
    ring
  · intro i
    simp

/-- The auxiliary natural weight is exactly `m₂+m₃`. -/
theorem weight_standardPositivePair
    (m : Fin 4 →₀ ℕ) :
    Finsupp.weight standardPositivePairWeight m =
      m 2 + m 3 := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [standardPositivePairWeight,
      Fin.sum_univ_four]
  · intro i
    simp

/-- Every supported monomial on a positive-degree `(0,0,d,d)` face contains
exactly one positive-weight variable. -/
theorem standardTwoZero_support_positivePairDegree_one
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    ∀ m : Fin 4 →₀ ℕ,
      MvPolynomial.coeff m F ≠ 0 ->
        m 2 + m 3 = 1 := by
  intro m hm
  have hdegree := hhom m hm
  rw [integralWeightedDegree_standardTwoZero] at hdegree
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hfactor :
      (((m 2 : ℤ) + (m 3 : ℤ)) - 1) * d = 0 := by
    calc
      (((m 2 : ℤ) + (m 3 : ℤ)) - 1) * d =
          ((m 2 : ℤ) + (m 3 : ℤ)) * d - d := by
            ring
      _ = 0 := by
            rw [hdegree]
            ring
  have hsumZ :
      (m 2 : ℤ) + (m 3 : ℤ) = 1 := by
    have hz :=
      (mul_eq_zero.mp hfactor).resolve_right hd0
    linarith
  exact_mod_cast hsumZ

/-- The exact support alternatives are `one X₂ and no X₃`, or vice versa. -/
theorem standardTwoZero_support_positivePair_exactly_one
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    {m : Fin 4 →₀ ℕ}
    (hm : MvPolynomial.coeff m F ≠ 0) :
    (m 2 = 1 ∧ m 3 = 0) ∨
      (m 2 = 0 ∧ m 3 = 1) := by
  have hsum :=
    standardTwoZero_support_positivePairDegree_one
      hd hhom m hm
  omega

/-- The integral support condition converts to Mathlib's natural weighted
homogeneity of degree one for `(0,0,1,1)`. -/
theorem standardTwoZero_isWeightedHomogeneous_positivePair_one
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    MvPolynomial.IsWeightedHomogeneous
      standardPositivePairWeight F 1 := by
  intro m hm
  rw [weight_standardPositivePair]
  exact
    standardTwoZero_support_positivePairDegree_one
      hd hhom m hm

/-- Weighted Euler gives the exact four-variable doubling decomposition. -/
theorem standardTwoZero_euler_decomposition
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    MvPolynomial.X 2 *
        MvPolynomial.pderiv 2 F +
      MvPolynomial.X 3 *
        MvPolynomial.pderiv 3 F =
      F := by
  have hnat :=
    standardTwoZero_isWeightedHomogeneous_positivePair_one
      hd hhom
  have heuler :=
    hnat.sum_weight_X_mul_pderiv
  simpa [standardPositivePairWeight,
    Fin.sum_univ_four] using heuler

/-- The `X₂` coefficient of a two-zero terminal face depends only on
`X₀,X₁`. -/
theorem standardTwoZero_pderiv_two_zeroPairSupported
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    DependsOnlyOnStandardZeroPair
      (MvPolynomial.pderiv 2 F) := by
  have hnat :=
    standardTwoZero_isWeightedHomogeneous_positivePair_one
      hd hhom
  have hderiv :
      MvPolynomial.IsWeightedHomogeneous
        standardPositivePairWeight
        (MvPolynomial.pderiv 2 F) 0 := by
    apply hnat.pderiv
    simp [standardPositivePairWeight]
  intro m hm
  have hweight := hderiv hm
  rw [weight_standardPositivePair] at hweight
  constructor <;> omega

/-- The `X₃` coefficient also depends only on `X₀,X₁`. -/
theorem standardTwoZero_pderiv_three_zeroPairSupported
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    DependsOnlyOnStandardZeroPair
      (MvPolynomial.pderiv 3 F) := by
  have hnat :=
    standardTwoZero_isWeightedHomogeneous_positivePair_one
      hd hhom
  have hderiv :
      MvPolynomial.IsWeightedHomogeneous
        standardPositivePairWeight
        (MvPolynomial.pderiv 3 F) 0 := by
    apply hnat.pderiv
    simp [standardPositivePairWeight]
  intro m hm
  have hweight := hderiv hm
  rw [weight_standardPositivePair] at hweight
  constructor <;> omega

/-- Support-level independence of a variable forces its formal partial
derivative to vanish.  This direction needs no characteristic-zero
hypothesis. -/
theorem pderiv_eq_zero_of_all_supported_exponents_zero
    (i : Fin 4)
    (P : MvPolynomial (Fin 4) K)
    (hsupp :
      ∀ m : Fin 4 →₀ ℕ,
        MvPolynomial.coeff m P ≠ 0 ->
          m i = 0) :
    MvPolynomial.pderiv i P = 0 := by
  classical
  ext m
  rw [coeff_pderiv_backport]
  let mPlus : Fin 4 →₀ ℕ :=
    m + Finsupp.single i 1
  have hmPlusApply :
      mPlus i = m i + 1 := by
    simp [mPlus]
  have hshift :
      mPlus i ≠ 0 := by
    rw [hmPlusApply]
    omega
  have hcoeff :
      MvPolynomial.coeff mPlus P = 0 := by
    by_contra hne
    exact hshift
      (hsupp mPlus hne)
  simpa [mPlus, hcoeff]

/-- The complete positive-positive Hessian block vanishes on the standard
two-zero terminal face. -/
theorem standardTwoZero_positivePositiveHessian_zero
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 3 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 3 F) = 0 := by
  have h2 :=
    standardTwoZero_pderiv_two_zeroPairSupported
      hd hhom
  have h3 :=
    standardTwoZero_pderiv_three_zeroPairSupported
      hd hhom
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        2 (MvPolynomial.pderiv 2 F)
        (fun m hm => (h2 m hm).1)
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        3 (MvPolynomial.pderiv 2 F)
        (fun m hm => (h2 m hm).2)
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        2 (MvPolynomial.pderiv 3 F)
        (fun m hm => (h3 m hm).1)
  · exact
      pderiv_eq_zero_of_all_supported_exponents_zero
        3 (MvPolynomial.pderiv 3 F)
        (fun m hm => (h3 m hm).2)

end

end HC4.Newton
