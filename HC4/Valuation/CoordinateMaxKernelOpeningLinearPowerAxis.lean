import HC4.Valuation.CoordinateMaxKernelOpeningLinearPowerRigidity
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Extraction-axis rigidity for a linear-power first opening

At an exact coordinate-max first opening, the low-rank child may have the form

    child = a * L^m.

The previous module shows that `L` omits the newly appearing kernel
coordinate.  Here we use the *maximal-extraction provenance* as well.

If `L` also omitted the extraction coordinate, then the nonzero child would
live at extraction level zero.  The parent has no negative exponents, so the
coordinate-max weight bound would force every parent monomial to have the same
zero extraction coordinate.  Hence the exact initial form would be the whole
parent, contradicting the defining fact that the child has the kernel while
the parent does not.

Thus the extraction coefficient of `L` is nonzero, and in particular the
extraction and kernel coordinates are distinct.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

/-- Every supported child exponent lies on the stored coordinate-max level. -/
theorem child_extractionCoordinate_eq
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ D.child.support) :
    d D.extractionCoordinate = D.extractionLevel := by
  have hd' :
      d ∈
        (initialForm
          (coordinateMaxWeight D.extractionCoordinate)
          (D.extractionLevel : ℤ) D.parent).support := by
    simpa [D.child_eq_initialForm] using hd
  have hhom :=
    initialForm_isWeightedHomogeneous
      (coordinateMaxWeight D.extractionCoordinate)
      (D.extractionLevel : ℤ) D.parent
  have hw := hhom (MvPolynomial.mem_support_iff.mp hd')
  rw [weight_coordinateMaxWeight] at hw
  exact_mod_cast hw

namespace ChildLinearPowerData

variable {m : ℕ}
variable (P : D.ChildLinearPowerData m)

/-- The exact linear form must genuinely use the coordinate along which this
first kernel-opening child was extracted. -/
theorem extraction_ratio_ne_zero
    (hm : 2 ≤ m) :
    P.ratio D.extractionCoordinate ≠ 0 := by
  intro hratio

  have hchildDeriv :
      MvPolynomial.pderiv D.extractionCoordinate D.child = 0 := by
    rw [P.eq_power, MvPolynomial.pderiv_C_mul]
    have hmrepr : m = (m - 1) + 1 := by omega
    conv_lhs =>
      rhs
      rw [hmrepr]
    rw [pderiv_gradientRatioLinearForm_pow_succ]
    simp [hratio]

  have hsupp : D.child.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr D.child_ne_zero
  rcases hsupp with ⟨d, hd⟩
  have hdcoeff : MvPolynomial.coeff d D.child ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdzero : d D.extractionCoordinate = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      D.extractionCoordinate D.child hchildDeriv d hdcoeff
  have hdlevel : d D.extractionCoordinate = D.extractionLevel :=
    D.child_extractionCoordinate_eq hd
  have hlevel : D.extractionLevel = 0 := by omega

  have hparentZero :
      ∀ q ∈ D.parent.support, q D.extractionCoordinate = 0 := by
    intro q hq
    have hle := D.weight_bound hq
    rw [weight_coordinateMaxWeight] at hle
    rw [hlevel] at hle
    have hnat : q D.extractionCoordinate ≤ 0 := by
      exact_mod_cast hle
    omega

  have hchildParent : D.child = D.parent := by
    rw [D.child_eq_initialForm]
    apply MvPolynomial.ext
    intro q
    rw [coeff_initialForm, weight_coordinateMaxWeight]
    by_cases hq : MvPolynomial.coeff q D.parent = 0
    · simp [hq]
    · have hqmem : q ∈ D.parent.support :=
        MvPolynomial.mem_support_iff.mpr hq
      have hqzero := hparentZero q hqmem
      simp [hlevel, hqzero]

  apply D.parent_kernel_ne
  rw [← hchildParent]
  exact D.child_kernel

/-- Therefore the extraction coordinate and the newly appearing kernel
coordinate are necessarily different. -/
theorem extractionCoordinate_ne_kernelCoordinate
    (hm : 2 ≤ m) :
    D.extractionCoordinate ≠ D.kernelCoordinate := by
  intro heq
  have hextract : P.ratio D.extractionCoordinate ≠ 0 :=
    P.extraction_ratio_ne_zero hm
  have hkernel : P.ratio D.kernelCoordinate = 0 :=
    P.kernel_ratio_eq_zero hm
  rw [heq] at hextract
  exact hextract hkernel

end ChildLinearPowerData

end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
