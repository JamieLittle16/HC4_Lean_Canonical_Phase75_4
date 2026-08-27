import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesFrontier
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerSupport
import HC4.Valuation.CanonicalSmithDefectExposure
import Mathlib.Tactic

/-!
# A19.27: exact parameter order of a positive Rees low layer

The A19.17 low-layer constructor records a coefficient which defeats the
uniform determinant-closing transverse Rees transform.  Its inequality already
contains more information than the four-pattern classification: because the
transverse degree is at most one, the exact parameter order of that coefficient
is strictly below the incoming Hessian clock.

This gives the source-facing dichotomy needed by final assembly.

* order zero means that the same low monomial is literally present on the
  represented special fibre;
* positive order gives an actually occurring positive parameter layer, and
  hence the globally first positive actual layer also occurs strictly before
  the determinant clock.

No terminal geometry and no new descent relation are used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace CanonicalPositiveTransverseReesLowLayer

/-- Every coefficient obstructing the determinant-closing positive transverse
Rees transform has exact parameter order strictly below the determinant
clock. -/
theorem coefficientOrder_lt
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (L : CanonicalPositiveTransverseReesLowLayer Delta P) :
    smithFamilyCoefficientOrder P L.exponent < Delta := by
  have hearly := L.early
  rw [canonicalPositiveTransverseReesWeight_finsupp] at hearly
  have hdegree := L.transverseDegree_le_one
  have hcases :
      canonicalTransverseDegree L.exponent = 0 ∨
        canonicalTransverseDegree L.exponent = 1 := by
    omega
  rcases hcases with hzero | hone
  · rw [hzero] at hearly
    simp only [Nat.mul_zero, Nat.add_zero] at hearly
    omega
  · rw [hone] at hearly
    simp only [Nat.mul_one] at hearly
    omega

/-- A low layer is either already visible on the represented special fibre,
or the represented family has a genuine positive actual parameter layer whose
first occurrence is strictly before the determinant clock. -/
theorem specialFiber_or_firstPositiveActual_lt
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (L : CanonicalPositiveTransverseReesLowLayer Delta P) :
    L.exponent ∈ (polynomialFamilySpecialFiber P).support ∨
      ∃ h : HasPositiveActualParameterLayer P,
        firstPositiveActualParameterOrder P h < Delta := by
  let q := smithFamilyCoefficientOrder P L.exponent
  by_cases hqzero : q = 0
  · left
    apply (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
      P L.mem).1
    simpa [q] using hqzero
  · right
    have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
    have hqeq :
        q = smithFamilyCoefficientParameterOrder P L.exponent L.mem := by
      dsimp [q]
      exact smithFamilyCoefficientOrder_eq P L.mem
    have hcoeff :
        (MvPolynomial.coeff L.exponent P).coeff q ≠ 0 := by
      rw [hqeq]
      exact polynomialParameterOrder_coeff_ne_zero
        (MvPolynomial.coeff L.exponent P)
        (MvPolynomial.mem_support_iff.mp L.mem)
    have hqmem : q ∈ familyParameterLayerOrders P := by
      exact (mem_familyParameterLayerOrders_iff P q).2
        ⟨L.exponent, L.mem, hcoeff⟩
    have hactual : HasPositiveActualParameterLayer P := by
      unfold HasPositiveActualParameterLayer
      refine ⟨q, ?_⟩
      exact Finset.mem_filter.mpr ⟨hqmem, hqpos⟩
    refine ⟨hactual, ?_⟩
    have hfirstLe :
        firstPositiveActualParameterOrder P hactual ≤ q :=
      firstPositiveActualParameterOrder_le P hactual hqmem hqpos
    have hqLt : q < Delta := by
      simpa [q] using L.coefficientOrder_lt
    exact lt_of_le_of_lt hfirstLe hqLt

/-- The positive-order branch may be stated without retaining the chosen exact
coefficient order: it already supplies the canonical earliest actual source
layer strictly before the determinant clock. -/
theorem specialFiber_or_earlierActualLayer
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (L : CanonicalPositiveTransverseReesLowLayer Delta P) :
    L.exponent ∈ (polynomialFamilySpecialFiber P).support ∨
      ∃ h : HasPositiveActualParameterLayer P,
        firstPositiveActualParameterOrder P h < Delta :=
  L.specialFiber_or_firstPositiveActual_lt

end CanonicalPositiveTransverseReesLowLayer

end

end HC4.Valuation
