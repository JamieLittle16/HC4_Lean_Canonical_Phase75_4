import HC4.Valuation.AdaptiveAlignedSmithCanonicalChartDispatcher
import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.CanonicalSmithDefectExposure
import Mathlib.Tactic

/-!
# Actual positive source layer at a rank-one aligned-Smith closing

The first-contact Newton extraction must be sensitive to *actual parameter
layers*, not only to X-adic valuations of whole source coefficients.

A coefficient

    c(τ) = c₀ + τ^j c_j + ...

has X-adic valuation zero when `c₀ ≠ 0`, even though its positive `j`th layer
may be exactly the layer which closes the Hessian determinant.  Therefore a
rank-one closing cannot honestly be reconstructed from the predicate
`polynomialParameterOrder c > 0` alone.

This file proves the source-level fact which is genuinely forced before any
supporting-cocharacter choice:

* a positive pure Hessian defect prevents the family from being constant in
  the parameter;
* hence the family has a positive *actual* parameter layer in the sense of
  `ActualParameterLayer`;
* for a rank-one Schur closing the defect is positive, because the selected
  first transverse Schur order is positive and equals the defect;
* consequently the honest right-recentered source contains an explicit
  supported source monomial with a nonzero coefficient at a positive actual
  parameter exponent.

This is the correct finite contact witness for the next Newton-polyhedral
supporting-lattice theorem.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Parameter-constant families -/

/-- If a polynomial coefficient has no positive parameter coefficients, it is
the constant polynomial determined by its constant coefficient. -/
theorem polynomial_eq_C_constantCoeff_of_positive_coeff_zero
    (c : Polynomial K)
    (hpos : ∀ n : ℕ, 0 < n → c.coeff n = 0) :
    c = Polynomial.C (Polynomial.constantCoeff c) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [hpos n hnpos, Polynomial.coeff_C]
    simp [Nat.ne_of_gt hnpos]

/-- If no positive actual parameter layer occurs anywhere in a polynomial
family, the family is literally the constant family on its special fibre. -/
theorem polynomialFamily_eq_constantPolynomialFamily_of_no_positiveActualLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hnone : ¬ HasPositiveActualParameterLayer P) :
    P = constantPolynomialFamily (polynomialFamilySpecialFiber P) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_constantPolynomialFamily, coeff_polynomialFamilySpecialFiber]
  apply polynomial_eq_C_constantCoeff_of_positive_coeff_zero
  intro n hnpos
  by_contra hcoeff
  have hd : d ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  have hnLayer :
      n ∈ familyParameterLayerOrders P := by
    exact
      (mem_familyParameterLayerOrders_iff P n).2
        ⟨d, hd, hcoeff⟩
  have hnPositive :
      n ∈ familyPositiveActualLayerOrders P := by
    exact Finset.mem_filter.mpr ⟨hnLayer, hnpos⟩
  exact hnone ⟨n, hnPositive⟩

/-- Hessian determinant commutes with embedding a field-valued polynomial as
a family constant in the parameter. -/
theorem hessianDeterminant_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant
        (constantPolynomialFamily F) =
      constantPolynomialFamily
        (HC4.Polynomial.hessianDeterminant F) := by
  let phi :
      MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.map Polynomial.C
  unfold HC4.Polynomial.hessianDeterminant
  rw [show
      HC4.Polynomial.hessian (constantPolynomialFamily F) =
        (HC4.Polynomial.hessian F).map phi by
    ext i j
    simp [constantPolynomialFamily, phi,
      HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]]
  exact (phi.map_det (HC4.Polynomial.hessian F)).symm

/-- A family with positive pure Hessian defect necessarily contains a
positive *actual* parameter layer.

This deliberately uses the exact finite layer notion rather than X-adic
coefficient valuation. -/
theorem hasPositiveActualParameterLayer_of_hessianDefect_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hDelta : 0 < Delta) :
    HasPositiveActualParameterLayer P := by
  by_contra hnone
  have hconst :
      P = constantPolynomialFamily (polynomialFamilySpecialFiber P) :=
    polynomialFamily_eq_constantPolynomialFamily_of_no_positiveActualLayer
      P hnone
  have hdetconst :=
    hessianDeterminant_constantPolynomialFamily
      (polynomialFamilySpecialFiber P)
  have heq := hdef
  unfold HasPolynomialFamilyHessianDefect at heq
  rw [hconst, hdetconst] at heq
  have hspatial :=
    congrArg (MvPolynomial.coeff (0 : Fin 4 →₀ ℕ)) heq
  have hC :
      MvPolynomial.coeff (0 : Fin 4 →₀ ℕ)
          (MvPolynomial.C (Polynomial.X ^ Delta)) =
        (Polynomial.X ^ Delta : Polynomial K) := by
    rw [MvPolynomial.coeff_C]
    simp only [if_pos]
  have hspatial' :
      Polynomial.C
          (MvPolynomial.coeff 0
            (HC4.Polynomial.hessianDeterminant
              (polynomialFamilySpecialFiber P))) =
        Polynomial.X ^ Delta := by
    rw [hC] at hspatial
    simpa [coeff_constantPolynomialFamily] using hspatial
  have hparameter :=
    congrArg (fun c : Polynomial K => c.coeff Delta) hspatial'
  have hDeltaNe : Delta ≠ 0 := Nat.ne_of_gt hDelta
  have hleft :
      (Polynomial.C
          (MvPolynomial.coeff 0
            (HC4.Polynomial.hessianDeterminant
              (polynomialFamilySpecialFiber P)))).coeff Delta = 0 := by
    simp [Polynomial.coeff_C, hDeltaNe]
  have hright :
      (Polynomial.X ^ Delta : Polynomial K).coeff Delta = 1 := by
    rw [Polynomial.coeff_X_pow]
    simp
  have h01 : (0 : K) = 1 := by
    calc
      0 =
          (Polynomial.C
            (MvPolynomial.coeff 0
              (HC4.Polynomial.hessianDeterminant
                (polynomialFamilySpecialFiber P)))).coeff Delta := hleft.symm
      _ = (Polynomial.X ^ Delta : Polynomial K).coeff Delta := hparameter
      _ = 1 := hright
  exact zero_ne_one h01

/-! ## Rank-one closing source layer -/

/-- A finite source-level witness for an actual positive parameter layer.
Unlike a valuation witness, the source coefficient is allowed to have a
nonzero constant term. -/
structure AdaptiveAlignedSmithActualPositiveLayerWitness
    (P : MvPolynomial (Fin 4) (Polynomial K)) where
  order : ℕ
  order_pos : 0 < order
  exponent : Fin 4 →₀ ℕ
  sourceSupport : exponent ∈ P.support
  coefficient_ne_zero :
    (MvPolynomial.coeff exponent P).coeff order ≠ 0

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Rank-one determinant closing occurs at positive defect. -/
theorem defect_pos
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    0 < B.aligned.endpoint.defect := by
  have hfirst := C.chartData.clock.firstOrder_pos
  rw [C.closing.1] at hfirst
  exact hfirst

/-- Therefore the honest right-recentered source family contains a positive
actual parameter layer. -/
theorem hasPositiveActualParameterLayer
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    HasPositiveActualParameterLayer C.family := by
  exact
    hasPositiveActualParameterLayer_of_hessianDefect_pos
      C.family C.family_hessianDefect C.defect_pos

/-- Canonical least positive actual source-layer order at the closing. -/
noncomputable def firstActualLayerOrder
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : ℕ :=
  firstPositiveActualParameterOrder
    C.family C.hasPositiveActualParameterLayer

theorem firstActualLayerOrder_pos
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    0 < C.firstActualLayerOrder := by
  exact
    firstPositiveActualParameterOrder_pos
      C.family C.hasPositiveActualParameterLayer

/-- The canonical least positive actual layer is realised by an honest
source monomial of the same right-recentered family that carries the exact
Schur chart. -/
theorem firstActualLayerOrder_realised
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    ∃ d ∈ C.family.support,
      (MvPolynomial.coeff d C.family).coeff
        C.firstActualLayerOrder ≠ 0 := by
  exact
    firstPositiveActualParameterOrder_realised
      C.family C.hasPositiveActualParameterLayer

/-- Package the finite actual-layer witness selected canonically from the
rank-one closing source. -/
theorem exists_actualPositiveLayerWitness
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    Nonempty (AdaptiveAlignedSmithActualPositiveLayerWitness C.family) := by
  rcases C.firstActualLayerOrder_realised with
    ⟨d, hd, hcoeff⟩
  exact ⟨{
    order := C.firstActualLayerOrder
    order_pos := C.firstActualLayerOrder_pos
    exponent := d
    sourceSupport := hd
    coefficient_ne_zero := hcoeff
  }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## The corrected Newton extraction target -/

/-- The next genuinely geometric statement is now isolated correctly:
starting from the actual positive source layer forced above, choose a
supporting integral source lattice which makes a positive layer first contact.

The witness is layer-sensitive: it does *not* require the whole source
coefficient to have positive X-adic valuation. -/
structure AdaptiveAlignedSmithLayerSensitiveFirstContactData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B) where
  weight : Fin 4 → ℕ
  commonLevel : ℕ
  R : ℕ
  R_pos : 0 < R
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure
      R weight commonLevel
      B.aligned.endpoint.rightRecenteredFamily
  rightSectionIntegrality :
    HasIntegralAdaptiveSmithSection weight
      (parameterRamificationSection
        (K := K) R
        B.aligned.endpoint.rightRecenteredRightSection)
  determinantExponentNonnegative :
    4 * commonLevel ≤
      R * B.aligned.endpoint.defect +
        2 * ∑ i : Fin 4, weight i
  contactOrder : ℕ
  contactOrderPositive : 0 < contactOrder
  contactExponent : Fin 4 →₀ ℕ
  contactSupport :
    contactExponent ∈
      B.aligned.endpoint.rightRecenteredFamily.support
  contactCoefficient_ne_zero :
    (MvPolynomial.coeff contactExponent
      B.aligned.endpoint.rightRecenteredFamily).coeff
        contactOrder ≠ 0
  contactLevel :
    R * contactOrder +
      Finsupp.weight weight contactExponent =
        commonLevel

/-- Rank-one closing version of the corrected layer-sensitive extraction
target.  All source, collision, and chart provenance remains on `C`; only the
finite supporting-lattice choice is left here. -/
abbrev AdaptiveAlignedSmithRankOneClosingLayerSensitiveFirstContactData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :=
  AdaptiveAlignedSmithLayerSensitiveFirstContactData B C.source

end

end HC4.Valuation
