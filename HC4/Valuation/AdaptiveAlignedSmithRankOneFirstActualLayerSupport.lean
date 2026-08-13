import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerCausality
import HC4.Valuation.AdaptiveAlignedSmithClosingFirstContactLattice
import Mathlib.Tactic

/-!
# Fresh versus overlapping first actual source support

The least positive *actual* parameter layer of a rank-one closing can arise
in two genuinely different ways.

* **fresh support**: some monomial appearing at the first positive layer is
  absent from the old special fibre;
* **overlap support**: every monomial of the first positive layer was already
  present in the old special fibre, so only its coefficient changes.

This distinction matters for the terminal Newton extraction.  A diagonal
whole-family exposure is controlled by the exact `X`-adic order of each
source coefficient.  Therefore it can make an actual layer `j` first contact
only when the selected source coefficient has exact `X`-adic order `j`.
In particular, a coefficient such as `1 + X^j` cannot be exposed at its
`j`th layer while the old constant term is kept in the same whole-family
exposure.

The overlap case must instead use the already-green relative factorisation

    P = P(0) + X^j Q,

whose quotient has special fibre exactly the first actual coefficient
potential.  This file makes that source-level dichotomy formal, so the next
absorption theorem cannot accidentally use the older valuation-only
first-contact interface on the wrong branch.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Exact parameter order detects the first nonzero coefficient -/

/-- A nonzero coefficient at order `n` bounds the exact `X`-adic order by
`n`. -/
theorem polynomialParameterOrder_le_of_coeff_ne_zero
    (c : Polynomial K)
    (hc : c ≠ 0)
    {n : ℕ}
    (hn : c.coeff n ≠ 0) :
    polynomialParameterOrder c hc ≤ n := by
  by_contra hnot
  have hlt : n < polynomialParameterOrder c hc :=
    Nat.lt_of_not_ge hnot
  have hdiv := polynomialParameterOrder_dvd c hc
  rw [Polynomial.X_pow_dvd_iff] at hdiv
  exact hn (hdiv n hlt)

/-- The coefficient at the selected exact `X`-adic order is nonzero. -/
theorem polynomialParameterOrder_coeff_ne_zero
    (c : Polynomial K)
    (hc : c ≠ 0) :
    c.coeff (polynomialParameterOrder c hc) ≠ 0 := by
  let q := polynomialParameterOrder c hc
  have hdiv := polynomialParameterOrder_dvd c hc
  rw [Polynomial.X_pow_dvd_iff] at hdiv
  intro hqzero
  apply polynomialParameterOrder_succ_not_dvd c hc
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  by_cases hnq : n = q
  · subst n
    exact hqzero
  · exact hdiv n (by
      dsimp [q] at hnq ⊢
      omega)

/-- At the globally least positive *actual* parameter layer, a source
coefficient contributing to that layer has exact `X`-adic order either zero
(the monomial already belongs to the special fibre) or exactly the selected
first actual order (the monomial is fresh at that layer).  No intermediate
positive order is possible by minimality. -/
theorem smithFamilyCoefficientParameterOrder_zero_or_firstPositiveActual
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hcoeff :
      (MvPolynomial.coeff d P).coeff
        (firstPositiveActualParameterOrder P h) ≠ 0) :
    smithFamilyCoefficientParameterOrder P d hd = 0 ∨
      smithFamilyCoefficientParameterOrder P d hd =
        firstPositiveActualParameterOrder P h := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  let j := firstPositiveActualParameterOrder P h
  have hqle : q ≤ j := by
    simpa [q, j, c, smithFamilyCoefficientParameterOrder] using
      polynomialParameterOrder_le_of_coeff_ne_zero c hc hcoeff
  by_cases hqzero : q = 0
  · exact Or.inl (by simpa [q] using hqzero)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
    have hqcoeff : c.coeff q ≠ 0 := by
      simpa [q, c, smithFamilyCoefficientParameterOrder] using
        polynomialParameterOrder_coeff_ne_zero c hc
    have hqmem : q ∈ familyParameterLayerOrders P := by
      exact
        (mem_familyParameterLayerOrders_iff P q).2
          ⟨d, hd, by simpa [c] using hqcoeff⟩
    have hjle : j ≤ q := by
      simpa [j] using
        firstPositiveActualParameterOrder_le P h hqmem hqpos
    exact Or.inr (by
      have : q = j := Nat.le_antisymm hqle hjle
      simpa [q, j] using this)

/-! ## Fresh and overlapping first support -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Some monomial of the first positive actual layer is absent from the old
special fibre. -/
def FirstActualLayerHasFreshSupport
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∃ d,
    d ∈ (familyParameterLayer C.family C.firstActualLayerOrder).support ∧
      d ∉ (polynomialFamilySpecialFiber C.family).support

/-- Every monomial of the first positive actual layer was already present in
the old special fibre. -/
def FirstActualLayerSupportContainedInSpecialFiber
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∀ ⦃d : Fin 4 →₀ ℕ⦄,
    d ∈ (familyParameterLayer C.family C.firstActualLayerOrder).support →
      d ∈ (polynomialFamilySpecialFiber C.family).support

/-- The first actual layer has an exhaustive fresh/overlap support split. -/
theorem firstActualLayer_fresh_or_overlap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.FirstActualLayerHasFreshSupport ∨
      C.FirstActualLayerSupportContainedInSpecialFiber := by
  classical
  by_cases hfresh : C.FirstActualLayerHasFreshSupport
  · exact Or.inl hfresh
  · right
    intro d hd
    by_contra hnot
    exact hfresh ⟨d, hd, hnot⟩

/-- For a coefficient which contributes to the selected first actual layer,
being fresh relative to the special fibre is equivalent to having exact
`X`-adic order equal to that first actual layer. -/
theorem firstActualLayer_sourceCoefficient_fresh_iff_parameterOrder_eq_first
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ C.family.support)
    (hcoeff :
      (MvPolynomial.coeff d C.family).coeff
        C.firstActualLayerOrder ≠ 0) :
    d ∉ (polynomialFamilySpecialFiber C.family).support ↔
      smithFamilyCoefficientParameterOrder C.family d hd =
        C.firstActualLayerOrder := by
  have hsplit :=
    smithFamilyCoefficientParameterOrder_zero_or_firstPositiveActual
      C.family C.hasPositiveActualParameterLayer hd hcoeff
  constructor
  · intro hfresh
    rcases hsplit with hzero | hfirst
    · exfalso
      apply hfresh
      apply
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          C.family hd).1
      rw [smithFamilyCoefficientOrder_eq C.family hd]
      exact hzero
    · exact hfirst
  · intro hfirst hspecial
    have hzero : smithFamilyCoefficientOrder C.family d = 0 :=
      (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
        C.family hd).2 hspecial
    rw [smithFamilyCoefficientOrder_eq C.family hd] at hzero
    have hjpos := C.firstActualLayerOrder_pos
    rw [hfirst] at hzero
    exact (Nat.ne_of_gt hjpos) hzero

/-- In the overlap branch the honest relative first-deformation quotient has
special fibre supported entirely on the old special fibre.  This is the
precise source object on which an absorption/right-equivalence argument must
operate. -/
theorem relativeFirstActualDeformation_specialFiber_support_subset_of_overlap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hoverlap : C.FirstActualLayerSupportContainedInSpecialFiber) :
    (polynomialFamilySpecialFiber
        C.relativeFirstActualDeformationFamily).support ⊆
      (polynomialFamilySpecialFiber C.family).support := by
  rw [C.relativeFirstActualDeformation_specialFiber]
  intro d hd
  exact hoverlap hd

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Whole-family first contact only sees fresh support -/

namespace AdaptiveAlignedSmithLayerSensitiveFirstContactData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- A layer-sensitive whole-family first-contact equation can occur only at
the exact `X`-adic order of its selected source coefficient.

This is the formal obstruction to exposing the `j`th term of a coefficient
such as `1 + X^j` without first freezing/subtracting the old special fibre. -/
theorem contactOrder_eq_parameterOrder
    (L : AdaptiveAlignedSmithLayerSensitiveFirstContactData B source) :
    smithFamilyCoefficientParameterOrder
        B.aligned.endpoint.rightRecenteredFamily
        L.contactExponent L.contactSupport =
      L.contactOrder := by
  let P := B.aligned.endpoint.rightRecenteredFamily
  let d := L.contactExponent
  let q := smithFamilyCoefficientParameterOrder P d L.contactSupport
  let j := L.contactOrder
  let w := Finsupp.weight L.weight d
  have hc : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp L.contactSupport
  have hqle : q ≤ j := by
    simpa [q, j, P, d, smithFamilyCoefficientParameterOrder] using
      polynomialParameterOrder_le_of_coeff_ne_zero
        (MvPolynomial.coeff d P) hc L.contactCoefficient_ne_zero
  have hcommon : L.commonLevel ≤ L.R * q + w := by
    simpa [P, d, q, w] using
      adaptiveSmithFirstContactExposure_commonLevel_le_exactOrder
        L.R L.R_pos P L.familyIntegrality L.contactSupport
  have hjle : j ≤ q := by
    by_contra hnot
    have hqj : q < j := Nat.lt_of_not_ge hnot
    have hmul : L.R * q < L.R * j :=
      Nat.mul_lt_mul_of_pos_left hqj L.R_pos
    have hlt : L.R * q + w < L.commonLevel := by
      calc
        L.R * q + w < L.R * j + w := Nat.add_lt_add_right hmul w
        _ = L.commonLevel := by
          simpa [j, d, w] using L.contactLevel
    exact (Nat.not_lt_of_ge hcommon) hlt
  have hqj : q = j := Nat.le_antisymm hqle hjle
  simpa [q, j, P, d] using hqj

end AdaptiveAlignedSmithLayerSensitiveFirstContactData

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- If a corrected whole-family first-contact witness selects the canonical
least positive actual layer, its contact monomial is necessarily fresh
relative to the old special fibre.  Thus the overlap branch cannot be
silently discharged by a diagonal whole-family exposure. -/
theorem firstActualLayerContact_hasFreshSupport
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (L : AdaptiveAlignedSmithRankOneClosingLayerSensitiveFirstContactData C)
    (hcontact : L.contactOrder = C.firstActualLayerOrder) :
    C.FirstActualLayerHasFreshSupport := by
  let P := C.family
  let d := L.contactExponent
  have hdLayer :
      d ∈ (familyParameterLayer P C.firstActualLayerOrder).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [familyParameterLayer_coeff]
    simpa [P, d, hcontact] using L.contactCoefficient_ne_zero
  refine ⟨d, hdLayer, ?_⟩
  intro hspecial
  have hzero : smithFamilyCoefficientOrder P d = 0 :=
    (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
      P L.contactSupport).2 hspecial
  rw [smithFamilyCoefficientOrder_eq P L.contactSupport] at hzero
  have horder := L.contactOrder_eq_parameterOrder
  have hpos := C.firstActualLayerOrder_pos
  have heq :
      smithFamilyCoefficientParameterOrder P d L.contactSupport =
        C.firstActualLayerOrder := by
    calc
      smithFamilyCoefficientParameterOrder P d L.contactSupport =
          L.contactOrder := by simpa [P, d] using horder
      _ = C.firstActualLayerOrder := hcontact
  rw [heq] at hzero
  exact (Nat.ne_of_gt hpos) hzero

/-- **Support-refined two-way closing frontier.**

After the causality theorem there are only:

* direct closing at `j = Delta`; or
* a genuinely earlier Schur-tangential layer, and that layer is either
  fresh support (eligible for honest whole-family first contact) or overlap
  support (which must be handled through the relative quotient).

This is the precise input for the next two local patches. -/
theorem firstActualLayer_preclosingSupportFrontier_or_directClosing
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder ∧
      (C.FirstActualLayerHasFreshSupport ∨
        C.FirstActualLayerSupportContainedInSpecialFiber)) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      (C.chartData.clock.series.offDiag.coeff
            C.firstActualLayerOrder ≠ 0 ∨
       C.chartData.clock.series.kernel.coeff
            C.firstActualLayerOrder ≠ 0)) := by
  rcases C.firstActualLayer_preclosingTangential_or_directClosing with
    hpre | hclose
  · exact Or.inl ⟨hpre.1, hpre.2, C.firstActualLayer_fresh_or_overlap⟩
  · exact Or.inr hclose

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
