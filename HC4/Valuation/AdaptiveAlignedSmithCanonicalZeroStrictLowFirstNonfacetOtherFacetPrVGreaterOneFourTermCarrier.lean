import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
import Mathlib.Tactic

/-!
# A19 literal four-term carrier after interior elimination

Once the non-unit quotient staircase has no strict-interior support, the whole
planar carrier consists of the two locked source monomials and the two
primitive highest monomials.  This file turns that support statement into a
literal polynomial equality and names the four genuine source coefficients.

It is intentionally independent of the later `Y = y w^V`, `H = z w^V`
notation.  The next adapter only has to normalize these four monomials into the
existing `twoFunctionCarrier` API.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Literal four source coefficients and exact four-monomial reconstruction of
the left-oriented non-unit carrier. -/
structure QsOtherFacetPrLeftVFourTermCarrierData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) where
  a : K
  b : K
  p : K
  q : K
  a_eq : a = MvPolynomial.coeff C.ray.facetExponent P.carrier
  b_eq : b = MvPolynomial.coeff C.ray.outsideExponent P.carrier
  p_eq : p = MvPolynomial.coeff F.highest.e0 P.carrier
  q_eq : q = MvPolynomial.coeff F.highest.e1 P.carrier
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  p_ne : p ≠ 0
  q_ne : q ≠ 0
  carrier_eq :
    P.carrier =
      MvPolynomial.monomial C.ray.facetExponent a +
      MvPolynomial.monomial C.ray.outsideExponent b +
      MvPolynomial.monomial F.highest.e0 p +
      MvPolynomial.monomial F.highest.e1 q

/-- `NoStrictInteriorSupport` upgrades directly to the literal four-term
source polynomial.  No coefficient is recreated: all four are coefficients of
`P.carrier` itself and their nonvanishing is supplied by the existing
provenance packages. -/
theorem QsOtherFacetPrLeftVContactFrontierData.fourTermCarrierData_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrLeftVFourTermCarrierData F) := by
  classical
  let a := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let p := MvPolynomial.coeff F.highest.e0 P.carrier
  let q := MvPolynomial.coeff F.highest.e1 P.carrier
  have hFO : C.ray.facetExponent ≠ C.ray.outsideExponent := by
    intro h
    have h0 : C.ray.facetExponent 0 = C.ray.outsideExponent 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.facet_zero, F.locked.outside_zero] at h0
    omega
  have hFH0 : C.ray.facetExponent ≠ F.highest.e0 := by
    intro h
    have h1 : C.ray.facetExponent 1 = F.highest.e0 1 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
    rw [F.locked.facet_one, F.highest.e0_one] at h1
    omega
  have hFH1 : C.ray.facetExponent ≠ F.highest.e1 := by
    intro h
    have h0 : C.ray.facetExponent 0 = F.highest.e1 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.facet_zero, F.highest.e1_zero] at h0
    omega
  have hOH0 : C.ray.outsideExponent ≠ F.highest.e0 := by
    intro h
    have h0 : C.ray.outsideExponent 0 = F.highest.e0 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.outside_zero, F.highest.e0_zero] at h0
    omega
  have hOH1 : C.ray.outsideExponent ≠ F.highest.e1 := by
    intro h
    have h1 : C.ray.outsideExponent 1 = F.highest.e1 1 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
    rw [F.locked.outside_one, F.highest.e1_one] at h1
    omega
  have hH01 : F.highest.e0 ≠ F.highest.e1 := by
    intro h
    have h0 : F.highest.e0 0 = F.highest.e1 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.highest.e0_zero, F.highest.e1_zero] at h0
    omega
  have hsupp := F.support_eq_locked_highest_of_noStrictInterior hno
  have hsum := MvPolynomial.as_sum P.carrier
  rw [hsupp] at hsum
  have hcarrier :
      P.carrier =
        MvPolynomial.monomial C.ray.facetExponent a +
        MvPolynomial.monomial C.ray.outsideExponent b +
        MvPolynomial.monomial F.highest.e0 p +
        MvPolynomial.monomial F.highest.e1 q := by
    dsimp [a, b, p, q]
    simpa [Finset.sum_insert, hFO, hFH0, hFH1, hOH0, hOH1, hH01,
      Ne.symm hFO, Ne.symm hFH0, Ne.symm hFH1,
      Ne.symm hOH0, Ne.symm hOH1, Ne.symm hH01,
      add_assoc] using hsum
  exact ⟨{
    a := a
    b := b
    p := p
    q := q
    a_eq := rfl
    b_eq := rfl
    p_eq := rfl
    q_eq := rfl
    a_ne := by
      dsimp [a]
      exact F.locked.facet_provenance.carrier_coeff_ne
    b_ne := by
      dsimp [b]
      exact F.locked.outside_provenance.carrier_coeff_ne
    p_ne := by
      dsimp [p]
      exact F.highest.e0_provenance.carrier_coeff_ne
    q_ne := by
      dsimp [q]
      exact F.highest.e1_provenance.carrier_coeff_ne
    carrier_eq := hcarrier
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
