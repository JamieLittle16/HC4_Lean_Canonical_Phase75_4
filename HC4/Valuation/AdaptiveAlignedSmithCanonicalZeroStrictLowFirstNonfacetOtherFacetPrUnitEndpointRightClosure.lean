import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointClosure
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# A19 endpoint-only right unit PR closure

The right unit endpoint-only carrier is the transverse-coordinate mirror of the
already-closed left carrier.  At `V = 1` the locked pair is fixed by swapping
coordinates `2` and `3`, while the primitive highest pair is carried exactly to
the standard left two-function exponents.

This file performs only that coordinate transport.  Hessian singularity is
moved through the existing permutation covariance theorem and all determinant
algebra remains delegated to `twoFunctionCarrier_hessian_impossible`.
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

private def unitTransverseSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3

@[simp] private theorem unitTransverseSwap_mapDomain_zero
    (e : Fin 4 →₀ ℕ) :
    (e.mapDomain unitTransverseSwap) (0 : Fin 4) = e 0 := by
  simpa [unitTransverseSwap] using
    (Finsupp.mapDomain_apply_of_injective
      unitTransverseSwap.injective e (0 : Fin 4))

@[simp] private theorem unitTransverseSwap_mapDomain_one
    (e : Fin 4 →₀ ℕ) :
    (e.mapDomain unitTransverseSwap) (1 : Fin 4) = e 1 := by
  simpa [unitTransverseSwap] using
    (Finsupp.mapDomain_apply_of_injective
      unitTransverseSwap.injective e (1 : Fin 4))

@[simp] private theorem unitTransverseSwap_mapDomain_two
    (e : Fin 4 →₀ ℕ) :
    (e.mapDomain unitTransverseSwap) (2 : Fin 4) = e 3 := by
  simpa [unitTransverseSwap] using
    (Finsupp.mapDomain_apply_of_injective
      unitTransverseSwap.injective e (3 : Fin 4))

@[simp] private theorem unitTransverseSwap_mapDomain_three
    (e : Fin 4 →₀ ℕ) :
    (e.mapDomain unitTransverseSwap) (3 : Fin 4) = e 2 := by
  simpa [unitTransverseSwap] using
    (Finsupp.mapDomain_apply_of_injective
      unitTransverseSwap.injective e (2 : Fin 4))

private theorem unitRight_locked_facet_mapDomain_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    C.ray.facetExponent.mapDomain unitTransverseSwap =
      HC4.Polynomial.twoFunctionLockedFacetExponent 1 F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionLockedFacetExponent,
      HC4.Polynomial.twoFunctionHExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three] <;> ring

private theorem unitRight_locked_outside_mapDomain_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    C.ray.outsideExponent.mapDomain unitTransverseSwap =
      HC4.Polynomial.twoFunctionLockedOutsideExponent 1 F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionLockedOutsideExponent,
      HC4.Polynomial.twoFunctionHExponent,
      F.locked.outside_zero, F.locked.outside_one,
      F.locked.outside_two, F.locked.outside_three] <;> ring

private theorem unitRight_highest_e0_mapDomain_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    F.highest.e0.mapDomain unitTransverseSwap =
      HC4.Polynomial.twoFunctionHighestZExponent 1 F.highest.n := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionHighestZExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one] <;> ring

private theorem unitRight_highest_e1_mapDomain_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    F.highest.e1.mapDomain unitTransverseSwap =
      HC4.Polynomial.twoFunctionHighestXExponent 1 F.highest.n := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionHighestXExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e1_zero, F.highest.e1_one,
      F.highest.e1_two, F.highest.e1_three,
      F.highest_V_eq_one] <;> ring

/-- Endpoint-only right unit support is the `swap 2 3` image of the standard
left two-function carrier, hence is impossible by Hessian covariance and the
already-verified state-free two-function contradiction. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.impossible_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) : False := by
  classical
  let a := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let p := MvPolynomial.coeff F.highest.e0 P.carrier
  let q := MvPolynomial.coeff F.highest.e1 P.carrier
  have ha : a ≠ 0 := by
    dsimp [a]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hp : p ≠ 0 := by
    dsimp [p]
    exact F.highest.e0_provenance.carrier_coeff_ne
  have hq : q ≠ 0 := by
    dsimp [q]
    exact F.highest.e1_provenance.carrier_coeff_ne
  have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
  have hFO : C.ray.facetExponent ≠ C.ray.outsideExponent := by
    intro h
    have h0 : C.ray.facetExponent 0 = C.ray.outsideExponent 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    simp [F.locked.facet_zero, F.locked.outside_zero] at h0
  have hFH0 : C.ray.facetExponent ≠ F.highest.e0 := by
    intro h
    have hpdeg := congrArg (fun e : Fin 4 →₀ ℕ => e 0 + e 1) h
    simp [F.locked.facet_zero, F.locked.facet_one,
      F.highest.e0_zero, F.highest.e0_one] at hpdeg
    omega
  have hFH1 : C.ray.facetExponent ≠ F.highest.e1 := by
    intro h
    have hpdeg := congrArg (fun e : Fin 4 →₀ ℕ => e 0 + e 1) h
    simp [F.locked.facet_zero, F.locked.facet_one,
      F.highest.e1_zero, F.highest.e1_one] at hpdeg
    omega
  have hOH0 : C.ray.outsideExponent ≠ F.highest.e0 := by
    intro h
    have hpdeg := congrArg (fun e : Fin 4 →₀ ℕ => e 0 + e 1) h
    simp [F.locked.outside_zero, F.locked.outside_one,
      F.highest.e0_zero, F.highest.e0_one] at hpdeg
    omega
  have hOH1 : C.ray.outsideExponent ≠ F.highest.e1 := by
    intro h
    have hpdeg := congrArg (fun e : Fin 4 →₀ ℕ => e 0 + e 1) h
    simp [F.locked.outside_zero, F.locked.outside_one,
      F.highest.e1_zero, F.highest.e1_one] at hpdeg
    omega
  have hH01 : F.highest.e0 ≠ F.highest.e1 := by
    intro h
    have h0 : F.highest.e0 0 = F.highest.e1 0 := by
      simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    simp [F.highest.e0_zero, F.highest.e1_zero] at h0
  have hsupp := F.support_eq_locked_highest_of_noStrictInterior hno
  have hsum := MvPolynomial.as_sum P.carrier
  rw [hsupp] at hsum
  have hfour :
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
  let Ppoly : Polynomial K := Polynomial.monomial F.highest.n p
  let Qpoly : Polynomial K := Polynomial.monomial (F.highest.n - 1) q
  have hn1 : F.highest.n - 1 ≠ 0 := by omega
  have hQderiv : Qpoly.derivative ≠ 0 := by
    dsimp [Qpoly]
    rw [Polynomial.derivative_monomial]
    rw [Polynomial.monomial_eq_zero_iff]
    exact mul_ne_zero hq ((Nat.cast_ne_zero).2 hn1)
  have hrenamed :
      MvPolynomial.rename unitTransverseSwap P.carrier =
        HC4.Polynomial.twoFunctionCarrier
          1 F.locked.ell a b Ppoly Qpoly := by
    calc
      MvPolynomial.rename unitTransverseSwap P.carrier =
          MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedFacetExponent 1 F.locked.ell) a +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedOutsideExponent 1 F.locked.ell) b +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestZExponent 1 F.highest.n) p +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestXExponent 1 F.highest.n) q := by
        rw [hfour]
        simp only [map_add, MvPolynomial.rename_monomial]
        rw [unitRight_locked_facet_mapDomain_eq_twoFunctionExponent F,
          unitRight_locked_outside_mapDomain_eq_twoFunctionExponent F,
          unitRight_highest_e0_mapDomain_eq_twoFunctionExponent F,
          unitRight_highest_e1_mapDomain_eq_twoFunctionExponent F]
      _ = HC4.Polynomial.twoFunctionCarrier
          1 F.locked.ell a b Ppoly Qpoly := by
        symm
        simpa [Ppoly, Qpoly] using
          (HC4.Polynomial.twoFunctionCarrier_monomial_normalForm
            (K := K) 1 F.locked.ell F.highest.n a b p q)
  have hdetRenamed :
      HC4.Polynomial.hessianDeterminant
        (MvPolynomial.rename unitTransverseSwap P.carrier) = 0 := by
    rw [HC4.Newton.hessianDeterminant_rename_perm]
    rw [P.hessian_zero]
    simp
  have hdetCarrier :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.twoFunctionCarrier
          1 F.locked.ell a b Ppoly Qpoly) = 0 := by
    rw [← hrenamed]
    exact hdetRenamed
  exact HC4.Polynomial.twoFunctionCarrier_hessian_impossible
    1 F.locked.ell (by norm_num) F.locked.ell_pos
    a b ha hb Ppoly Qpoly hQderiv hdetCarrier

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
