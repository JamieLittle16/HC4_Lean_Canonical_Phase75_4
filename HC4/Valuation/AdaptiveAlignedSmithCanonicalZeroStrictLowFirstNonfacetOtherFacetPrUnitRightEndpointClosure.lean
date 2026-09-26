import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointClosure
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# A19 right endpoint-only unit PR closure

The left endpoint-only unit branch is already the concrete two-function
carrier.  At `V = 1`, the right branch differs only by swapping transverse
coordinates `2` and `3`: the locked pair is fixed, while the primitive highest
pair is carried to the left two-function highest pair.  Hessian determinant
zero is invariant under the same coordinate permutation, so the existing
state-free two-function contradiction closes the right branch without any new
determinant algebra.
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

private noncomputable def unitSwap23 : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

private theorem swap23_zero :
    (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by
  decide

private theorem swap23_one :
    (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by
  decide

private theorem swap23_two :
    (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by
  decide

private theorem swap23_three :
    (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by
  decide

private theorem unitRight_locked_facet_swap_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    Finsupp.mapDomain unitSwap23 C.ray.facetExponent =
      HC4.Polynomial.twoFunctionLockedFacetExponent 1 F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [unitSwap23, swap23_zero, swap23_one, swap23_two, swap23_three,
      HC4.Polynomial.twoFunctionLockedFacetExponent,
      HC4.Polynomial.twoFunctionHExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three] <;> omega

private theorem unitRight_locked_outside_swap_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    Finsupp.mapDomain unitSwap23 C.ray.outsideExponent =
      HC4.Polynomial.twoFunctionLockedOutsideExponent 1 F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [unitSwap23, swap23_zero, swap23_one, swap23_two, swap23_three,
      HC4.Polynomial.twoFunctionLockedOutsideExponent,
      HC4.Polynomial.twoFunctionHExponent,
      F.locked.outside_zero, F.locked.outside_one,
      F.locked.outside_two, F.locked.outside_three] <;> omega

private theorem unitRight_highest_e0_swap_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    Finsupp.mapDomain unitSwap23 F.highest.e0 =
      HC4.Polynomial.twoFunctionHighestZExponent 1 F.highest.n := by
  ext i
  fin_cases i <;>
    simp [unitSwap23, swap23_zero, swap23_one, swap23_two, swap23_three,
      HC4.Polynomial.twoFunctionHighestZExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one] <;> omega

private theorem unitRight_highest_e1_swap_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    Finsupp.mapDomain unitSwap23 F.highest.e1 =
      HC4.Polynomial.twoFunctionHighestXExponent 1 F.highest.n := by
  ext i
  fin_cases i <;>
    simp [unitSwap23, swap23_zero, swap23_one, swap23_two, swap23_three,
      HC4.Polynomial.twoFunctionHighestXExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e1_zero, F.highest.e1_one,
      F.highest.e1_two, F.highest.e1_three,
      F.highest_V_eq_one] <;> omega

/-- The endpoint-only right unit branch is the transverse rename of the
existing concrete two-function carrier, hence is impossible. -/
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

  have hrenamedFour :
      MvPolynomial.rename unitSwap23 P.carrier =
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
    rw [unitRight_locked_facet_swap_eq_twoFunctionExponent F,
      unitRight_locked_outside_swap_eq_twoFunctionExponent F,
      unitRight_highest_e0_swap_eq_twoFunctionExponent F,
      unitRight_highest_e1_swap_eq_twoFunctionExponent F]

  have hcarrier :
      MvPolynomial.rename unitSwap23 P.carrier =
        HC4.Polynomial.twoFunctionCarrier
          1 F.locked.ell a b Ppoly Qpoly := by
    calc
      MvPolynomial.rename unitSwap23 P.carrier =
          MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedFacetExponent 1 F.locked.ell) a +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedOutsideExponent 1 F.locked.ell) b +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestZExponent 1 F.highest.n) p +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestXExponent 1 F.highest.n) q := hrenamedFour
      _ = HC4.Polynomial.twoFunctionCarrier
          1 F.locked.ell a b Ppoly Qpoly := by
        symm
        simpa [Ppoly, Qpoly] using
          (HC4.Polynomial.twoFunctionCarrier_monomial_normalForm
            (K := K) 1 F.locked.ell F.highest.n a b p q)

  have hdetRename :
      HC4.Polynomial.hessianDeterminant
          (MvPolynomial.rename unitSwap23 P.carrier) = 0 := by
    rw [HC4.Newton.hessianDeterminant_rename_perm]
    rw [P.hessian_zero]
    simp

  apply HC4.Polynomial.twoFunctionCarrier_hessian_impossible
    1 F.locked.ell (by norm_num) F.locked.ell_pos
    a b ha hb Ppoly Qpoly hQderiv
  rw [← hcarrier]
  exact hdetRename

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
