import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerMomentRealisation
import HC4.Valuation.SeparatedRightWallScaleDescent
import Mathlib.Tactic

/-!
# A19 binary homogenization of the singular planar-contact Rees

The singular planar-contact family carries the same integral contact weight as
the represented source, but now on the already-singular planar carrier.  As in
the earlier source-contact construction, inflating the three transverse source
variables once cancels the transverse part of the contact grading.

Thus a carrier monomial `d` acquires the pure binary parameter order

    D - (V + 2) * d₀,

where `D = T.topFace.degree`.  Unlike the historical source-contact family,
the underlying planar-contact family has identically zero Hessian determinant.
The three transverse inflations therefore remain singular as well.

This is the source-honest representation bridge from the all-depth planar
layers to the existing stationary binary staircase-profile machinery.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- Pure longitudinal weight left after cancelling the three transverse
ordinary-degree contributions. -/
def binaryProfileWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (_D : QsOtherFacetPrLeftVPlanarContactReesData F) : ℕ :=
  F.V + 2

/-- Transversely inflated singular planar-contact family. -/
noncomputable def binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  unitTransverseInflateFamily D.family

/-- Exact source coefficient of the binary-homogenized planar-contact family.
The transverse inflation cancels `d₁+d₂+d₃` from the reverse contact order,
leaving only `(V+2)d₀`. -/
theorem coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d D.binaryHomogenizedFamily =
      Polynomial.X ^
          (T.topFace.degree - D.binaryProfileWeight * d (0 : Fin 4)) *
        Polynomial.C (MvPolynomial.coeff d P.carrier) := by
  rw [binaryHomogenizedFamily, coeff_unitTransverseInflateFamily]
  rw [family, reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ P.carrier.support
  · rw [if_pos hd]
    have hbound := D.bound d hd
    rw [qsIntegralContactWeight_finsupp] at hbound ⊢
    have hordinary :
        HC4.Polynomial.ordinaryDegree4 d =
          d 0 + (d 1 + d 2 + d 3) := by
      simp [HC4.Polynomial.ordinaryDegree4]
      ring
    rw [hordinary] at hbound ⊢
    have hweight :
        d 0 + (d 1 + d 2 + d 3) + (F.V + 1) * d 0 =
          (d 1 + d 2 + d 3) + (F.V + 2) * d 0 := by
      ring
    rw [hweight] at hbound
    rw [← mul_assoc]
    rw [← pow_add]
    have hexp :
        d 1 + d 2 + d 3 +
            (T.topFace.degree -
              (d 0 + (d 1 + d 2 + d 3) + (F.V + 1) * d 0)) =
          T.topFace.degree - (F.V + 2) * d 0 := by
      rw [hweight]
      omega
    simpa [binaryProfileWeight] using
      congrArg
        (fun n : ℕ =>
          (Polynomial.X : Polynomial K) ^ n *
            Polynomial.C (MvPolynomial.coeff d P.carrier))
        hexp
  · have hcoeff : MvPolynomial.coeff d P.carrier = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hcoeff]

/-- The binary homogenization remains singular.  This follows directly from
the exact determinant covariance of the three diagonal source inflations and
the singularity of the planar-contact family. -/
theorem binaryHomogenizedFamily_hessianDeterminant_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    HC4.Polynomial.hessianDeterminant D.binaryHomogenizedFamily = 0 := by
  have hzero : HC4.Polynomial.hessianDeterminant D.family = 0 := by
    simpa [family] using D.hessian_zero
  unfold binaryHomogenizedFamily unitTransverseInflateFamily
  rw [hessianDeterminant_kernelInflateHom]
  rw [hessianDeterminant_kernelInflateHom]
  rw [hessianDeterminant_kernelInflateHom]
  rw [hzero]
  simp

/-- Exact longitudinal profile of the singular planar carrier, retaining the
three transverse variables symbolically so no coefficient cancellation is
possible. -/
noncomputable def carrierLongitudinalProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (_D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.finSuccEquiv K 3 P.carrier

/-- Longitudinal polynomial view of the pure binary family. -/
noncomputable def binaryHomogenizedLongitudinal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (MvPolynomial (Fin 3) (Polynomial K)) :=
  MvPolynomial.finSuccEquiv (Polynomial K) 3 D.binaryHomogenizedFamily

/-- Every longitudinal coefficient is exactly one parameter monomial times the
corresponding symbolic coefficient of the planar carrier profile. -/
theorem coeff_binaryHomogenizedLongitudinal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    D.binaryHomogenizedLongitudinal.coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - D.binaryProfileWeight * n)) *
        MvPolynomial.map Polynomial.C
          (D.carrierLongitudinalProfile.coeff n) := by
  ext m
  rw [binaryHomogenizedLongitudinal]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [D.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp [carrierLongitudinalProfile,
    MvPolynomial.finSuccEquiv_coeff_coeff]

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
