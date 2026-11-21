import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryDeterminantCancellation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryCouplingCorrection
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDeterminantExtraction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianFractionRecognition
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileTwoCoefficientRigidity
import Mathlib.Tactic

/-!
# A19.119 / R19: contact fraction-profile rigidity

A19.114 constructs the exact symbolic longitudinal profile of the represented
source, and A19.115 injects it into the fraction field of the transverse
coefficient domain without losing its constant coefficient or degree.

The historical closing interface asked for the complete stationary residual
to vanish.  R18.21 has now isolated the two coefficients actually used by the
finite staircase contradiction: the leading `N+N` coefficient and the
next-highest `N+M` coefficient.  This file therefore owns both consumers.

The integral profile Hessian maps exactly to the canonical fraction-field
staircase residual.  Consequently two zero integral profile-Hessian
determinant coefficients already imply `False`.  The binary-family layer
interface is retained as a thin adapter for callers that naturally own those
exact parameter layers.

No transverse evaluation, planar JC2 hypothesis, or division in the geometric
coefficient ring is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The A19.115 fraction-field profile is impossible as soon as the honest
contact/Schur calculation supplies the stationary residual equation. -/
theorem QsOtherFacetContactFractionProfilePackage.impossible_of_residual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (H : QsOtherFacetContactFractionProfilePackage C P)
    (hres :
      binaryStaircaseProfileResidual
        T.topFace.degree P.profileWeight H.profile = 0) : False := by
  have hle : H.profile.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := qsContactProfileField K)
      T.topFace.degree P.profileWeight P.profileWeight_two_le H.profile
      H.coeff_zero_ne H.support_bound hres
  have htwo : 2 ≤ H.profile.natDegree := H.degree_two_le
  omega

/-- **R19 localization identity.**  Mapping the honest integral profile Hessian
determinant into the transverse fraction field gives exactly the canonical
stationary staircase residual of the mapped profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.fractionMap_profileHessianDet_eq_residual
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Polynomial.map
        (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
        R.profileHessianDet =
      binaryStaircaseProfileResidual T.topFace.degree P.profileWeight
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
          R.profile) := by
  let A := MvPolynomial (Fin 3) K
  let L := qsContactProfileField K
  let ι : A →+* L := algebraMap A L
  change Polynomial.map ι R.profileHessianDet =
    binaryStaircaseProfileResidual T.topFace.degree P.profileWeight
      (Polynomial.map ι R.profile)
  have h00coeff : ∀ n : ℕ,
      (Polynomial.map ι R.profileHessian00).coeff n =
        (((T.topFace.degree : L) - (P.profileWeight : L) * (n : L)) *
          ((T.topFace.degree : L) - (P.profileWeight : L) * (n : L) - 1)) *
          (Polynomial.map ι R.profile).coeff n := by
    intro n
    simpa [A, L, ι] using congrArg ι (R.coeff_profileHessian00 n)
  have h01coeff : ∀ n : ℕ,
      (Polynomial.map ι R.profileHessian01).coeff n =
        (n : L) *
          ((T.topFace.degree : L) - (P.profileWeight : L) * (n : L)) *
          (Polynomial.map ι R.profile).coeff n := by
    intro n
    simpa [A, L, ι] using congrArg ι (R.coeff_profileHessian01 n)
  have h11coeff : ∀ n : ℕ,
      (Polynomial.map ι R.profileHessian11).coeff n =
        (n : L) * ((n : L) - 1) *
          (Polynomial.map ι R.profile).coeff n := by
    intro n
    simpa [A, L, ι] using congrArg ι (R.coeff_profileHessian11 n)
  have h00eq :
      Polynomial.map ι R.profileHessian00 =
        binaryStaircaseProfileHessian00
          T.topFace.degree P.profileWeight (Polynomial.map ι R.profile) :=
    binaryStaircaseProfileHessian00_eq_of_coeff
      T.topFace.degree P.profileWeight
      (Polynomial.map ι R.profile) (Polynomial.map ι R.profileHessian00)
      h00coeff
  have h01eq :
      Polynomial.map ι R.profileHessian01 =
        binaryStaircaseProfileHessian01
          T.topFace.degree P.profileWeight (Polynomial.map ι R.profile) :=
    binaryStaircaseProfileHessian01_eq_of_coeff
      T.topFace.degree P.profileWeight
      (Polynomial.map ι R.profile) (Polynomial.map ι R.profileHessian01)
      h01coeff
  have h11eq :
      Polynomial.map ι R.profileHessian11 =
        binaryStaircaseProfileHessian11 (Polynomial.map ι R.profile) :=
    binaryStaircaseProfileHessian11_eq_of_coeff
      (Polynomial.map ι R.profile) (Polynomial.map ι R.profileHessian11)
      h11coeff
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul]
  rw [h00eq, h01eq, h11eq]
  exact binaryStaircaseProfileHessianDet_eq_residual
    T.topFace.degree P.profileWeight (Polynomial.map ι R.profile)

/-- **A19.R19 integral closing interface.**

The final binary Schur adapter no longer needs to mention the transverse
fraction field.  If it produces an integral symmetric binary Hessian block
whose three entries have the canonical staircase coefficients and whose
2-by-2 determinant vanishes, A19.R15 maps that equation injectively to the
fraction field and A19.119 immediately gives the contradiction. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_coeffwise_hessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (H00 H01 H11 : Polynomial (MvPolynomial (Fin 3) K))
    (h00 : ∀ n : ℕ,
      H00.coeff n =
        (((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K)) *
          ((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K) - 1)) *
          R.profile.coeff n)
    (h01 : ∀ n : ℕ,
      H01.coeff n =
        (n : MvPolynomial (Fin 3) K) *
          ((T.topFace.degree : MvPolynomial (Fin 3) K) -
            (P.profileWeight : MvPolynomial (Fin 3) K) *
              (n : MvPolynomial (Fin 3) K)) *
          R.profile.coeff n)
    (h11 : ∀ n : ℕ,
      H11.coeff n =
        (n : MvPolynomial (Fin 3) K) *
          ((n : MvPolynomial (Fin 3) K) - 1) *
          R.profile.coeff n)
    (hdet : H00 * H11 - H01 * H01 = 0) : False := by
  let H : QsOtherFacetContactFractionProfilePackage C P :=
    Classical.choice R.fractionProfilePackage
  have hres :
      binaryStaircaseProfileResidual T.topFace.degree P.profileWeight
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
          R.profile) = 0 :=
    binaryStaircaseProfileResidual_fraction_eq_zero_of_coeffwise_hessian
      T.topFace.degree P.profileWeight R.profile H00 H01 H11
      h00 h01 h11 hdet
  have hprofile :
      H.profile =
        Polynomial.map
          (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
          R.profile := by
    rw [H.profile_eq, qsContactFractionLongitudinalProfile, ← R.profile_eq]
  apply H.impossible_of_residual
  rw [hprofile]
  exact hres

/-- **R19 integral two-exposed-coefficient terminal contradiction.**

This is the minimal finite interface needed by R18.21.  Once active-pivot
cancellation has exposed zeros of the two integral profile-Hessian determinant
coefficients at `N+N` and `N+M`, localization carries those two equations
straight to the two stationary staircase residual coefficients.  No converse
parameter-layer extraction is required. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_two_profileHessianDet_coeffs
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hNNint : R.profileHessianDet.coeff (N + N) = 0)
    (hNMint : R.profileHessianDet.coeff (N + M) = 0) : False := by
  let A := MvPolynomial (Fin 3) K
  let L := qsContactProfileField K
  let ι : A →+* L := algebraMap A L
  have hι : Function.Injective ι := IsFractionRing.injective A L
  let H : QsOtherFacetContactFractionProfilePackage C P :=
    Classical.choice R.fractionProfilePackage
  have hprofile : H.profile = Polynomial.map ι R.profile := by
    dsimp [ι, A, L]
    rw [H.profile_eq, qsContactFractionLongitudinalProfile, ← R.profile_eq]
  have hmapDegree :
      (Polynomial.map ι R.profile).natDegree = R.profile.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hι R.profile
  have hdegree : H.profile.natDegree = R.profile.natDegree := by
    rw [hprofile]
    exact hmapDegree
  have hNfrac : N = H.profile.natDegree := by
    rw [hdegree]
    exact hN
  have hNtwo : 2 ≤ N := by
    rw [hNfrac]
    exact H.degree_two_le
  have hlead : H.profile.leadingCoeff = ι R.profile.leadingCoeff := by
    calc
      H.profile.leadingCoeff = H.profile.coeff H.profile.natDegree := by
        rw [Polynomial.coeff_natDegree]
      _ = H.profile.coeff R.profile.natDegree := by rw [hdegree]
      _ = (Polynomial.map ι R.profile).coeff R.profile.natDegree := by
        rw [hprofile]
      _ = ι (R.profile.coeff R.profile.natDegree) := by
        rw [Polynomial.coeff_map]
      _ = ι R.profile.leadingCoeff := by
        rw [Polynomial.coeff_natDegree]
  let Q : Polynomial A :=
    R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N
  have hMq : M = Q.natDegree := by
    simpa [Q] using hM
  have hmapC :
      Polynomial.map ι (Polynomial.C R.profile.leadingCoeff) =
        Polynomial.C (ι R.profile.leadingCoeff) := by
    simp
  have hmapX :
      Polynomial.map ι (Polynomial.X ^ N) = Polynomial.X ^ N := by
    simp
  have hsub :
      H.profile - Polynomial.C H.profile.leadingCoeff * Polynomial.X ^ N =
        Polynomial.map ι Q := by
    rw [hlead, hprofile]
    dsimp [Q]
    rw [Polynomial.map_sub, Polynomial.map_mul, hmapC, hmapX]
  have hmapQDegree : (Polynomial.map ι Q).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hι Q
  have hMfrac :
      M =
        (H.profile - Polynomial.C H.profile.leadingCoeff * Polynomial.X ^ N).natDegree := by
    rw [hsub]
    exact hMq.trans hmapQDegree.symm
  have hmapDet := R.fractionMap_profileHessianDet_eq_residual
  have hNNfrac :
      (binaryStaircaseProfileResidual
        T.topFace.degree P.profileWeight H.profile).coeff (N + N) = 0 := by
    rw [hprofile]
    rw [← hmapDet]
    rw [Polynomial.coeff_map, hNNint]
    simp
  have hNMfrac :
      (binaryStaircaseProfileResidual
        T.topFace.degree P.profileWeight H.profile).coeff (N + M) = 0 := by
    rw [hprofile]
    rw [← hmapDet]
    rw [Polynomial.coeff_map, hNMint]
    simp
  exact binaryStaircaseProfile_terminal_impossible_of_two_residual_coeffs
    (K := L)
    (D := T.topFace.degree) (r := P.profileWeight) (N := N) (M := M)
    (hr := P.profileWeight_two_le) (h := H.profile)
    (h0 := H.coeff_zero_ne) (hsupport := H.support_bound)
    (hN := hNfrac) (hNtwo := hNtwo) (hM := hMfrac)
    (hNN := hNNfrac) (hNM := hNMfrac)

/-- **R19 binary-layer adapter.**  Two zero exact parameter layers imply the
two integral coefficient equations and hence the finite contradiction above. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_two_binaryProfileHessianDetFamily_layers
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hNN :
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * T.topFace.degree - P.profileWeight * (N + N)) = 0)
    (hNM :
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * T.topFace.degree - P.profileWeight * (N + M)) = 0) : False := by
  have hNNint : R.profileHessianDet.coeff (N + N) = 0 :=
    R.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer (N + N) hNN
  have hNMint : R.profileHessianDet.coeff (N + M) = 0 :=
    R.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer (N + M) hNM
  exact R.impossible_of_two_profileHessianDet_coeffs
    N M hN hM hNNint hNMint

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation