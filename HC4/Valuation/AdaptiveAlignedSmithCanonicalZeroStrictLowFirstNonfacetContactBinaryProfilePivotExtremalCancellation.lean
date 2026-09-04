import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfilePivotContradiction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianExtremalSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalSlices
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfileRigidity
import Mathlib.Tactic

/-!
# A19.R18.21: two-step active-pivot cancellation

The historical R18 consumer asks for an active-pivot product clock at every
parameter order below Hessian closure.  The finite staircase never needs that
much information.  If `N` is the highest longitudinal profile index and `M`
is the next-highest one, only

    qNN = 2D - r(2N),
    qNM = 2D - r(N+M)

are used.

The extremal-support module proves there is no profile-Hessian determinant
support below `qNN` or strictly between `qNN` and `qNM`.  Therefore the generic
constant-pivot convolution lemma may be applied exactly twice.  This file
packages that two-step cancellation without division and without introducing
an all-depth product clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18.21 exact two-step triangular cancellation.**

For any parameter-first pivot with nonzero constant coefficient, vanishing of
its product with the binary profile determinant at just `qNN` and `qNM`
forces those two binary profile-determinant layers themselves to vanish. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.two_exposed_layers_eq_zero_of_profilePivotProduct
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (A : Polynomial (MvPolynomial (Fin 4) K))
    (hA0 : A.coeff 0 ≠ 0)
    (N M : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hMN : M < N)
    (hprodNN :
      (A * parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff
        (2 * T.topFace.degree - P.profileWeight * (N + N)) = 0)
    (hprodNM :
      (A * parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff
        (2 * T.topFace.degree - P.profileWeight * (N + M)) = 0) :
    familyParameterLayer P.binaryProfileHessianDetFamily
          (2 * T.topFace.degree - P.profileWeight * (N + N)) = 0 ∧
      familyParameterLayer P.binaryProfileHessianDetFamily
          (2 * T.topFace.degree - P.profileWeight * (N + M)) = 0 := by
  let B : Polynomial (MvPolynomial (Fin 4) K) :=
    parameterFirstEquiv K P.binaryProfileHessianDetFamily
  let qNN : ℕ :=
    2 * T.topFace.degree - P.profileWeight * (N + N)
  let qNM : ℕ :=
    2 * T.topFace.degree - P.profileWeight * (N + M)

  have hNbound : N * P.profileWeight ≤ T.topFace.degree := by
    rw [hN]
    exact R.support_bound
  have hweightPos : 0 < P.profileWeight := by omega
  have hqNNltqNM : qNN < qNM := by
    dsimp [qNN, qNM]
    have hNNbound :
        P.profileWeight * (N + N) ≤ 2 * T.topFace.degree := by
      rw [Nat.mul_add]
      omega
    have hNMbound :
        P.profileWeight * (N + M) ≤ 2 * T.topFace.degree := by
      rw [Nat.mul_add]
      have hMNle : M ≤ N := Nat.le_of_lt hMN
      omega
    omega

  have hbelowNN : ∀ k : ℕ, k < qNN → B.coeff k = 0 := by
    intro k hk
    dsimp [B]
    rw [parameterFirstEquiv_coeff]
    exact R.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_lt_qNN
      (by simpa [qNN, hN] using hk)

  have hBNN : B.coeff qNN = 0 := by
    apply polynomial_coeff_eq_zero_of_constant_pivot A B hA0
    · simpa [B, qNN] using hprodNN
    · exact hbelowNN

  have hbelowNM : ∀ k : ℕ, k < qNM → B.coeff k = 0 := by
    intro k hk
    by_cases hkNN : k < qNN
    · exact hbelowNN k hkNN
    by_cases hkEq : k = qNN
    · subst k
      exact hBNN
    have hkAbove : qNN < k := by omega
    dsimp [B]
    rw [parameterFirstEquiv_coeff]
    exact R.binaryProfileHessianDetFamily_parameterLayer_eq_zero_between_qNN_qNM
      N M hN hM hMN
      (by simpa [qNN] using hkAbove)
      (by simpa [qNM] using hk)

  have hBNM : B.coeff qNM = 0 := by
    apply polynomial_coeff_eq_zero_of_constant_pivot A B hA0
    · simpa [B, qNM] using hprodNM
    · exact hbelowNM

  constructor
  · have h := hBNN
    dsimp [B] at h
    rw [parameterFirstEquiv_coeff] at h
    simpa [qNN] using h
  · have h := hBNM
    dsimp [B] at h
    rw [parameterFirstEquiv_coeff] at h
    simpa [qNM] using h

/-- **R18.24 finite `.pr` terminal consumer.**

Once the actual PR contact calculation kills the active-pivot/profile product
at the two exposed orders selected by `prExtremalDegreeData`, no further clock
or recurrence is required: two-step triangular cancellation exposes the two
binary profile-Hessian layers, and R19's finite staircase theorem gives the
contradiction.  This theorem is intentionally the last adapter before the
hard contact coefficient calculation. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.pr_impossible_of_two_exposed_profilePivotProduct_coeffs
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hprodNN :
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff
          (2 * T.topFace.degree -
            P.profileWeight * (E.next.N + E.next.N))) = 0)
    (hprodNM :
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff
          (2 * T.topFace.degree -
            P.profileWeight * (E.next.N + E.next.M))) = 0) : False := by
  let A : Polynomial (MvPolynomial (Fin 4) K) :=
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.contactFamily).activeDet
  have hA0 : A.coeff 0 ≠ 0 := by
    dsimp [A]
    exact P.pr_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  have hlayers :=
    R.two_exposed_layers_eq_zero_of_profilePivotProduct
      A hA0 E.next.N E.next.M E.next.N_eq E.next.M_eq E.next.M_lt_N
      (by simpa [A] using hprodNN)
      (by simpa [A] using hprodNM)
  exact R.impossible_of_two_binaryProfileHessianDetFamily_layers
    E.next.N E.next.M E.next.N_eq E.next.M_eq hlayers.1 hlayers.2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
