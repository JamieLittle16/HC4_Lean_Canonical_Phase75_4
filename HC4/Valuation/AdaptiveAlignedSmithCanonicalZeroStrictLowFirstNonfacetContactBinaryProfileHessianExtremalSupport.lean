import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDegreeBound
import Mathlib.Tactic

/-!
# A19.R18.21: extremal support of the binary profile Hessian

The finite staircase contradiction only uses the highest longitudinal profile
index `N` and the next-highest index `M`.  The exact binary homogenisation
reverses this longitudinal ordering into parameter ordering:

    qNN = 2D - r(2N)
    qNM = 2D - r(N+M).

A19.R18 already identifies every longitudinal coefficient of the whole binary
profile-Hessian determinant with one single parameter monomial.  The previous
support module shows that nothing occurs below `qNN`.  Here we prove the
second triangular fact: if `M` is the degree left after removing the leading
`N` monomial, then no profile-Hessian determinant coefficient occurs in
longitudinal degrees strictly between `N+M` and `2N`; equivalently there is no
binary parameter support strictly between `qNN` and `qNM`.

This is pure finite-support bookkeeping.  No Schur identity, active-pivot
cancellation, localization, or terminal geometry is used.
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

private theorem QsOtherFacetContactRawLongitudinalProfilePackage.coeff_index_le_nextHighest
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    {k : ℕ}
    (hk : R.profile.coeff k ≠ 0)
    (hkN : k < N) :
    k ≤ M := by
  let Q : Polynomial (MvPolynomial (Fin 3) K) :=
    R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N
  have hQcoeff : Q.coeff k = R.profile.coeff k := by
    dsimp [Q]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hkne : k ≠ N := Nat.ne_of_lt hkN
    simp [Polynomial.coeff_X_pow, hkne]
  have hQne : Q.coeff k ≠ 0 := by
    rw [hQcoeff]
    exact hk
  have hle := Polynomial.le_natDegree_of_ne_zero hQne
  have hMQ : M = Q.natDegree := by simpa [Q] using hM
  rw [← hMQ] at hle
  exact hle

private theorem QsOtherFacetContactRawLongitudinalProfilePackage.profile_pair_zero_of_nextHighest_gap
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M n i j : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hMN : M < N)
    (hnlo : N + M < n)
    (hnhi : n < N + N)
    (hsum : i + j = n) :
    R.profile.coeff i = 0 ∨ R.profile.coeff j = 0 := by
  by_contra hnot
  push_neg at hnot
  rcases hnot with ⟨hi, hj⟩
  have hiLe : i ≤ N := by
    rw [hN]
    exact Polynomial.le_natDegree_of_ne_zero hi
  have hjLe : j ≤ N := by
    rw [hN]
    exact Polynomial.le_natDegree_of_ne_zero hj
  have hiBound : i = N ∨ i ≤ M := by
    by_cases hiN : i = N
    · exact Or.inl hiN
    · exact Or.inr (R.coeff_index_le_nextHighest N M hN hM hi (by omega))
  have hjBound : j = N ∨ j ≤ M := by
    by_cases hjN : j = N
    · exact Or.inl hjN
    · exact Or.inr (R.coeff_index_le_nextHighest N M hN hM hj (by omega))
  rcases hiBound with rfl | hiM <;> rcases hjBound with rfl | hjM <;> omega

/-- No coefficient of the integral profile-Hessian determinant can occur
strictly between the exposed degrees `N+M` and `2N`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet_coeff_eq_zero_of_nextHighest_gap
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M n : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hMN : M < N)
    (hnlo : N + M < n)
    (hnhi : n < N + N) :
    R.profileHessianDet.coeff n = 0 := by
  rw [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet,
    Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_mul]
  have h0011 :
      ∑ ij ∈ Finset.antidiagonal n,
          R.profileHessian00.coeff ij.1 * R.profileHessian11.coeff ij.2 = 0 := by
    apply Finset.sum_eq_zero
    intro ij hij
    rcases R.profile_pair_zero_of_nextHighest_gap
        N M n ij.1 ij.2 hN hM hMN hnlo hnhi
        (Finset.mem_antidiagonal.mp hij) with hi | hj
    · rw [R.coeff_profileHessian00, hi]
      simp
    · rw [R.coeff_profileHessian11, hj]
      simp
  have h0101 :
      ∑ ij ∈ Finset.antidiagonal n,
          R.profileHessian01.coeff ij.1 * R.profileHessian01.coeff ij.2 = 0 := by
    apply Finset.sum_eq_zero
    intro ij hij
    rcases R.profile_pair_zero_of_nextHighest_gap
        N M n ij.1 ij.2 hN hM hMN hnlo hnhi
        (Finset.mem_antidiagonal.mp hij) with hi | hj
    · rw [R.coeff_profileHessian01, hi]
      simp
    · rw [R.coeff_profileHessian01, hj]
      simp
  rw [h0011, h0101]
  rfl

/-- **R18.21 second exposed parameter order.**  There is no parameter support
of the whole binary profile-Hessian determinant strictly between `qNN` and
`qNM`.  Thus after the `qNN` coefficient has been killed, constant-pivot
triangular cancellation may be applied once more at `qNM` without any
all-depth product clock. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessianDetFamily_parameterLayer_eq_zero_between_qNN_qNM
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (N M : ℕ)
    (hN : N = R.profile.natDegree)
    (hM : M =
      (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hMN : M < N)
    {q : ℕ}
    (hqlo :
      2 * T.topFace.degree - P.profileWeight * (N + N) < q)
    (hqhi :
      q < 2 * T.topFace.degree - P.profileWeight * (N + M)) :
    familyParameterLayer P.binaryProfileHessianDetFamily q = 0 := by
  have hNbound : N * P.profileWeight ≤ T.topFace.degree := by
    rw [hN]
    exact R.support_bound
  have hMNle : M ≤ N := Nat.le_of_lt hMN
  have hNNbound :
      P.profileWeight * (N + N) ≤ 2 * T.topFace.degree := by
    rw [Nat.mul_add]
    omega
  have hNMbound :
      P.profileWeight * (N + M) ≤ 2 * T.topFace.degree := by
    rw [Nat.mul_add]
    omega
  apply (MvPolynomial.finSuccEquiv K 3).injective
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  rw [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  have hlong := R.binaryProfileHessianDetFamily_longitudinal_coeff n
  have hm := congrArg
    (fun A : MvPolynomial (Fin 3) (Polynomial K) => MvPolynomial.coeff m A)
    hlong
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hm
  rw [hm]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  by_cases hnLow : n ≤ N + M
  · have horder :
        2 * T.topFace.degree - P.profileWeight * (N + M) ≤
          2 * T.topFace.degree - P.profileWeight * n := by
      omega
    have hqorder : q < 2 * T.topFace.degree - P.profileWeight * n :=
      lt_of_lt_of_le hqhi horder
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hqorder]
  · have hnlo : N + M < n := Nat.lt_of_not_ge hnLow
    by_cases hnHigh : n < N + N
    · have hdet := R.profileHessianDet_coeff_eq_zero_of_nextHighest_gap
        N M n hN hM hMN hnlo hnHigh
      rw [hdet]
      simp
    · have hNNle : N + N ≤ n := Nat.le_of_not_gt hnHigh
      by_cases hnEq : n = N + N
      · subst n
        rw [Polynomial.coeff_X_pow_mul']
        have hqNN :
            2 * T.topFace.degree - P.profileWeight * (N + N) < q := hqlo
        have hle :
            2 * T.topFace.degree - P.profileWeight * (N + N) ≤ q :=
          Nat.le_of_lt hqNN
        have hpos :
            0 < q -
              (2 * T.topFace.degree - P.profileWeight * (N + N)) :=
          Nat.sub_pos_of_lt hqNN
        simp [hle, Nat.ne_of_gt hpos]
      · have hnAbove : N + N < n := by omega
        have hdet : R.profileHessianDet.coeff n = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt R.profileHessianDet_natDegree_le_two_profile
              (by simpa [hN] using hnAbove))
        rw [hdet]
        simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
