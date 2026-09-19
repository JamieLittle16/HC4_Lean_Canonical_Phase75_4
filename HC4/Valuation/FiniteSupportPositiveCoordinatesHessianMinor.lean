import HC4.Newton.FiniteSupportExposedVertex
import HC4.Polynomial.MonomialHessianPrincipalMinor
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# Positive support coordinates force a nonzero Hessian principal minor

For a finite nonzero four-variable polynomial, suppose two distinct source
coordinates occur with positive exponent in every supported monomial.
Successively maximize all four coordinates. The final exact initial form is
one nonzero monomial and still has both selected coordinates positive, so its
principal Hessian minor is nonzero in characteristic zero. Exact
initial-form covariance then lifts that nonvanishing back to the source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem hessianPrincipalMinor_ne_zero_of_support_two_positive
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    {i j : Fin 4}
    (hij : i ≠ j)
    (hi : ∀ d ∈ F.support, 0 < d i)
    (hj : ∀ d ∈ F.support, 0 < d j) :
    hessianPrincipalMinor F i j ≠ 0 := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  let d := D3.witness
  let c := MvPolynomial.coeff d D3.face

  have hd2 : d ∈ D2.face.support := D3.witness_mem
  have hd1 : d ∈ D1.face.support := D2.support_subset hd2
  have hd0 : d ∈ D0.face.support := D1.support_subset hd1
  have hdF : d ∈ F.support := D0.support_subset hd0

  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp D3.witness_mem

  have hunique : ∀ q ∈ D3.face.support, q = d := by
    intro q hq
    have hq2 : q ∈ D2.face.support := D3.support_subset hq
    have hq1 : q ∈ D1.face.support := D2.support_subset hq2
    have hq0 : q ∈ D0.face.support := D1.support_subset hq1
    apply Finsupp.ext
    intro k
    fin_cases k
    · simpa using
        (D0.coordinate_eq q hq0).trans (D0.coordinate_eq d hd0).symm
    · simpa using
        (D1.coordinate_eq q hq1).trans (D1.coordinate_eq d hd1).symm
    · simpa using
        (D2.coordinate_eq q hq2).trans (D2.coordinate_eq d hd2).symm
    · simpa using
        (D3.coordinate_eq q hq).trans
          (D3.coordinate_eq d D3.witness_mem).symm

  have hmono : D3.face = MvPolynomial.monomial d c := by
    apply MvPolynomial.ext
    intro q
    by_cases hqd : q = d
    · subst q
      simp [c]
    · have hq0 : MvPolynomial.coeff q D3.face = 0 := by
        by_contra hne
        exact hqd (hunique q (MvPolynomial.mem_support_iff.mpr hne))
      have hdq : d ≠ q := by
        intro hdq
        exact hqd hdq.symm
      rw [hq0]
      simp [hdq]

  have hminor3 : hessianPrincipalMinor D3.face i j ≠ 0 := by
    rw [hmono]
    exact hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      hc hij (hi d hdF) (hj d hdF)

  have hminor2 : hessianPrincipalMinor D2.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D3.weight_bound i j
    simpa [D3.face_eq] using hminor3

  have hminor1 : hessianPrincipalMinor D1.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D2.weight_bound i j
    simpa [D2.face_eq] using hminor2

  have hminor0 : hessianPrincipalMinor D0.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D1.weight_bound i j
    simpa [D1.face_eq] using hminor1

  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    D0.weight_bound i j
  simpa [D0.face_eq] using hminor0

end

end HC4.Valuation
