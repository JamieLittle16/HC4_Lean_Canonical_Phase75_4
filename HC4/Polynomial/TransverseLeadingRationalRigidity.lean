import HC4.Polynomial.RationalCharacteristicRankTwoClosure
import HC4.Polynomial.TransverseLeadingCharacteristics

/-!
# Rational rigidity of the actual leading transverse layer

The complete anchored rigidity theorem is consumed at the original
source's top transverse grade, for arbitrary cap m >= 2. A nonzero
transverse principal determinant supplies its own regular anchor.
No collision extraction or global weighted closure is asserted here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- Eliminate the existential anchor from rational rigidity when the
original singular Hessian has a nonzero transverse principal minor. -/
theorem rationalCharacteristic_adjugate_annihilator_of_transverseDet_ne_zero
    (L : S K) (hdet : (hessian L).det = 0)
    (htrans : ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  exact rationalCharacteristic_anchored_adjugate_annihilator a L hdet ha

/-- The true leading layer of every constant-Hessian source of
transverse cap at least two has a constant adjugate annihilator
whenever its transverse principal determinant is nonzero.
No auxiliary rational-characteristic rigidity hypothesis remains. -/
theorem transverseLeading_adjugate_annihilator
    (F : S K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight m F)).submatrix
      Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight m F
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  exact rationalCharacteristic_adjugate_annihilator_of_transverseDet_ne_zero
    (initialForm transverseCubicWeight m F)
    (transverseLeading_hessian_det_eq_zero F m hm hcap hdet) htrans

end
end HC4.Polynomial.RankThreeCubic

#print axioms HC4.Polynomial.RankThreeCubic.rationalCharacteristic_anchored_adjugate_annihilator
#print axioms HC4.Polynomial.RankThreeCubic.transverseLeading_adjugate_annihilator
