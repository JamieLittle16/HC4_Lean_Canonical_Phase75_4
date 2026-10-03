import HC4.RationalRigidity.RankThreeAffineTwoFixedImpossible
import Mathlib.Tactic

/-!
# A18.5.73a.2: two fixed affine directions via scalar equalities

This adapter keeps the full three-slope terminal certificate unchanged and
accepts the two fixed-direction facts as scalar equalities.  The substitutions
are performed only in the small RationalRigidity context, avoiding dependent
normalisation of the much larger Newton first-contact presentation.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A genuine affine terminal whose last two slopes are equal to zero is
impossible when the remaining slope is neither zero nor `-1`. -/
theorem rankThree_terminal_two_fixed_impossible_of_eq
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hR : R = 0)
    (hS : S = 0)
    (hQ : Q ≠ 0)
    (hQone : Q + 1 ≠ 0) :
    False := by
  subst R
  subst S
  exact rankThree_terminal_two_fixed_impossible
    hA hB hC hP hphiDeg hphi0 hcert hQ hQone

end

end HC4.RationalRigidity
