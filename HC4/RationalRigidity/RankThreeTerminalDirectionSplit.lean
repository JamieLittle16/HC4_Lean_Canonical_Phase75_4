import HC4.RationalRigidity.RankThreeHighestDirectionRelation
import Mathlib.Tactic

/-!
# A18.5.42: finite direction split at a rank-three terminal

A18.5.41 reduces the highest autonomous coefficient to

    (D-1) Q R S (1+Q+R+S) = 0.

Over a characteristic-zero field this has the exact geometric interpretation
wanted by the endpoint assembly:

* `D = 1`: the coefficient polynomial is genuinely two-term;
* `Q = 0`, `R = 0`, or `S = 0`: one transverse exponent is unchanged along
  the affine edge;
* `1+Q+R+S = 0`: the affine direction has ordinary degree zero.

No further scalar analysis is hidden in this file.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Finite rank-three terminal direction split.** -/
theorem rankThree_terminal_degreeOne_or_directionDegenerate
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    phi.natDegree = 1 ∨ Q = 0 ∨ R = 0 ∨ S = 0 ∨
      1 + Q + R + S = 0 := by
  have h := rankThree_terminal_highest_direction_relation
    hA hB hC hP hphiDeg hphi0 hcert
  rcases mul_eq_zero.mp h with hD | hrest
  · left
    have hcast : (phi.natDegree : K) = 1 := sub_eq_zero.mp hD
    exact_mod_cast hcast
  · right
    rcases mul_eq_zero.mp hrest with hQ | hrest
    · exact Or.inl hQ
    · rcases mul_eq_zero.mp hrest with hR | hrest
      · exact Or.inr (Or.inl hR)
      · rcases mul_eq_zero.mp hrest with hS | hsum
        · exact Or.inr (Or.inr (Or.inl hS))
        · exact Or.inr (Or.inr (Or.inr hsum))

end

end HC4.RationalRigidity
