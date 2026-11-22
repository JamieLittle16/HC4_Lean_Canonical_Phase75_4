import HC4.Polynomial.RankThreeCubicDetOnePrincipalSourceChart
import Mathlib.Tactic

/-!
# Exact principal-block cofactor and Schur diagonal in the source chart

For a symmetric 4x4 matrix indexed by Unit ⊕ Fin3, put the two
transverse coordinates other than k first, longitudinal next, and
the transverse k coordinate last.

In the reindexed GeneralFourBlock:
  activeDet = adj(T)[k,k]
  schurC = det(T)
where T is the ORIGINAL transverse 3x3 block.

The second equality is a denominator-cleared principal 3x3
determinant identity: no division or choice of inverse is used.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

theorem principalSourceFourBlock_activeDet_and_schurC
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (hB : B.IsSymm) (k : Fin 3) :
    let T : Matrix (Fin 3) (Fin 3) K :=
      B.submatrix Sum.inr Sum.inr
    (principalSourceFourBlock B k).activeDet = T.adjugate k k ∧
      (principalSourceFourBlock B k).schurC = T.det := by
  classical
  let T : Matrix (Fin 3) (Fin 3) K :=
    B.submatrix Sum.inr Sum.inr
  have h01 :
      B (.inr (1 : Fin 3)) (.inr (0 : Fin 3)) =
      B (.inr (0 : Fin 3)) (.inr (1 : Fin 3)) :=
    (hB.apply _ _).symm
  have h02 :
      B (.inr (2 : Fin 3)) (.inr (0 : Fin 3)) =
      B (.inr (0 : Fin 3)) (.inr (2 : Fin 3)) :=
    (hB.apply _ _).symm
  have h12 :
      B (.inr (2 : Fin 3)) (.inr (1 : Fin 3)) =
      B (.inr (1 : Fin 3)) (.inr (2 : Fin 3)) :=
    (hB.apply _ _).symm
  fin_cases k <;>
    simp [T, principalSourceFourBlock, principalSourceFourMatrix,
      principalSourceFourOrder, GeneralFourBlock.ofSymmetricMatrix,
      GeneralFourBlock.activeDet, GeneralFourBlock.schurC,
      Matrix.adjugate_fin_three, Matrix.det_fin_three,
      h01, h02, h12, Fin.succAbove] <;>
    ring

end
end HC4.Polynomial.RankThreeCubic
