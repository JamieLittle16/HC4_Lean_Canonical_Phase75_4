import HC4.Polynomial.RankThreeCubicDetOneWeightedRepair

/-!
# First lightweight bound for the actual source Hessian repair

The source determinant-one pole repair theorem has already been
Lean-verified in RankThreeCubicDetOneWeightedRepair. Here we isolate
only the source-derived weight bound on the transverse-transverse
repair block: its polynomial entries have transverse weight < 1.

The earlier version of this file included a large triple-derivative
and full existential assembly which repeatedly timed out during
elaboration. Those declarations have intentionally been withdrawn,
not claimed as verified. They will be rebuilt from small lemmas.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
noncomputable section

variable {K : Type*} [Field K]

private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual strictly lower cubic source remainder has a
transverse Hessian block with strict transverse weight below one.
No determinant assumption, independent correction, or new source
hypothesis is introduced. -/
theorem sourceCubic_repair_transverseEntry_strictWeightOne
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j : Fin 3) :
    IsWeightLT transverseCubicWeight 1
      (hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j)) := by
  have h :=
    (sub_initialForm_isWeightLT hcap).hessian_entry
      (.inr i) (.inr j)
  have hw :
      (3 : ℤ) - transverseCubicWeight (.inr i) -
        transverseCubicWeight (.inr j) = 1 := by
    simp [transverseCubicWeight]
  rw [hw] at h
  exact h

end
end HC4.Polynomial.RankThreeCubic
