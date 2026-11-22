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

/-- Every monomial has nonnegative transverse weight, since the
longitudinal source variable has weight zero and the transverse
variables have weight one. -/
theorem transverseCubicWeight_nonnegative
    (d : (Unit ⊕ Fin 3) →₀ ℕ) :
    0 ≤ Finsupp.weight transverseCubicWeight d := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro i hi
  cases i with
  | inl u =>
      cases u
      simp [transverseCubicWeight]
  | inr j =>
      simp [transverseCubicWeight]

/-- A source polynomial supported in strictly negative transverse
weights must be zero. This only uses the actual monomial support. -/
theorem transverseCubicWeight_lt_zero_eq_zero
    (P : SB K)
    (hP : IsWeightLT transverseCubicWeight 0 P) :
    P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  have hcoeff : coeff d P = 0 := by
    by_contra hn
    have hd : d ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr hn
    have hlt := hP hd
    exact (not_lt_of_ge (transverseCubicWeight_nonnegative d)) hlt
  simpa using hcoeff

/-- A transverse derivative of any source polynomial of transverse
weight strictly below one is identically zero. This is the
small generic lemma needed to control the genuine Hessian repair. -/
theorem transverseCubicWeight_pderiv_eq_zero_of_lt_one
    (P : SB K) (hP : IsWeightLT transverseCubicWeight 1 P)
    (k : Fin 3) :
    pderiv (.inr k) P = 0 := by
  have hder := hP.pderiv (.inr k)
  have hw : (1 : ℤ) - transverseCubicWeight (.inr k) = 0 := by
    simp [transverseCubicWeight]
  rw [hw] at hder
  exact transverseCubicWeight_lt_zero_eq_zero _ hder

/-- The strictly lower source remainder has no third
transverse derivative, stated directly for its transverse
Hessian entry. -/
theorem sourceCubic_repair_transverseEntry_pderiv_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j k : Fin 3) :
    pderiv (.inr k)
        (hessian (F - initialForm transverseCubicWeight 3 F)
          (.inr i) (.inr j)) = 0 := by
  exact transverseCubicWeight_pderiv_eq_zero_of_lt_one _
    (sourceCubic_repair_transverseEntry_strictWeightOne F hcap i j) k

end
end HC4.Polynomial.RankThreeCubic
