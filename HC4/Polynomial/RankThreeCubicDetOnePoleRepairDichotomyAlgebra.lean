import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleCompatibility

/-!
# The lower-repair longitudinal escape: a four-row matrix lemma

For a vector w=(0,S) and a matrix correction C+D whose D
transverse-transverse block vanishes, nontrivial repair is possible
only if C acts nontrivially on w or the mixed longitudinal row
of D has nonzero pairing with S.

This distinction is important for the cubic pole: the strict
subquadratic source remainder can repair the longitudinal equation
but CANNOT repair the three transverse equations directly.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- In the 1+3 matrix decomposition, a correction with zero
transverse-transverse block acts on a purely transverse vector
only in the longitudinal row. Consequently every nonzero
(C+D)-repair comes from C or from that mixed row of D. -/
theorem zeroLongitudinalVector_repair_secondLayer_or_lowerMixed
    {R : Type*} [CommRing R]
    (C D : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (S : Fin 3 → R)
    (hDtrans : ∀ i j : Fin 3, D (.inr i) (.inr j) = 0)
    (hrepair :
      (C + D) *ᵥ (Sum.elim (fun _ : Unit => (0 : R)) S) ≠ 0) :
    C *ᵥ (Sum.elim (fun _ : Unit => (0 : R)) S) ≠ 0 ∨
      (∑ j : Fin 3, D (.inl ()) (.inr j) * S j) ≠ 0 := by
  classical
  let w : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) S
  change (C + D) *ᵥ w ≠ 0 at hrepair
  change C *ᵥ w ≠ 0 ∨
    (∑ j : Fin 3, D (.inl ()) (.inr j) * S j) ≠ 0
  by_cases hC : C *ᵥ w = 0
  · right
    intro hDmixed
    have hDtransRows (i : Fin 3) :
        (∑ j : Fin 3, D (.inr i) (.inr j) * S j) = 0 := by
      simp [hDtrans]
    have hDzero :
        D *ᵥ w = 0 :=
      fourHessian_zeroLongitudinalVector_of_rows
        D S hDmixed hDtransRows
    apply hrepair
    rw [Matrix.add_mulVec, hC, hDzero]
    simp
  · exact Or.inl hC

end
end HC4.Polynomial.RankThreeCubic
