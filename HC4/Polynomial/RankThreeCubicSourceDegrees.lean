import HC4.Polynomial.RankThreeCubicSourceFractionKernel
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Cubic transverse source weights survive longitudinal specialization

The three transverse variables have weight one and the longitudinal
variable has weight zero. After the longitudinal variable is specialized
to a constant, integer weighted-homogeneous source components become
ordinary homogeneous polynomials. This supplies the last graded input
to the pole-free rational velocity linearity theorem.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial Finsupp
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev CubicS (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K
private abbrev CubicB' (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- The natural-number version of the transverse cubic source weight. -/
def transverseCubicNatWeight : Unit ⊕ Fin 3 → ℕ :=
  Sum.elim (fun _ : Unit => 0) (fun _ : Fin 3 => 1)

/-- Integer and natural transverse weights coincide after casting. -/
private theorem transverseCubicNatWeight_cast (d : (Unit ⊕ Fin 3) →₀ ℕ) :
    ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) =
      Finsupp.weight transverseCubicWeight d := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases i with
  | inl u =>
    cases u
    simp [transverseCubicNatWeight, transverseCubicWeight]
  | inr j =>
    simp [transverseCubicNatWeight, transverseCubicWeight, nsmul_eq_mul]

/-- Convert the source's integer weight condition to the corresponding
natural-number weight, permitting Mathlib's weighted Euler theorem. -/
private theorem source_weightedNat_of_weightedInt (p : CubicS K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    p.IsWeightedHomogeneous transverseCubicNatWeight n := by
  intro d hd
  have h : ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) = (n : ℤ) := by
    rw [transverseCubicNatWeight_cast]
    exact hp hd
  exact_mod_cast h

/-- Weighted homogeneity of the source descends to ordinary transverse
homogeneity after longitudinal specialization. -/
theorem referenceSlice_isHomogeneous_of_transverseWeight
    (a : K) (p : CubicS K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    (referenceSlice a p).IsHomogeneous n := by
  classical
  have hpNat := source_weightedNat_of_weightedInt p n hp
  have he := hpNat.sum_weight_X_mul_pderiv
  have hsum :
      (∑ j : Fin 3, (X (.inr j) : CubicS K) *
        pderiv (.inr j) p) = n • p := by
    simpa [transverseCubicNatWeight, Fintype.sum_sum_type] using he
  have hspec := congrArg (referenceSlice a) hsum
  have hX (j : Fin 3) :
      referenceSlice a (X (.inr j) : CubicS K) = (X j : CubicB' K) := by
    simp [referenceSlice]
  have hDeriv (j : Fin 3) :
      referenceSlice a (pderiv (.inr j) p) =
        pderiv j (referenceSlice a p) :=
    (referenceSlice_pderiv a j p).symm
  have hEuler : transverseEuler (referenceSlice a p) =
      n • referenceSlice a p := by
    simpa only [map_sum, map_mul, map_nsmul, hX, hDeriv,
      transverseEuler] using hspec
  exact isHomogeneous_of_transverseEuler_eq_nsmul (referenceSlice a p) n hEuler

/-- Entries of the transverse Hessian of the actual cubic initial form
are homogeneous of degree one after any longitudinal specialization. -/
theorem sourceCubic_transverseHessian_homogeneous_one
    (a : K) (F : CubicS K) :
    ∀ i j : Fin 3,
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F) i j).IsHomogeneous 1 := by
  intro i j
  let L := initialForm transverseCubicWeight 3 F
  have hL : L.IsWeightedHomogeneous transverseCubicWeight 3 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have h1 : (pderiv (.inr j) (pderiv (.inr i) L)).
      IsWeightedHomogeneous transverseCubicWeight (1 : ℤ) := by
    have h := pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL (.inr i)) (.inr j)
    simpa [transverseCubicWeight] using h
  exact referenceSlice_isHomogeneous_of_transverseWeight a _ 1 h1

/-- The negative longitudinal/transverse mixed Hessian row has
ordinary transverse degree two, even though the cubic source's
coefficients may depend polynomially on the longitudinal variable. -/
theorem sourceCubic_negativeMixedHessian_homogeneous_two
    (a : K) (F : CubicS K) :
    ∀ i : Fin 3,
      (sourceNegativeMixedHessian a
        (initialForm transverseCubicWeight 3 F) i).IsHomogeneous 2 := by
  intro i
  let L := initialForm transverseCubicWeight 3 F
  have hL : L.IsWeightedHomogeneous transverseCubicWeight 3 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have h2 : (pderiv (.inl ()) (pderiv (.inr i) L)).
      IsWeightedHomogeneous transverseCubicWeight (2 : ℤ) := by
    have h := pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL (.inr i)) (.inl ())
    simpa [transverseCubicWeight] using h
  exact (referenceSlice_isHomogeneous_of_transverseWeight a _ 2 h2).neg

end
end HC4.Polynomial.RankThreeCubic
