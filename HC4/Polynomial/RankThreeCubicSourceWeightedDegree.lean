import HC4.Polynomial.RankThreeCubicSourceFractionKernel
import Mathlib.Tactic

/-!
# Source-honest transverse degrees and the pole-free cubic linearity bridge

The weight-three initial form has weight zero in x and weight one in the
three transverse variables. A longitudinal slice preserves this degree,
so the source transverse Hessian is homogeneous of degree one and the
mixed derivative is homogeneous of degree two.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section
variable {K : Type*} [Field K]

private abbrev Poly3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev Frac3 (K : Type*) [Field K] := FractionRing (Poly3 K)

private def natTransverseWeight : Unit ⊕ Fin 3 → ℕ :=
  Sum.elim (fun _ : Unit => 0) (fun _ : Fin 3 => 1)

/-- The selected longitudinal specialization sends a source monomial
of transverse weight n to a transverse homogeneous polynomial of
degree n. -/
private theorem referenceSlice_monomial_homogeneous
    (a : K) (d : Unit ⊕ Fin 3 →₀ ℕ) (c : K) :
    (referenceSlice a (monomial d c)).IsHomogeneous
      (Finsupp.weight natTransverseWeight d) := by
  classical
  let z : Unit ⊕ Fin 3 → Poly3 K :=
    Sum.elim (fun _ : Unit => MvPolynomial.C a) X
  have hz (i : Unit ⊕ Fin 3) :
      (z i).IsHomogeneous (natTransverseWeight i) := by
    cases i with
    | inl u =>
      cases u
      exact MvPolynomial.isHomogeneous_C _ _
    | inr j =>
      exact MvPolynomial.isHomogeneous_X _ _
  have hprod :
      (d.prod fun i k => z i ^ k).IsHomogeneous
        (∑ i ∈ d.support, natTransverseWeight i * d i) := by
    change (∏ i ∈ d.support, z i ^ d i).IsHomogeneous _
    apply MvPolynomial.IsHomogeneous.prod
      d.support (fun i => z i ^ d i)
      (fun i => natTransverseWeight i * d i)
    intro i hi
    exact (hz i).pow (d i)
  have hmono : (MvPolynomial.C c *
      (d.prod fun i k => z i ^ k)).IsHomogeneous
        (∑ i ∈ d.support, natTransverseWeight i * d i) := by
    simpa only [zero_add] using
      ((MvPolynomial.isHomogeneous_C (Fin 3) c).mul hprod)
  change (MvPolynomial.aeval z (monomial d c)).IsHomogeneous _
  rw [MvPolynomial.aeval_monomial]
  simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_comm]
    using hmono

/-- Evaluating the weight-zero longitudinal variable at a constant
preserves the degree of every transverse-weight-homogeneous source. -/
theorem referenceSlice_homogeneous_of_natWeight
    (a : K) (p : MvPolynomial (Unit ⊕ Fin 3) K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous natTransverseWeight n) :
    (referenceSlice a p).IsHomogeneous n := by
  classical
  rw [p.as_sum, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  have hw : Finsupp.weight natTransverseWeight d = n :=
    hp (MvPolynomial.mem_support_iff.mp hd)
  simpa only [hw] using referenceSlice_monomial_homogeneous a d (coeff d p)

/-- The integer transverse weight is the cast of the natural-number
weight of the same source monomial. -/
private theorem integer_weight_eq_nat_weight
    (d : Unit ⊕ Fin 3 →₀ ℕ) :
    Finsupp.weight transverseCubicWeight d =
      (Finsupp.weight natTransverseWeight d : ℤ) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases i with
  | inl u =>
    cases u
    simp [transverseCubicWeight, natTransverseWeight]
  | inr j =>
    simp [transverseCubicWeight, natTransverseWeight]

/-- Longitudinal specialization converts the original integer-weight
initial-form grading into ordinary transverse homogeneity. -/
theorem referenceSlice_homogeneous_of_transverseWeight
    (a : K) (p : MvPolynomial (Unit ⊕ Fin 3) K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    (referenceSlice a p).IsHomogeneous n := by
  apply referenceSlice_homogeneous_of_natWeight a p n
  intro d hd
  have h := hp hd
  rw [integer_weight_eq_nat_weight] at h
  exact_mod_cast h

/-- The cubic initial form automatically supplies the source Hessian
homogeneity required by the pole-free rational-to-linear theorem. -/
theorem sourceTransverseHessian_homogeneous
    (F : MvPolynomial (Unit ⊕ Fin 3) K) (a : K) (i j : Fin 3) :
    (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F) i j).IsHomogeneous 1 := by
  have hgrade := initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have hd := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous hgrade (.inr i)) (.inr j)
  have hone : (pderiv (.inr j)
      (pderiv (.inr i) (initialForm transverseCubicWeight 3 F))).IsWeightedHomogeneous
      transverseCubicWeight (1 : ℤ) := by
    convert hd using 1
  exact referenceSlice_homogeneous_of_transverseWeight a _ 1 hone

/-- The mixed longitudinal-transverse Hessian of the cubic initial
form is a quadratic homogeneous polynomial after specialization. -/
theorem sourceNegativeMixedHessian_homogeneous
    (F : MvPolynomial (Unit ⊕ Fin 3) K) (a : K) (i : Fin 3) :
    (sourceNegativeMixedHessian a
        (initialForm transverseCubicWeight 3 F) i).IsHomogeneous 2 := by
  have hgrade := initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have hd := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous hgrade (.inr i)) (.inl ())
  have htwo : (pderiv (.inl ())
      (pderiv (.inr i) (initialForm transverseCubicWeight 3 F))).IsWeightedHomogeneous
      transverseCubicWeight (2 : ℤ) := by
    convert hd using 1
  exact (referenceSlice_homogeneous_of_transverseWeight a _ 2 htwo).neg

/-- The source-generated characteristic has either a genuine pole or
an exactly linear transverse velocity. The pole-free implication is
derived from source data; there are no independent homogeneity or
Hessian-equation assumptions. -/
theorem exists_sourceCubic_poleFree_linear_velocity [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → Frac3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((∀ i : Fin 3, ∃ p : Poly3 K,
          algebraMap (Poly3 K) (Frac3 K) p = V (.inr i)) →
      ∃ N : Matrix (Fin 3) (Fin 3) K,
        ∀ i : Fin 3, V (.inr i) =
          algebraMap (Poly3 K) (Frac3 K)
            (∑ j : Fin 3, MvPolynomial.C (N i j) * X j)) := by
  obtain ⟨a, V, hreg, hlong, heq⟩ :=
    exists_sourceCubic_fractionHessianEquation F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, ?_⟩
  intro hpole
  exact exists_linear_matrix_of_poleFree_fractionKernel
    (g := algebraMap (Poly3 K) (Frac3 K))
    (hg := IsFractionRing.injective (Poly3 K) (Frac3 K))
    (H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F))
    (r := sourceNegativeMixedHessian a
      (initialForm transverseCubicWeight 3 F))
    (V := fun i => V (.inr i))
    (fun i j => sourceTransverseHessian_homogeneous F a i j)
    (fun i => sourceNegativeMixedHessian_homogeneous F a i)
    hreg heq hpole

end
end HC4.Polynomial.RankThreeCubic
