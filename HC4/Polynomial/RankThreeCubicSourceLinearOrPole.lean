import HC4.Polynomial.RankThreeCubicSourceDegrees
import Mathlib.Tactic

/-!
# Source-level linear-or-pole dichotomy for full-rank cubic characteristics

All the matrix data, homogeneity, and determinant nonvanishing are
now generated from the actual cubic source. Either its normalized
rational characteristic has polynomial coordinates, which necessarily
form a constant matrix times the transverse variables, or at least
one rational coordinate is not represented by a polynomial.

The second branch is an exact non-polynomial witness, not yet a
denominator-prime or a terminal HC4 contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B' (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev Frac' (K : Type*) [Field K] := FractionRing (B' K)

/-- An actual cubic cap-three constant-determinant source with full
transverse Hessian rank has a regular normalized rational characteristic
which is either a constant linear velocity or contains a truly
non-polynomial fraction-field coordinate.

No pole-free or linearity assumption is included in the source
hypotheses: the dichotomy follows from polynomial fraction
representability and the previously proved Euler rigidity. -/
theorem exists_sourceCubic_linearVelocity_or_nonPolynomial
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans :
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → Frac' K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (sourceTransverseHessian a L).map
          (algebraMap (B' K) (Frac' K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          (algebraMap (B' K) (Frac' K))
            (sourceNegativeMixedHessian a L i) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              (algebraMap (B' K) (Frac' K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ i : Fin 3, ∀ p : B' K,
            (algebraMap (B' K) (Frac' K)) p ≠ V (.inr i))) := by
  classical
  obtain ⟨a, V, hregular, hV, hkernel⟩ :=
    exists_sourceCubic_fractionHessianEquation F hcap hdet htrans
  refine ⟨a, V, hregular, hV, hkernel, ?_⟩
  let g : B' K →+* Frac' K := algebraMap (B' K) (Frac' K)
  have hg : Function.Injective g :=
    IsFractionRing.injective (B' K) (Frac' K)
  have hH : ∀ i j,
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F) i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F
  have hr : ∀ i,
      (sourceNegativeMixedHessian a
        (initialForm transverseCubicWeight 3 F) i).IsHomogeneous 2 :=
    sourceCubic_negativeMixedHessian_homogeneous_two a F
  by_cases hpoly :
      ∀ i : Fin 3, ∃ p : B' K, g p = V (.inr i)
  · left
    obtain ⟨N, hN⟩ :=
      exists_linear_matrix_of_poleFree_fractionKernel g hg
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F))
        (sourceNegativeMixedHessian a
          (initialForm transverseCubicWeight 3 F))
        (fun i : Fin 3 => V (.inr i))
        hH hr hregular hkernel hpoly
    exact ⟨N, hN⟩
  · right
    push_neg at hpoly
    exact hpoly

end
end HC4.Polynomial.RankThreeCubic
