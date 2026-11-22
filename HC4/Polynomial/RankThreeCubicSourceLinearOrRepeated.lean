import HC4.Polynomial.RankThreeCubicSquarefreePoleFinal
import HC4.Polynomial.RankThreeCubicSourceSingularTrichotomy
import Mathlib.Tactic

/-!
# Full-rank cubic source: linear characteristic or repeated linear factor

The source-derived squarefree pole contradiction removes the third
alternative from the earlier cubic source trichotomy. The remaining
repeated-factor alternative is not yet shown impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Under the actual constant-Hessian-determinant cubic source
hypotheses, the rational characteristic is constant-linear in the
transverse variables, or the transverse determinant has a repeated
irreducible degree-one factor. Neither alternative assumes a
separately supplied closure certificate. -/
theorem exists_sourceCubic_linear_or_repeatedLinear
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → F3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V (pderiv i L) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (F3 K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ p : B3 K, Irreducible p ∧
            p * p ∣ (sourceTransverseHessian a L).det ∧
            p.totalDegree = 1)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  obtain ⟨V, hV, hgrad⟩ :=
    exists_transverseCubic_characteristic_at a F hcap hdet ha
  have hreg : (sourceTransverseHessian a L).det ≠ 0 :=
    sourceTransverseHessian_det_ne_zero_of_generic a L ha
  have hker :
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K))) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K)
            (sourceNegativeMixedHessian a L i) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hg : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  have hH : ∀ i j : Fin 3,
      (sourceTransverseHessian a L i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F
  have hr : ∀ i : Fin 3,
      (sourceNegativeMixedHessian a L i).IsHomogeneous 2 :=
    sourceCubic_negativeMixedHessian_homogeneous_two a F
  by_cases hpoly : ∀ i : Fin 3, ∃ p : B3 K, g p = V (.inr i)
  · exact Or.inl
      (exists_linear_matrix_of_poleFree_fractionKernel g hg
        (sourceTransverseHessian a L)
        (sourceNegativeMixedHessian a L)
        (fun i : Fin 3 => V (.inr i))
        hH hr hreg hker hpoly)
  · push_neg at hpoly
    have hnotSq : ¬ Squarefree (sourceTransverseHessian a L).det := by
      intro hsq
      exact sourceCubic_squarefreePole_impossible
        F a V hV hgrad hsq hpoly
    exact Or.inr
      (exists_sourceCubic_repeated_linear_factor a F hreg hnotSq)

end
end HC4.Polynomial.RankThreeCubic
