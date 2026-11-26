module

public import HC4.Polynomial.RankThreeCubicPoleTransportTrichotomy
public import HC4.Polynomial.RankThreeCubicSourceSquarefreeSingularResidue
public import Mathlib.Tactic

/-!
# Full-source cubic characteristic classification with singular pole residue

This theorem is an unconditional source-honest trichotomy under the
existing full-transverse-rank cubic initial-form hypotheses:

* the rational characteristic is constant-linear in the transverse variables;
* a repeated irreducible degree-one factor occurs in the transverse
  Hessian determinant;
* or the actual nonzero Cramer numerator survives on a squarefree pole
  component, is killed by the reduced Hessian, satisfies all three
  source third-derivative quadratic gradient equations, and admits a
  principal 2x2 Hessian cofactor on the same component.

The full gradient-transport identity, source Hessian equation and pole
geometry use the *same* a and V. There is no extra assumed squarefreeness,
characteristic regularity, or singular-direction endpoint.

This is a reduction, not a contradiction eliminating the pole.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSourceSingularTrichotomy

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSourceSingularTrichotomy

open RankThreeCubicSourceSingularTrichotomy (B3 F3 SB)

/-- The nonpolynomial cubic alternative is now a nonzero *source*
singular-residue certificate rather than an unspecified quotient kernel.
The repeated factor case remains explicit and is not ruled out. -/
theorem exists_sourceCubic_linear_or_repeated_or_nonzeroSingularResidue
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
            p.totalDegree = 1)
        ∨ (∃ p : B3 K, Irreducible p ∧
            p ∣ (sourceTransverseHessian a L).det ∧
            let H := sourceTransverseHessian a L
            let r := sourceNegativeMixedHessian a L
            let q := Ideal.Quotient.mk (Ideal.span {p})
            let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
              fun j => q ((H.adjugate *ᵥ r) j)
            S ≠ 0 ∧
            (H.map q) *ᵥ S = 0 ∧
            (∀ i : Fin 3,
              ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
                (∀ j k : Fin 3,
                  (Q j k).map (algebraMap (B3 K) (F3 K)) =
                    lineEval (transverseGenericPoint a) V
                      (pderiv (.inr k) (pderiv (.inr j)
                        (pderiv (.inr i) L)))) ∧
                quadraticFamilyEval
                  (fun j k : Fin 3 => (Q j k).map q)
                  (fun j : Fin 3 => _root_.Polynomial.C (S j)) = 0) ∧
            (∃ k : Fin 3, ¬ p ∣ H.adjugate k k))) := by
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
    by_cases hsq : Squarefree (sourceTransverseHessian a L).det
    · exact Or.inr (Or.inr
        (exists_sourceCubic_squarefreePole_nonzeroSingularResidue
          F a V hV hgrad hsq hpoly))
    · exact Or.inr (Or.inl
        (exists_sourceCubic_repeated_linear_factor a F hreg hsq))

end
end HC4.Polynomial.RankThreeCubic
