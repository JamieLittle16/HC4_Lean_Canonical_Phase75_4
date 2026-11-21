import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib

/-!
# Full-gradient-transport-preserving cubic pole trichotomy

The earlier source trichotomy retained the fraction-field transverse
Hessian equation but dropped the full straight characteristic identity.
That identity is essential for the *second-order* pole-residue argument:
the Hessian equation alone does not imply cubic singularity.

Here the full transport, the source-derived Hessian equation, and the
pole alternatives are all retained for exactly the same source
characteristic, at exactly the same longitudinal basepoint. No extra
transport assumption is introduced.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev PB (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev PF (K : Type*) [Field K] := FractionRing (PB K)

/-- Source-honest full characteristic classification, preserving the
straight gradient transport used to construct the rational velocity.

The three cases are: polynomial-linear transverse velocity, a
repeated irreducible linear divisor of the transverse Hessian
determinant, or a nonzero residue kernel with a surviving principal
2x2 cofactor on the same irreducible pole component.

Crucially, the full gradient transport and the Hessian relation have
the *same* V and a, unlike independently existential witnesses. -/
theorem exists_sourceCubic_transport_linear_or_repeated_or_principal
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → PF K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V (pderiv i L) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (PB K) (PF K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (PB K) (PF K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (PB K) (PF K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ p : PB K, Irreducible p ∧
            p * p ∣ (sourceTransverseHessian a L).det ∧
            p.totalDegree = 1)
        ∨ (∃ p : PB K, Irreducible p ∧
            p ∣ (sourceTransverseHessian a L).det ∧
            (∃ S : Fin 3 → (PB K ⧸ Ideal.span {p}),
              S ≠ 0 ∧
              ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) ∧
            (∃ k : Fin 3, ¬ p ∣
              (sourceTransverseHessian a L).adjugate k k))) := by
  classical
  let L := initialForm transverseCubicWeight 3 F
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  obtain ⟨V, hV, hgrad⟩ :=
    exists_transverseCubic_characteristic_at a F hcap hdet ha
  have hreg : (sourceTransverseHessian a L).det ≠ 0 :=
    sourceTransverseHessian_det_ne_zero_of_generic a L ha
  have hker :
      ((sourceTransverseHessian a L).map
          (algebraMap (PB K) (PF K))) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (PB K) (PF K) (sourceNegativeMixedHessian a L i) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  let g : PB K →+* PF K := algebraMap (PB K) (PF K)
  have hg : Function.Injective g :=
    IsFractionRing.injective (PB K) (PF K)
  have hH : ∀ i j : Fin 3, (sourceTransverseHessian a L i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F
  have hr : ∀ i : Fin 3, (sourceNegativeMixedHessian a L i).IsHomogeneous 2 :=
    sourceCubic_negativeMixedHessian_homogeneous_two a F
  by_cases hpoly : ∀ i : Fin 3, ∃ p : PB K, g p = V (.inr i)
  · exact Or.inl
      (exists_linear_matrix_of_poleFree_fractionKernel g hg
        (sourceTransverseHessian a L)
        (sourceNegativeMixedHessian a L)
        (fun i : Fin 3 => V (.inr i))
        hH hr hreg hker hpoly)
  · push_neg at hpoly
    by_cases hsq : Squarefree (sourceTransverseHessian a L).det
    · obtain ⟨p, hp, hpdet, hS, hcof⟩ :=
        exists_residueKernel_and_cofactor_of_squarefree_fractionKernel
          (sourceTransverseHessian a L)
          (sourceNegativeMixedHessian a L)
          (fun i : Fin 3 => V (.inr i)) hker hpoly hsq
      obtain ⟨i, j, hij⟩ := hcof
      have hsym : (sourceTransverseHessian a L).IsSymm :=
        sourceTransverseHessian_isSymm a L
      obtain ⟨k, hk⟩ :=
        exists_principal_cofactor_not_dvd
          (sourceTransverseHessian a L)
          hsym p hp.prime hpdet ⟨i, j, hij⟩
      exact Or.inr (Or.inr ⟨p, hp, hpdet, hS, k, hk⟩)
    · exact Or.inr (Or.inl
        (exists_sourceCubic_repeated_linear_factor a F hreg hsq))

end
end HC4.Polynomial.RankThreeCubic
