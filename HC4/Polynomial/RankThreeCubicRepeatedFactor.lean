import HC4.Polynomial.RankThreeCubicPoleSquarefreeResidue
import Mathlib

/-!
# Low-degree repeated factors in the cubic Hessian determinant

When a nonzero polynomial has total degree at most three, a
nonsquarefree factorisation has an irreducible repeated factor of
total degree exactly one.  This is a general UFD statement, not
a contradiction of the genuine cubic source.

The full-rank cubic transverse Hessian has a homogeneous cubic
determinant. Transporting this degree bound from the source is
the separate input to the final source-facing theorem.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- In three variables, a nonzero nonsquarefree polynomial of total
degree at most three has a repeated irreducible factor of degree one.
The factor can be affine linear here; its homogeneous linearity is
a separate consequence of homogeneous source data. -/
theorem exists_degree_one_repeated_irreducible_of_cubic_degree
    (D : B3 K)
    (hD : D ≠ 0)
    (hdeg : D.totalDegree ≤ 3)
    (hnot : ¬ Squarefree D) :
    ∃ p : B3 K, Irreducible p ∧ p * p ∣ D ∧ p.totalDegree = 1 := by
  classical
  have hbad : ∃ p : B3 K, Irreducible p ∧ p * p ∣ D := by
    by_contra h
    apply hnot
    apply (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hD).2
    intro p hp hpp
    exact h ⟨p, hp, hpp⟩
  obtain ⟨p, hp, hpp⟩ := hbad
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdegsq : (p * p).totalDegree = p.totalDegree + p.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hp0 hp0
  have hle : (p * p).totalDegree ≤ D.totalDegree := by
    obtain ⟨c, hc⟩ := hpp
    have hc0 : c ≠ 0 := by
      intro hz
      apply hD
      rw [hc, hz, mul_zero]
    have hprod : ((p * p) * c).totalDegree =
        (p * p).totalDegree + c.totalDegree :=
      MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero hp0 hp0) hc0
    calc
      (p * p).totalDegree ≤ (p * p).totalDegree + c.totalDegree := by omega
      _ = D.totalDegree := by rw [hc, hprod]
  have hpos : 0 < p.totalDegree := by
    by_contra hn
    have hzero : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hn
    have hconst : p = C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    have hc0 : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp0
      rw [hconst, hc, map_zero]
    have hu : IsUnit p :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
        ⟨isUnit_iff_ne_zero.mpr hc0, hzero⟩
    exact hp.not_isUnit hu
  have hpdeg : p.totalDegree = 1 := by omega
  exact ⟨p, hp, hpp, hpdeg⟩

/-- A nonsquarefree source transverse Hessian determinant with the
cubic total-degree bound has a repeated degree-one irreducible
factor. The nonzero Hessian determinant is already supplied by
the source-level characteristic construction. -/
theorem exists_sourceCubic_repeated_linear_factor_of_degree_bound
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hreg : (sourceTransverseHessian a L).det ≠ 0)
    (hdeg : (sourceTransverseHessian a L).det.totalDegree ≤ 3)
    (hnot : ¬ Squarefree (sourceTransverseHessian a L).det) :
    ∃ p : B3 K, Irreducible p ∧
      p * p ∣ (sourceTransverseHessian a L).det ∧
      p.totalDegree = 1 :=
  exists_degree_one_repeated_irreducible_of_cubic_degree
    (sourceTransverseHessian a L).det hreg hdeg hnot

/-- The determinant of a three-by-three matrix of homogeneous
degree-one polynomials is homogeneous of degree three. -/
theorem homogeneous_three_det_of_linear_homogeneous_matrix
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hH : ∀ i j : Fin 3, (H i j).IsHomogeneous 1) :
    H.det.IsHomogeneous 3 := by
  classical
  have htriple (i j k l m n : Fin 3) :
      (H i j * H k l * H m n).IsHomogeneous 3 := by
    simpa only [Nat.reduceAdd] using
      ((hH i j).mul (hH k l)).mul (hH m n)
  rw [Matrix.det_fin_three]
  repeat'
    first
    | apply MvPolynomial.IsHomogeneous.add
    | apply MvPolynomial.IsHomogeneous.sub
    | exact htriple _ _ _ _ _ _

/-- Source honest degree bound: a cubic transverse initial form has
a homogeneous cubic determinant on every longitudinal slice. -/
theorem sourceCubic_transverseHessian_det_homogeneous_three [CharZero K]
    (a : K) (F : MvPolynomial (Unit ⊕ Fin 3) K) :
    (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det.IsHomogeneous 3 :=
  homogeneous_three_det_of_linear_homogeneous_matrix
    (sourceTransverseHessian a (initialForm transverseCubicWeight 3 F))
    (sourceCubic_transverseHessian_homogeneous_one a F)

/-- If the source cubic slice has a nonsquarefree transverse Hessian
determinant, the actual source supplies a repeated *degree-one*
irreducible factor. There is no independently assumed degree bound. -/
theorem exists_sourceCubic_repeated_linear_factor [CharZero K]
    (a : K) (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hreg : (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (hnot : ¬ Squarefree (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det) :
    ∃ p : B3 K, Irreducible p ∧
      p * p ∣ (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ∧
      p.totalDegree = 1 :=
  exists_degree_one_repeated_irreducible_of_cubic_degree
    (sourceTransverseHessian a (initialForm transverseCubicWeight 3 F)).det
    hreg
    (sourceCubic_transverseHessian_det_homogeneous_three a F).totalDegree_le
    hnot

/-- Cubic characteristic geometry is either linear, supported on a
repeated degree-one determinant factor, or represented by a nonzero
kernel on an irreducible determinant component. This package has
no hidden squarefreeness or source-degree hypothesis. -/
theorem exists_sourceCubic_linear_or_repeated_linear_or_primeResidue
    [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FractionRing (B3 K)),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (FractionRing (B3 K))) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (FractionRing (B3 K))
            (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (FractionRing (B3 K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ p : B3 K, Irreducible p ∧
            p * p ∣ (sourceTransverseHessian a L).det ∧
            p.totalDegree = 1)
        ∨ (∃ p : B3 K, Irreducible p ∧
            p ∣ (sourceTransverseHessian a L).det ∧
            ∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
              S ≠ 0 ∧
              ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0)) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linear_or_nonsquarefree_or_primeResidue
      F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnot | hres
  · exact Or.inl hlin
  · exact Or.inr (Or.inl
      (exists_sourceCubic_repeated_linear_factor a F hreg hnot))
  · exact Or.inr (Or.inr hres)


end
end HC4.Polynomial.RankThreeCubic
