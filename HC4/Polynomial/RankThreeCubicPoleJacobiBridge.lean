import HC4.Polynomial.RankThreeCubicRankOneQuadraticContraction
import HC4.Polynomial.RankThreeCubicJacobiDetPderiv
import HC4.Polynomial.RankThreeCubicSourceSingularCoefficientResidue
import Mathlib.Tactic

/-!
# Cubic source: the rank-one Cramer residue controls Jacobi derivatives

The constant coefficient of a source-derived third-derivative transport
family is the partial derivative of the source transverse Hessian.
We combine that fact with the existing rank-one Cramer cancellation
and the singular-safe Jacobi identity.

This module deliberately stops at a *derivative-divisibility* conclusion.
The separate squarefree/characteristic-zero contradiction is not assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The zero time coefficient of line substitution is the original
evaluation, even if the line velocity lies in a fraction field. -/
theorem cubic_lineEval_coeff_zero
    {F : Type*} [CommRing F] [Algebra K F]
    {ι : Type*} (z V : ι → F)
    (P : MvPolynomial ι K) :
    (lineEval z V P).coeff 0 = MvPolynomial.aeval z P := by
  classical
  let E := lineEval (K := K) z V
  have hev :
      (_root_.Polynomial.constantCoeff.comp E.toRingHom) =
        (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] F).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [E, lineEval, IsScalarTower.algebraMap_apply K F
        (_root_.Polynomial F), _root_.Polynomial.algebraMap_eq]
    · intro i
      simp [E, lineEval]
  exact RingHom.congr_fun hev P

/-- Identify the time-zero coefficient of the *actual* source cubic
third-derivative family with the derivative of its transverse Hessian
on the same longitudinal slice. No characteristic pole assumption. -/
theorem cubic_sourceThirdDerivative_timeZero
    (a : K) (L : SB K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (i j k : Fin 3)
    (Q : _root_.Polynomial (B3 K))
    (hQ :
      Q.map (algebraMap (B3 K) (F3 K)) =
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) :
    Q.coeff 0 = pderiv i (sourceTransverseHessian a L j k) := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hcomm :
      pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)) =
      pderiv (.inr i) (pderiv (.inr k) (pderiv (.inr j) L)) := by
    rw [HC4.Newton.pderiv_comm_backport (.inr j) (.inr i) L]
    rw [HC4.Newton.pderiv_comm_backport (.inr k) (.inr i)
      (pderiv (.inr j) L)]
  have hleft :
      g (Q.coeff 0) =
        MvPolynomial.aeval (transverseGenericPoint a)
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) := by
    calc
      g (Q.coeff 0) = (Q.map g).coeff 0 := by simp
      _ = (lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))).coeff 0 :=
        congrArg (fun p : _root_.Polynomial (F3 K) => p.coeff 0) hQ
      _ = _ := cubic_lineEval_coeff_zero _ _ _
  have hright :
      g (pderiv i (sourceTransverseHessian a L j k)) =
        MvPolynomial.aeval (transverseGenericPoint a)
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) := by
    calc
      g (pderiv i (sourceTransverseHessian a L j k)) =
          g (referenceSlice a
            (pderiv (.inr i) (pderiv (.inr k) (pderiv (.inr j) L)))) := by
            change g (pderiv i (referenceSlice a
              (pderiv (.inr k) (pderiv (.inr j) L)))) = _
            rw [referenceSlice_pderiv]
      _ = MvPolynomial.aeval (transverseGenericPoint a)
          (pderiv (.inr i) (pderiv (.inr k) (pderiv (.inr j) L))) :=
            referenceSlice_fractionEvaluation a _
      _ = _ := by rw [hcomm]
  exact (IsFractionRing.injective (B3 K) (F3 K)) (hleft.trans hright.symm)

/-- Pure algebraic Jacobi bridge. When a symmetric transverse Hessian
becomes singular after a domain-valued ring map, and its nonzero Cramer
residue is annihilated by the quadratic Hessian-derivative families,
the image of every derivative of the determinant vanishes.

This works *without* assuming that the determinant has a repeated factor. -/
theorem cubic_rankOneCramer_Jacobi_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hSym : H.IsSymm)
    (q : B3 K →+* R)
    (hdetzero : q H.det = 0)
    (r : Fin 3 → B3 K)
    (k : Fin 3)
    (hkk : q (H.adjugate k k) ≠ 0)
    (hS :
      (H.adjugate.map q) *ᵥ (fun j : Fin 3 => q (r j)) ≠ 0)
    (hquad :
      ∀ i : Fin 3,
        (∑ j : Fin 3, ∑ l : Fin 3,
          q (pderiv i (H j l)) *
            ((H.adjugate.map q) *ᵥ
              (fun n : Fin 3 => q (r n))) j *
            ((H.adjugate.map q) *ᵥ
              (fun n : Fin 3 => q (r n))) l) = 0) :
    ∀ i : Fin 3, q (pderiv i H.det) = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) R := H.map q
  let B : Matrix (Fin 3) (Fin 3) R := M.adjugate
  have hmap : B = H.adjugate.map q := by
    exact (q.map_adjugate H).symm
  have hMdet : M.det = 0 := by
    change (H.map q).det = 0
    rw [← RingHom.map_det]
    exact hdetzero
  have hMsymm : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change q (H i j) = q (H j i)
    exact congrArg q (hSym.apply i j)
  have hBsymm : B.IsSymm := hMsymm.adjugate
  have hcross (i j : Fin 3) :
      B k k * B i j = B i k * B k j :=
    adjugate_rankOne_cross_products M hMdet k i j
  have hkkB : B k k ≠ 0 := by
    rw [hmap]
    exact hkk
  have hSB : B *ᵥ (fun j : Fin 3 => q (r j)) ≠ 0 := by
    rw [hmap]
    exact hS
  intro i
  have hquadB :
      (∑ j : Fin 3, ∑ l : Fin 3,
        q (pderiv i (H j l)) *
          (B *ᵥ (fun n : Fin 3 => q (r n))) j *
          (B *ᵥ (fun n : Fin 3 => q (r n))) l) = 0 := by
    rw [hmap]
    exact hquad i
  have hcontraction :=
    rankOneCramer_quadratic_zero_implies_adjugate_contraction_zero
      B hBsymm (fun j : Fin 3 => q (r j))
      k hkkB hcross hSB
      (fun j l : Fin 3 => q (pderiv i (H j l))) hquadB
  calc
    q (pderiv i H.det) =
        ∑ j : Fin 3, ∑ l : Fin 3,
          q (H.adjugate l j) * q (pderiv i (H j l)) := by
        rw [pderiv_det_fin_three H i]
        simp only [map_sum, map_mul]
    _ = ∑ j : Fin 3, ∑ l : Fin 3,
          q (pderiv i (H j l)) * B j l := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [hmap]
        change q (H.adjugate l j) * q (pderiv i (H j l)) =
          q (pderiv i (H j l)) * q (H.adjugate j l)
        rw [(hSym.adjugate).apply j l]
        ring
    _ = 0 := hcontraction

end HC4.Polynomial.RankThreeCubic
