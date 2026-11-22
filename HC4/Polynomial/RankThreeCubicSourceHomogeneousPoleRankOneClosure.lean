import HC4.Polynomial.RankThreeCubicTensorGeneralPlaneContradiction
import HC4.Polynomial.RankThreeCubicSourceCoordinateRankOneClosure
import Mathlib.Tactic

/-!
# Rank-one pole contradiction at an arbitrary homogeneous linear pole

Let H be the actual source transverse Hessian of a cubic initial form,
and let p = sum_i ell_i X_i be a nonzero homogeneous linear polynomial.
If every 2x2 cofactor of H is divisible by p, then the Hessian
vanishes in rank at most one on p=0.

Choose an explicit invertible frame whose last two columns lie in
the kernel of ell. At the two columns and their sum, every
cofactor of the Hessian evaluates to zero. The global symmetric
cubic tensor obstruction then forces det H=0 at every point,
contradicting the actual source regularity.

No coordinate-axis choice is assumed. The only *remaining*
source bridge is to show that the irreducible degree-one factor
p of the homogeneous determinant has this homogeneous linear
representation with a nonzero coefficient vector.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The rank-at-most-one branch is impossible for every nonzero
homogeneous linear pole of the *actual* cubic source transverse
Hessian. No extra normalized kernel or Schur pivot is assumed. -/
theorem sourceCubic_homogeneousLinearPole_rankOne_impossible
    (F : SB K) (a : K)
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ t : Fin 3,
      (MvPolynomial.X t : B3 K) * MvPolynomial.C (ell t))
    (hell : ell ≠ 0)
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (hcof : ∀ i j : Fin 3,
      p ∣ (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate i j) :
    False := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let D : Fin 3 → Fin 3 → Fin 3 → K :=
    fun t i j => (pderiv t (H i j)).coeff 0
  have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F i j
  have hderConst (t i j : Fin 3) :
      pderiv t (H i j) = MvPolynomial.C (D t i j) := by
    have hdeg0 : (pderiv t (H i j)).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2
        ((hhom i j).pderiv)
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
  have hlinear (i j : Fin 3) :
      H i j = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * MvPolynomial.C (D t i j) := by
    have heuler := (hhom i j).sum_X_mul_pderiv
    calc
      H i j = (1 : ℕ) • (H i j) := by simp
      _ = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * pderiv t (H i j) := heuler.symm
      _ = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * MvPolynomial.C (D t i j) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hderConst t i j]
  have hEval (v : Fin 3 → K) (i j : Fin 3) :
      MvPolynomial.aeval v (H i j) =
        ∑ t : Fin 3, v t * D t i j := by
    rw [hlinear i j]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
  have hswap₂ (t i j : Fin 3) : D t i j = D t j i := by
    have hsym := sourceTransverseHessian_isSymm a L
    have h := congrArg (fun P : B3 K => (pderiv t P).coeff 0)
      (hsym.apply i j)
    exact h.symm
  have hswap₁ (t i j : Fin 3) : D t i j = D i t j := by
    have hleft :
        pderiv t (H i j) =
          referenceSlice a
            (pderiv (.inr t)
              (pderiv (.inr j) (pderiv (.inr i) L))) := by
      change pderiv t (referenceSlice a
        (pderiv (.inr j) (pderiv (.inr i) L))) = _
      exact referenceSlice_pderiv a t _
    have hright :
        pderiv i (H t j) =
          referenceSlice a
            (pderiv (.inr i)
              (pderiv (.inr j) (pderiv (.inr t) L))) := by
      change pderiv i (referenceSlice a
        (pderiv (.inr j) (pderiv (.inr t) L))) = _
      exact referenceSlice_pderiv a i _
    have hcomm :
        pderiv (.inr t)
          (pderiv (.inr j) (pderiv (.inr i) L)) =
        pderiv (.inr i)
          (pderiv (.inr j) (pderiv (.inr t) L)) := by
      rw [HC4.Newton.pderiv_comm_backport (.inr j) (.inr i) L]
      rw [HC4.Newton.pderiv_comm_backport (.inr t) (.inr i)
        (pderiv (.inr j) L)]
      rw [HC4.Newton.pderiv_comm_backport (.inr t) (.inr j) L]
    have hder : pderiv t (H i j) = pderiv i (H t j) := by
      rw [hleft, hright, hcomm]
    exact congrArg (fun P : B3 K => P.coeff 0) hder
  have hTensor (v : Fin 3 → K) :
      cubicTensorHessianAt D v =
        H.map (MvPolynomial.aeval v).toRingHom := by
    ext i j
    change (∑ t : Fin 3, v t * D t i j) =
      MvPolynomial.aeval v (H i j)
    exact (hEval v i j).symm
  obtain ⟨M, hM, hM1, hM2⟩ :=
    exists_invertible_frame_annihilating_linearFunctional ell hell
  have hform (v : Fin 3 → K)
      (hv : (∑ t : Fin 3, ell t * v t) = 0) :
      MvPolynomial.aeval v p = 0 := by
    calc
      MvPolynomial.aeval v p =
          ∑ t : Fin 3, v t * ell t := by
            rw [hpoly]
            simp only [map_sum, map_mul, MvPolynomial.aeval_X,
              MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
      _ = ∑ t : Fin 3, ell t * v t := by
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = 0 := hv
  have hcofAt (v : Fin 3 → K)
      (hpv : MvPolynomial.aeval v p = 0) :
      (cubicTensorHessianAt D v).adjugate = 0 := by
    rw [hTensor v]
    have hmap : (H.map (MvPolynomial.aeval v).toRingHom).adjugate =
        H.adjugate.map (MvPolynomial.aeval v).toRingHom :=
      ((MvPolynomial.aeval v).toRingHom.map_adjugate H).symm
    rw [hmap]
    ext i j
    change MvPolynomial.aeval v (H.adjugate i j) = 0
    obtain ⟨u, hu⟩ := hcof i j
    rw [hu, map_mul, hpv, zero_mul]
  have hM12 : (∑ t : Fin 3,
      ell t * (M t 1 + M t 2)) = 0 := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hM1, hM2, zero_add]
  have hA : (cubicTensorHessianAt D (fun t => M t 1)).adjugate = 0 :=
    hcofAt (fun t => M t 1) (hform _ hM1)
  have hB : (cubicTensorHessianAt D (fun t => M t 2)).adjugate = 0 :=
    hcofAt (fun t => M t 2) (hform _ hM2)
  have hAB : (cubicTensorHessianAt D
      (fun t => M t 1 + M t 2)).adjugate = 0 :=
    hcofAt (fun t => M t 1 + M t 2) (hform _ hM12)
  have hdetAll :
      ∀ v : Fin 3 → K, (cubicTensorHessianAt D v).det = 0 :=
    cubicTensor_rankOnePlane_global_det_zero
      D hswap₁ hswap₂ M hM hA hB hAB
  have hEvalZero (v : Fin 3 → K) :
      MvPolynomial.aeval v H.det = 0 := by
    have hv := hdetAll v
    rw [hTensor v] at hv
    change (MvPolynomial.aeval v).toRingHom H.det = 0
    rw [RingHom.map_det]
    exact hv
  have hdetZero : H.det = 0 := by
    apply (sourceCubic_transverseHessian_det_homogeneous_three a F).eq_zero_of_forall_eval_eq_zero
    intro v
    simpa only [MvPolynomial.coe_aeval_eq_eval] using hEvalZero v
  exact hregular hdetZero

end
end HC4.Polynomial.RankThreeCubic
