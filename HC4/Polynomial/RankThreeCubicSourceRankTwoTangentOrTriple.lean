import HC4.Polynomial.RankThreeCubicSourceLinearTensorEvaluation
import HC4.Polynomial.RankThreeCubicSourceRankTwoAdjugateAlignment
import HC4.Polynomial.RankThreeCubicSourceRankOneElimination
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import Mathlib.Tactic

/-!
# Actual source rank-two residue: tangent plane or triple Hessian pole

This theorem joins the recently verified rank-one exclusion and
source-derived principal pivot with the new tensor kernel-leaf
argument. For an actual reduced denominator pole of the full
source cubic characteristic, choose its normalized nonzero
residue S in K[y]/(p), its homogeneous linear equation p=ell·y,
and the exact determinant factorisation det H=p²*c.

H(y) S=0 follows from the normalized characteristic equation.
Symmetry of the actual source third derivative tensor and the
time-zero quadratic transport give H(S) S=0. Consequently
det H(S)=det H(y+S)=0. The tensor repeated-pole theorem
gives the *source-honest* alternative

  p | sum_i C(ell_i)*T_i    or    p | c,

where T is the actual normalized polynomial numerator of
the source rational characteristic.

The left alternative says that the residue velocity is tangent
to the repeated-pole hyperplane; the right says that the
linear complementary factor is associated to p, i.e. the
Hessian determinant has a triple pole. No tangency or rank-two
chart is separately assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Every genuine cubic denominator pole has a nonzero normalized
source residue which is tangent to its hyperplane, unless the
linear cofactor itself is divisible by the pole (triple
determinant factor). -/
theorem sourceCubic_genuineRankTwo_residue_tangent_or_triple
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (j : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j))) :
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
    ∃ (k : Fin 3) (c s : B3 K)
      (T : Fin 3 → B3 K) (ell : Fin 3 → K),
      H.det = (p * p) * c ∧
      c ≠ 0 ∧
      (¬ p ∣ H.adjugate k k) ∧
      p ∣ s ∧
      (∀ l : Fin 3,
        algebraMap (B3 K) (F3 K) (T l) =
          algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      ((p ∣ ∑ i : Fin 3, MvPolynomial.C (ell i) * T i) ∨ p ∣ c) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F i j
  have hDhom : H.det.IsHomogeneous 3 :=
    sourceCubic_transverseHessian_det_homogeneous_three a F
  have hpp : p * p ∣ H.det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad j p hp hpd hpn
  obtain ⟨c, hfactor, hc0, hpdeg, hcdeg⟩ :=
    cubic_homogeneous_repeatedFactor_exact_linear_cofactor
      H.det p hDhom hregular hp hpp
  obtain ⟨ell, hpoly, hell⟩ :=
    homogeneousCubic_repeatedDegreeOneFactor_linearForm
      H.det p c hDhom hfactor hp.ne_zero hc0 hpdeg hcdeg
  obtain ⟨gamma, hcLinear⟩ :=
    homogeneousCubic_repeatedDegreeOneFactor_cofactorLinearForm
      H.det p c hDhom hfactor hp.ne_zero hc0 hpdeg hcdeg
  obtain ⟨k, hk⟩ :=
    sourceCubic_genuinePole_has_principalRankTwo
      F a V hV hgrad hregular j p hp hpd hpn
  obtain ⟨s, T, hps, hscale, hSk, hSker, _halign, hquad⟩ :=
    sourceCubic_genuinePole_rankTwo_adjugateAlignedResidue
      F a V hV hgrad j p hp hpd hpn k hk
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  let S : Fin 3 → R := fun t => q (T t)
  let x : Fin 3 → R := fun t => q (MvPolynomial.X t)
  let D : Fin 3 → Fin 3 → Fin 3 → R :=
    fun t i j => q (pderiv t (H i j))
  let ellR : Fin 3 → R := fun t => algebraMap K R (ell t)
  let gammaR : Fin 3 → R := fun t => algebraMap K R (gamma t)
  have hqC (b : K) :
      q (MvPolynomial.C b) = algebraMap K R b := by
    change (algebraMap (B3 K) R) (algebraMap K (B3 K) b) =
      algebraMap K R b
    exact (IsScalarTower.algebraMap_apply K (B3 K) R b).symm
  have hTensorEval (v : Fin 3 → R) :
      H.map (MvPolynomial.aeval v).toRingHom =
        cubicTensorHessianAt D v :=
    homogeneousLinearHessian_tensor_evaluation
      H hhom q hqC v
  have hHbase :
      cubicTensorHessianAt D x = H.map q := by
    ext i j
    have heuler := (hhom i j).sum_X_mul_pderiv
    have hlin : H i j = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * pderiv t (H i j) := by
      simpa only [one_nsmul] using heuler.symm
    change (∑ t : Fin 3,
      q (MvPolynomial.X t) * q (pderiv t (H i j))) = q (H i j)
    calc
      (∑ t : Fin 3, q (MvPolynomial.X t) * q (pderiv t (H i j))) =
          q (∑ t : Fin 3, (MvPolynomial.X t : B3 K) *
            pderiv t (H i j)) := by
              simp only [map_sum, map_mul]
      _ = q (H i j) := congrArg q hlin.symm
  have hswap₂ (t i j : Fin 3) : D t i j = D t j i := by
    have hsym := sourceTransverseHessian_isSymm a L
    have h := congrArg (fun P : B3 K => q (pderiv t P))
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
    exact congrArg q hder
  have hquadTensor (i : Fin 3) :
      (∑ l : Fin 3, ∑ m : Fin 3,
        D i l m * S l * S m) = 0 := hquad i
  have hkerTensor : (cubicTensorHessianAt D x) *ᵥ S = 0 := by
    rw [hHbase]
    exact hSker
  have hEvalp (v : Fin 3 → R) :
      MvPolynomial.aeval v p = cubicPoleLinearFunctional ellR v :=
    homogeneousLinearPole_aeval_eq_linearFunctional p ell hpoly v
  have hEvalc (v : Fin 3 → R) :
      MvPolynomial.aeval v c = cubicPoleLinearFunctional gammaR v :=
    homogeneousLinearPole_aeval_eq_linearFunctional c gamma hcLinear v
  have hFactorTensor (v : Fin 3 → R) :
      (cubicTensorHessianAt D v).det =
        cubicPoleLinearFunctional ellR v *
        cubicPoleLinearFunctional ellR v *
        cubicPoleLinearFunctional gammaR v := by
    calc
      (cubicTensorHessianAt D v).det =
          (H.map (MvPolynomial.aeval v).toRingHom).det := by
            rw [hTensorEval v]
      _ = MvPolynomial.aeval v H.det := by
            change (H.map (MvPolynomial.aeval v).toRingHom).det =
              (MvPolynomial.aeval v).toRingHom H.det
            simp only [RingHom.map_det, RingHom.mapMatrix_apply]
      _ = MvPolynomial.aeval v ((p * p) * c) := by rw [hfactor]
      _ = cubicPoleLinearFunctional ellR v *
          cubicPoleLinearFunctional ellR v *
          cubicPoleLinearFunctional gammaR v := by
            simp only [map_mul, hEvalp, hEvalc]
  have hqP : q p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (dvd_refl p))
  have hpX : cubicPoleLinearFunctional ellR x = 0 := by
    calc
      cubicPoleLinearFunctional ellR x =
          q (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
            MvPolynomial.C (ell i)) := by
          simp only [map_sum, map_mul]
          unfold cubicPoleLinearFunctional
          apply Finset.sum_congr rfl
          intro i _
          dsimp [ellR, x]
          rw [hqC]
          ring
      _ = q p := congrArg q hpoly.symm
      _ = 0 := hqP
  have hcX : cubicPoleLinearFunctional gammaR x = q c := by
    rw [hcLinear]
    simp only [map_sum, map_mul]
    unfold cubicPoleLinearFunctional
    apply Finset.sum_congr rfl
    intro i _
    dsimp [gammaR, x]
    rw [hqC]
    ring
  have hSplit :
      cubicPoleLinearFunctional ellR S = 0 ∨
        cubicPoleLinearFunctional gammaR x = 0 :=
    cubicTensor_repeatedPole_kernel_tangent_or_triple
      D hswap₁ hswap₂ ellR gammaR hFactorTensor
      x S k hSk hpX hkerTensor hquadTensor
  refine ⟨k, c, s, T, ell, hfactor, hc0, hk, hps, hscale, hpoly, ?_⟩
  rcases hSplit with htangent | htriple
  · left
    have hqTang :
        q (∑ i : Fin 3, MvPolynomial.C (ell i) * T i) = 0 := by
      calc
        q (∑ i : Fin 3, MvPolynomial.C (ell i) * T i) =
            cubicPoleLinearFunctional ellR S := by
              simp only [map_sum, map_mul]
              unfold cubicPoleLinearFunctional
              apply Finset.sum_congr rfl
              intro i _
              dsimp [ellR, S]
              rw [hqC]
        _ = 0 := htangent
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hqTang)
  · right
    have hqc : q c = 0 := by rw [← hcX]; exact htriple
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hqc)

end
end HC4.Polynomial.RankThreeCubic
