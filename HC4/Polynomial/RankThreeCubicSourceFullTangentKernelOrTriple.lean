import HC4.Polynomial.RankThreeCubicSourceUniformTangentKernel
import HC4.Polynomial.RankThreeCubicZeroBinarySourceCofactor
import Mathlib.Tactic

/-!
# Source cubic: eliminate the zero-tangential-block double-pole branch

The previous whole-plane classification gave, for an actual
source cubic denominator pole, either a scalar triple Hessian
determinant, an identically zero tangential binary Hessian, or
a fixed nonzero *full* Hessian tangent-kernel direction on the
entire pole plane.

The zero-block branch now forces p | c in det H = p²*c, by
the symmetric-tensor normal form and its exact determinant
expansion. The homogeneous-degree-one complementary factor
then makes det H a nonzero scalar multiple of p³.

Therefore every genuine cubic source pole has the sharpened
alternative:

* an invertible pole-adapted frame and a fixed nonzero
  full-Hessian tangent kernel along its entire pole plane;
* an exact nonzero scalar triple Hessian determinant factor.

This theorem preserves the actual denominator pole and a
surviving rank-two principal cofactor, and introduces no
source endpoint assumptions. It does not yet rule out the
fixed-kernel or triple cases.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The exact-double genuine source cubic pole has a common
nonzero full Hessian kernel direction tangent to the pole,
unless its Hessian determinant has an exact scalar triple
linear factor. -/
theorem sourceCubic_genuineRankTwo_fullTangentKernel_or_exactTriple
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
    (u : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u))) :
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
    ∃ (ell : Fin 3 → K) (k : Fin 3),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      (¬ p ∣ H.adjugate k k) ∧
      ((∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
          M.det ≠ 0 ∧
          (∑ i : Fin 3, ell i * M i 1) = 0 ∧
          (∑ i : Fin 3, ell i * M i 2) = 0 ∧
          (r ≠ 0 ∨ t ≠ 0) ∧
          ∀ x y : K,
            let B := M.transpose *
              H.map (MvPolynomial.aeval
                (M.mulVec ![(0 : K), x, y])).toRingHom * M
            B 0 1 * r + B 0 2 * t = 0 ∧
            B 1 1 * r + B 1 2 * t = 0 ∧
            B 2 1 * r + B 2 2 * t = 0)
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_uniformTangentBlockZero_or_fullKernel_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hsplit with ⟨M, r, t, hM, hM1, hM2, hrt, hker, hbranch⟩ | htriple
  · rcases hbranch with hzero | hfull
    · right
      have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
        sourceCubic_transverseHessian_homogeneous_one a F i j
      have hDhom : H.det.IsHomogeneous 3 :=
        sourceCubic_transverseHessian_det_homogeneous_three a F
      have hpp : p * p ∣ H.det :=
        sourceCubic_genuinePole_is_repeatedFactor
          F a V hV hgrad u p hp hpd hpn
      obtain ⟨c, hfactor, hc0, hpdeg, hcdeg⟩ :=
        cubic_homogeneous_repeatedFactor_exact_linear_cofactor
          H.det p hDhom hregular hp hpp
      obtain ⟨gamma, hcform⟩ :=
        homogeneousCubic_repeatedDegreeOneFactor_cofactorLinearForm
          H.det p c hDhom hfactor hp.ne_zero hc0 hpdeg hcdeg
      let q : B3 K →+* K :=
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom
      let D : Fin 3 → Fin 3 → Fin 3 → K :=
        fun z i j => q (pderiv z (H i j))
      have hqC (b : K) :
          q (MvPolynomial.C b) = algebraMap K K b := by
        change MvPolynomial.aeval
          (fun _ : Fin 3 => (0 : K)) (MvPolynomial.C b) = _
        simp
      have hEval (w : Fin 3 → K) :
          H.map (MvPolynomial.aeval w).toRingHom =
            cubicTensorHessianAt D w :=
        homogeneousLinearHessian_tensor_evaluation H hhom q hqC w
      have hswap₂ (z i j : Fin 3) : D z i j = D z j i := by
        have hsym := sourceTransverseHessian_isSymm a L
        exact (congrArg (fun P : B3 K => q (pderiv z P))
          (hsym.apply i j)).symm
      have hswap₁ (z i j : Fin 3) : D z i j = D i z j := by
        have hleft :
            pderiv z (H i j) =
              referenceSlice a
                (pderiv (.inr z)
                  (pderiv (.inr j) (pderiv (.inr i) L))) := by
          change pderiv z (referenceSlice a
            (pderiv (.inr j) (pderiv (.inr i) L))) = _
          exact referenceSlice_pderiv a z _
        have hright :
            pderiv i (H z j) =
              referenceSlice a
                (pderiv (.inr i)
                  (pderiv (.inr j) (pderiv (.inr z) L))) := by
          change pderiv i (referenceSlice a
            (pderiv (.inr j) (pderiv (.inr z) L))) = _
          exact referenceSlice_pderiv a i _
        have hcomm :
            pderiv (.inr z)
              (pderiv (.inr j) (pderiv (.inr i) L)) =
            pderiv (.inr i)
              (pderiv (.inr j) (pderiv (.inr z) L)) := by
          rw [HC4.Newton.pderiv_comm_backport (.inr j) (.inr i) L]
          rw [HC4.Newton.pderiv_comm_backport (.inr z) (.inr i)
            (pderiv (.inr j) L)]
          rw [HC4.Newton.pderiv_comm_backport (.inr z) (.inr j) L]
        have hder : pderiv z (H i j) = pderiv i (H z j) := by
          rw [hleft, hright, hcomm]
        exact congrArg q hder
      have hell : ell ≠ 0 := by
        intro he
        apply hp.ne_zero
        rw [hpoly, he]
        simp
      have hpc : p ∣ c :=
        homogeneousLinearCubic_zeroBinaryBlock_implies_p_dvd_cofactor
          H D hswap₁ hswap₂ hEval p c ell gamma
          hfactor hpoly hcform hell M hM hM1 hM2 hzero
      exact repeatedLinearCofactor_dvd_implies_exactTriple
        H.det p c hfactor hp.ne_zero hc0 hpdeg hcdeg hpc
    · left
      refine ⟨M, r, t, hM, hM1, hM2, hrt, ?_⟩
      intro x y
      have hk := hker x y
      have hn := hfull x y
      exact ⟨hn, hk.1, hk.2⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
