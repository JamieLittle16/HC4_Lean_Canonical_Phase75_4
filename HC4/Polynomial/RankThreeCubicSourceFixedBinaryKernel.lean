import HC4.Polynomial.RankThreeCubicTensorFrameBinaryKernel
import HC4.Polynomial.RankThreeCubicSourceAdaptedBinarySingular
import HC4.Polynomial.RankThreeCubicSourceLinearTensorEvaluation
import Mathlib.Tactic

/-!
# Actual source rank-two double pole: a fixed tangential binary Hessian kernel

The Hessian of the actual transverse cubic initial form is
homogeneous linear in the transverse coordinates. Its first
derivatives define a constant, fully symmetric cubic tensor,
not an arbitrary linear matrix pencil.

The source-adapted-frame theorem gives a vanishing principal
normal cofactor at every tangent-plane point. Pulling the
source tensor through that frame, the three-point binary
Hessian theorem then produces a *single nonzero* tangent
vector that lies in the kernel of the tangential 2x2 Hessian
block for every point of the plane.

A vanishing tangent-block product does not yet assert the
entire 3x3 Hessian has a constant kernel. That extension needs
the repeated determinant factor and further cubic symmetry.
The exact scalar triple-pole branch remains explicit.
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

/-- The genuine rank-two cubic source pole has a fixed nonzero
tangent-kernel direction for its adapted binary Hessian block,
unless the determinant is a nonzero scalar multiple of p³.
The pole equation, cofactor and frame all come from the actual
source characteristic. -/
theorem sourceCubic_genuineRankTwo_fixedBinaryKernel_or_exactTriple
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
          (∀ x y : K, ∀ j : Fin 3,
            (M.transpose *
              H.map (MvPolynomial.aeval
                (M.mulVec ![(0 : K), x, y])).toRingHom * M).adjugate 0 j = 0) ∧
          ∀ x y : K,
            let B := M.transpose *
              H.map (MvPolynomial.aeval
                (M.mulVec ![(0 : K), x, y])).toRingHom * M
            (B 1 1 * r + B 1 2 * t = 0) ∧
              (B 2 1 * r + B 2 2 * t = 0))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_adaptedBinarySingular_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hsplit with ⟨M, hM, hM1, hM2, hnormal⟩ | htriple
  · left
    let q : B3 K →+* K :=
      (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom
    let D : Fin 3 → Fin 3 → Fin 3 → K :=
      fun z i j => q (pderiv z (H i j))
    have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
      sourceCubic_transverseHessian_homogeneous_one a F i j
    have hqC (b : K) :
        q (MvPolynomial.C b) = algebraMap K K b := by
      change MvPolynomial.aeval
        (fun _ : Fin 3 => (0 : K)) (MvPolynomial.C b) = _
      simp
    have hEval (w : Fin 3 → K) :
        H.map (MvPolynomial.aeval w).toRingHom =
          cubicTensorHessianAt D w :=
      homogeneousLinearHessian_tensor_evaluation
        H hhom q hqC w
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
    have hnormalD (x y : K) :
        (M.transpose *
          cubicTensorHessianAt D (M.mulVec ![(0 : K), x, y]) *
          M).adjugate 0 0 = 0 := by
      rw [← hEval (M.mulVec ![(0 : K), x, y])]
      exact hnormal x y 0
    obtain ⟨r, t, hrt, hker⟩ :=
      cubicTensor_adaptedPlane_constantTangentKernel
        D hswap₁ hswap₂ M hnormalD
    refine ⟨M, r, t, hM, hM1, hM2, hrt, hnormal, ?_⟩
    intro x y
    have h := hker x y
    rw [hEval (M.mulVec ![(0 : K), x, y])]
    exact h
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
