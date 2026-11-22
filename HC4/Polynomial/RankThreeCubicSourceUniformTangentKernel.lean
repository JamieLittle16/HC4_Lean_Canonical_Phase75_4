import HC4.Polynomial.RankThreeCubicSourceTangentKernelExtension
import HC4.Polynomial.RankThreeCubicSourceLinearPlanePencil
import Mathlib.Tactic

/-!
# Whole-plane rank-two cubic source obstruction

The source's exactly-double pole gives an adapted linear Hessian
pencil B(u,v), a fixed nonzero kernel of its tangential 2x2
block, and a pointwise alternative:

  tangential block B_tan(u,v)=0
  OR
  B(u,v)*(0,r,t)=0.

Both the tangential block and the normal coupling of the
fixed vector are additive in (u,v), because the source
Hessian is homogeneous linear. The additive zero-set
dichotomy therefore promotes the pointwise alternative into
a *whole-plane* alternative:

  either the entire tangential block vanishes identically
  on the pole plane, or the same nonzero vector (0,r,t)
  is a full Hessian kernel direction everywhere on it.

The exact scalar triple factor remains a separate branch.
Neither of the two exactly-double configurations is assumed
impossible. This is an actual-source theorem, not an abstract
pencil hypothesis.
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

/-- The genuine source double-pole geometry has a uniform
adapted-plane classification: the binary tangent Hessian is
zero everywhere, or a fixed nonzero tangential vector belongs
to the full Hessian kernel everywhere. The triple-pole
alternative is retained. -/
theorem sourceCubic_genuineRankTwo_uniformTangentBlockZero_or_fullKernel_or_triple
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
          ((∀ x y : K,
              let B := M.transpose *
                H.map (MvPolynomial.aeval
                  (M.mulVec ![(0 : K), x, y])).toRingHom * M
              B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0)
           ∨
           (∀ x y : K,
              let B := M.transpose *
                H.map (MvPolynomial.aeval
                  (M.mulVec ![(0 : K), x, y])).toRingHom * M
              B 0 1 * r + B 0 2 * t = 0)))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_fullKernelOrZeroBinaryPointwise_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hsplit with ⟨M, r, t, hM, hM1, hM2, hrt, hpoint⟩ | htriple
  · left
    let B : K → K → Matrix (Fin 3) (Fin 3) K :=
      fun x y => M.transpose *
        H.map (MvPolynomial.aeval
          (M.mulVec ![(0 : K), x, y])).toRingHom * M
    let A : Matrix (Fin 3) (Fin 3) K := B 1 0
    let C : Matrix (Fin 3) (Fin 3) K := B 0 1
    have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
      sourceCubic_transverseHessian_homogeneous_one a F i j
    have hpencil (x y : K) : B x y = x • A + y • C :=
      homogeneousLinearHessian_adaptedPlane_isLinearPencil H hhom M x y
    have hpoint' (x y : K) :
        let P := x • A + y • C
        (P 1 1 = 0 ∧ P 1 2 = 0 ∧ P 2 2 = 0) ∨
          (P 0 1 * r + P 0 2 * t = 0) := by
      have h := hpoint x y
      change (B x y 1 1 = 0 ∧ B x y 1 2 = 0 ∧ B x y 2 2 = 0) ∨
        (B x y 0 1 * r + B x y 0 2 * t = 0) at h
      rw [hpencil x y] at h
      exact h
    obtain hQ | hW :=
      linearMatrixPencil_zeroTangentBlock_or_normalKernel_global
        A C r t hpoint'
    · refine ⟨M, r, t, hM, hM1, hM2, hrt, Or.inl ?_⟩
      intro x y
      change B x y 1 1 = 0 ∧ B x y 1 2 = 0 ∧ B x y 2 2 = 0
      rw [hpencil x y]
      exact hQ x y
    · refine ⟨M, r, t, hM, hM1, hM2, hrt, Or.inr ?_⟩
      intro x y
      change B x y 0 1 * r + B x y 0 2 * t = 0
      rw [hpencil x y]
      exact hW x y
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
