import HC4.Polynomial.RankThreeCubicSourceFixedBinaryKernel
import HC4.Polynomial.RankThreeCubicTangentKernelExtension
import Mathlib.Tactic

/-!
# Exactly-double source pole: full tangent kernel or zero binary block

The actual cubic source supplies an invertible adapted frame and
a single nonzero kernel (r,t) of the tangential binary Hessian
at *every* point of its pole plane. Its normal-adjugate divisibility
also makes the entire normal adjugate row vanish there.

The elementary 3x3 extension lemma now gives, at each point
of the actual source pole plane, the alternative:

* the entire binary tangential Hessian block vanishes; or
* the same fixed tangent vector (0,r,t) belongs to the kernel
  of the full 3x3 Hessian at that point.

This is a source-honest pointwise dichotomy, not a claim that
the zero-block case is impossible or that the choice is uniform
over the entire plane. Those are subsequent rigidity questions.

The exact scalar triple determinant pole is retained separately.
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

/-- A genuine source cubic double pole has a fixed nonzero
binary kernel that either extends to the full Hessian or
encounters an entirely zero tangential block at each point.
The frame and pole are both derived from the actual source. -/
theorem sourceCubic_genuineRankTwo_fullKernelOrZeroBinaryPointwise_or_triple
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
          (∀ x y : K,
            let B := M.transpose *
              H.map (MvPolynomial.aeval
                (M.mulVec ![(0 : K), x, y])).toRingHom * M
            (B 1 1 * r + B 1 2 * t = 0) ∧
              (B 2 1 * r + B 2 2 * t = 0)) ∧
          ∀ x y : K,
            let B := M.transpose *
              H.map (MvPolynomial.aeval
                (M.mulVec ![(0 : K), x, y])).toRingHom * M
            (B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0) ∨
              (B 0 1 * r + B 0 2 * t = 0))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_fixedBinaryKernel_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hsplit with ⟨M, r, t, hM, hM1, hM2, hrt, hrow, hker⟩ | htriple
  · left
    refine ⟨M, r, t, hM, hM1, hM2, hrt, hker, ?_⟩
    intro x y
    let w : Fin 3 → K := M.mulVec ![(0 : K), x, y]
    let ev : B3 K →+* K := (MvPolynomial.aeval w).toRingHom
    let A : Matrix (Fin 3) (Fin 3) K := H.map ev
    let B : Matrix (Fin 3) (Fin 3) K := M.transpose * A * M
    have hSymH : H.IsSymm := sourceTransverseHessian_isSymm a L
    have hSymA : A.IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      change ev (H j i) = ev (H i j)
      exact congrArg ev (hSymH.apply i j)
    have hSymB : B.IsSymm := by
      change B.transpose = B
      dsimp [B]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        hSymA, Matrix.mul_assoc]
    have h01 : B.adjugate 0 1 = 0 := hrow x y 1
    have h02 : B.adjugate 0 2 = 0 := hrow x y 2
    have hq := hker x y
    have hq1 : B 1 1 * r + B 1 2 * t = 0 := hq.1
    have hq2 : B 2 1 * r + B 2 2 * t = 0 := hq.2
    exact symmetricThree_tangentKernel_full_or_tangentBlockZero
      B hSymB h01 h02 r t hq1 hq2
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
