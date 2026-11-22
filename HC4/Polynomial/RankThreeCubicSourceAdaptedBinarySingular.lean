import HC4.Polynomial.RankThreeCubicAdaptedNormalCofactor
import HC4.Polynomial.RankThreeCubicSourceFinalRankTwoObstruction
import Mathlib.Tactic

/-!
# Actual source double pole: binary tangential Hessian degeneracy

The source cubic's exact-double-versus-triple classification gives,
in the exactly-double branch, a homogeneous linear pole p=ell·y
whose normal ell annihilates all adjugate columns modulo p.

Choose an invertible frame M with columns 1 and 2 in ker ell,
using the source-derived adapted-frame construction. Evaluating
the normal cofactor divisibility at y=M(0,u,v), and applying the
algebraic adjugate congruence identity, yields

  adj(Mᵀ H(M(0,u,v)) M)(0,0) = 0

for every u,v in K.

This is the full source-to-binary-Hessian transfer: the binary
tangential Hessian is singular everywhere on the actual pole
plane, rather than an assumed coordinate plane. The source
alternative is retained: there may instead be an exact scalar
triple determinant factor.

No additional rank or kernel geometry is assumed.
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

/-- A pole-normal annihilation modulo a homogeneous linear p
becomes a vanishing principal cofactor throughout an invertibly
adapted coordinate plane. This is the polynomial evaluation
bridge, independent of the underlying source. -/
theorem normalAdjugate_divisible_adaptedPlaneCofactor_zero
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (hnormal : ∀ j : Fin 3,
      p ∣ (∑ i : Fin 3,
        MvPolynomial.C (ell i) * H.adjugate i j))
    (u v : K) :
    (M.transpose *
        H.map (MvPolynomial.aeval (M.mulVec ![(0 : K), u, v])).toRingHom *
        M).adjugate 0 0 = 0 := by
  classical
  let w : Fin 3 → K := ![(0 : K), u, v]
  let x : Fin 3 → K := M.mulVec w
  let ev : B3 K →+* K := (MvPolynomial.aeval x).toRingHom
  have hplane : (∑ i : Fin 3, ell i * x i) = 0 := by
    have h1 := hM1
    have h2 := hM2
    simp only [Fin.sum_univ_three] at h1 h2
    dsimp [x, w]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination u * h1 + v * h2
  have hpx : ev p = 0 := by
    calc
      ev p = ev (∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i)) :=
          congrArg ev hpoly
      _ = ∑ i : Fin 3, ell i * x i := by
          simp only [map_sum, map_mul, MvPolynomial.aeval_X,
            MvPolynomial.aeval_C]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 0 := hplane
  have hmap : (H.map ev).adjugate = H.adjugate.map ev :=
    (ev.map_adjugate H).symm
  have hzero (j : Fin 3) :
      (∑ i : Fin 3, ell i * (H.map ev).adjugate i j) = 0 := by
    obtain ⟨z, hz⟩ := hnormal j
    have heval :
        ev (∑ i : Fin 3,
          MvPolynomial.C (ell i) * H.adjugate i j) = 0 := by
      rw [hz, map_mul, hpx, zero_mul]
    rw [hmap]
    simpa only [map_sum, map_mul, MvPolynomial.aeval_C,
      Matrix.map_apply] using heval
  exact tangentFrame_normalAdjugate_principal_zero
    (H.map ev) M ell hell hM hM1 hM2 hzero

/-- The actual cubic source characteristic is linear, or the
genuine principal rank-two pole has either an exact scalar
triple determinant factor or an invertible frame in which
the binary tangential Hessian has identically vanishing
determinant on the pole plane. -/
theorem sourceCubic_genuineRankTwo_adaptedBinarySingular_or_exactTriple
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
      ((∃ M : Matrix (Fin 3) (Fin 3) K,
          M.det ≠ 0 ∧
          (∑ i : Fin 3, ell i * M i 1) = 0 ∧
          (∑ i : Fin 3, ell i * M i 2) = 0 ∧
          (∀ x y : K,
            (M.transpose *
                H.map
                  (MvPolynomial.aeval (M.mulVec ![(0 : K), x, y])).toRingHom *
                M).adjugate 0 0 = 0))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
  obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_exactDoubleNormal_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hsplit with ⟨c, hfactor, hc0, hnpc, hnormal⟩ | htriple
  · left
    have hell : ell ≠ 0 := by
      intro he
      apply hp.ne_zero
      rw [hpoly, he]
      simp
    obtain ⟨M, hM, hM1, hM2⟩ :=
      exists_invertible_frame_annihilating_linearFunctional ell hell
    refine ⟨M, hM, hM1, hM2, ?_⟩
    intro x y
    exact normalAdjugate_divisible_adaptedPlaneCofactor_zero
      H p ell hpoly hell M hM hM1 hM2 hnormal x y
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
