import HC4.Polynomial.RankThreeCubicSourceFullKernelPole
import Mathlib.Tactic

/-!
# Four-row source cubic Hessian kernel at the actual repeated pole

The previous source theorem constructs a fixed nonzero transverse
tangent direction W on the true pole plane of the cubic source.
Its three transverse Hessian rows and the additional longitudinal
mixed-Hessian row all annihilate W modulo the genuine reduced-
denominator prime.

Here we assemble these FOUR rows into a single full 4x4 Hessian
kernel for the actual cubic initial form, at the chosen longitudinal
slice and modulo that same prime. The vector has longitudinal
coordinate zero and transverse coordinates W.

This is not a kernel of the Hessian of the ORIGINAL source F:
lower transverse-weight layers can repair it. The next proof must
apply the determinant-one condition to constrain that repair.
The exact scalar triple-pole case stays explicit.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

/-- Assemble the longitudinal mixed row and all transverse rows
into the kernel of a full four-by-four matrix. The longitudinal
entry of the vector is zero, so the upper-left Hessian entry is
irrelevant to this purely algebraic implication. -/
theorem fourHessian_zeroLongitudinalVector_of_rows
    {R : Type*} [CommRing R]
    (A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (W : Fin 3 → R)
    (hmixed : (∑ j : Fin 3, A (.inl ()) (.inr j) * W j) = 0)
    (htrans : ∀ i : Fin 3,
      (∑ j : Fin 3, A (.inr i) (.inr j) * W j) = 0) :
    A *ᵥ (Sum.elim (fun _ : Unit => (0 : R)) W) = 0 := by
  classical
  funext i
  cases i with
  | inl u =>
      cases u
      simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Finset.sum_const_zero, mul_zero, zero_add,
        Sum.elim_inr, Sum.elim_inl] using hmixed
  | inr i =>
      simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Finset.sum_const_zero, mul_zero, zero_add,
        Sum.elim_inr, Sum.elim_inl] using htrans i

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The same actual source characteristic that yields a rank-two
genuine pole produces either a fixed tangent kernel for the FULL
four-variable cubic Hessian modulo p, or an exact nonzero scalar
triple factor of the transverse Hessian determinant.

The nontriple branch retains an invertible frame with nonzero
tangent vector; no new rank, isotropy or source assumption
is introduced. -/
theorem sourceCubic_genuinePole_fourHessianFixedTangent_or_exactTriple
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
    let L := initialForm transverseCubicWeight 3 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) :=
      fun i j => q (referenceSlice a (pderiv j (pderiv i L)))
    (∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q (MvPolynomial.C
          ((M.mulVec ![(0 : K), r, t]) j))
      C *ᵥ (Sum.elim (fun _ : Unit => 0) W) = 0)
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      (sourceTransverseHessian a L).det =
        MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
      (B3 K ⧸ Ideal.span {p}) :=
    fun i j => q (referenceSlice a (pderiv j (pderiv i L)))
  obtain ⟨ell, k, hpoly, hk, hbranch⟩ :=
    sourceCubic_genuinePole_fullHessianFixedTangent_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  rcases hbranch with
      ⟨M, r, t, s, T, hM, hM1, hM2, hrt,
        hframe, hps, hscale, hSk, hcross, hWdiv⟩ | htriple
  · left
    let W : Fin 3 → B3 K ⧸ Ideal.span {p} :=
      fun j => q (MvPolynomial.C
        ((M.mulVec ![(0 : K), r, t]) j))
    have hell : ell ≠ 0 := by
      intro he
      apply hp.ne_zero
      rw [hpoly, he]
      simp
    have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
      sourceCubic_transverseHessian_homogeneous_one a F i j
    have hWker : (H.map q) *ᵥ W = 0 :=
      homogeneousLinearMatrix_fixedTangentKernel_modPole
        H hhom p ell hpoly hell M hM hM1 hM2 r t hframe
    have hmixed : (∑ j : Fin 3,
        C (.inl ()) (.inr j) * W j) = 0 := by
      have hz : q (∑ j : Fin 3,
          referenceSlice a (pderiv (.inr j) (pderiv (.inl ()) L)) *
            MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr hWdiv)
      simpa only [C, W, map_sum, map_mul] using hz
    have htrans (i : Fin 3) :
        (∑ j : Fin 3, C (.inr i) (.inr j) * W j) = 0 := by
      have hh := congrFun hWker i
      simpa only [Matrix.mulVec, dotProduct, C,
        sourceTransverseHessian] using hh
    refine Or.inl ⟨M, r, t, hM, hrt, ?_⟩
    exact fourHessian_zeroLongitudinalVector_of_rows C W hmixed htrans
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
