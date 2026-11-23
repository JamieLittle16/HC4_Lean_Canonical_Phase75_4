import HC4.Polynomial.RankThreeCubicDetOnePolePlanePointwiseHessian
import HC4.Polynomial.RankThreeCubicDetOneThreePointBorderedObstruction
import Mathlib.Tactic

/-!
# The no-transverse-repair pole forces the cubic principal cofactor
# to vanish at every rational point of its genuine pole plane

Let F be an actual source polynomial of transverse weight <=3
with det Hess(F)=1. Let p=ell·y be the genuine homogeneous
linear pole equation and w a fixed nonzero transverse direction.

Suppose the cubic full Hessian annihilates (0,w) modulo p,
the quadratic transverse correction also annihilates w
modulo p, and the mixed quadratic longitudinal correction
is divisible by p.

The full source Hessian then has a fixed transverse kernel w
and a constant longitudinal response along the pole plane.
At any z with p(z)=0, its three evaluations at 0,z,-z have
transverse blocks T,T+A(z),T-A(z), determinant one, and the
same kernel/coupling. The three-scale cofactor lemma forces
the cubic leading principal cofactor at z to vanish.

This is a POINTWISE vanishing statement, not yet the polynomial
divisibility p | adj(H3)[k,k]. That final lifting uses the fact
that p is a linear hyperplane over an infinite field.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

theorem sourceCubic_fixedPoleKernel_cubicCofactor_vanishes_on_plane
    (F : SB K) (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w : Fin 3 → K) (hw : w ≠ 0)
    (k : Fin 3) (hwk : w k ≠ 0) :
    let L3 : SB K := initialForm transverseCubicWeight 3 F
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A := φ.mapMatrix (hessian L3)
    let C := φ.mapMatrix (hessian L2)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) →
    p ∣ (∑ j : Fin 3,
      referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
        MvPolynomial.C (w j)) →
    ∀ z : Fin 3 → K, MvPolynomial.aeval z p = 0 →
      MvPolynomial.aeval z
        ((sourceTransverseHessian a L3).adjugate k k) = 0 := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let Aq : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let Cq : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  let flow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w j)
  let g : K := flow.coeff 0
  change Aq *ᵥ v = 0 →
    (∀ i : Fin 3, (Cq *ᵥ v) (.inr i) = 0) → _ → _
  intro hAker hCrows hdvd z hpz
  obtain ⟨hBqrows, hBqmix⟩ :=
    sourceCubic_fixedPoleKernel_fullHessian_scalarResponse
      F a p hcap w hAker hCrows hdvd
  let ev (y : Fin 3 → K) : SB K →+* K :=
    ((MvPolynomial.aeval y).toRingHom).comp
      (referenceSlice a).toRingHom
  let Bzero : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    (ev (fun _ => (0 : K))).mapMatrix (hessian F)
  let Bplus : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    (ev z).mapMatrix (hessian F)
  let Bminus : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    (ev (fun i => -z i)).mapMatrix (hessian F)
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (ev (fun _ => (0 : K)))
      (hessian L2 (.inr i) (.inr j))
  let H3 : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L3
  let A : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (ev z) (hessian L3 (.inr i) (.inr j))
  have hscales :=
    sourceCubic_fullTransverseHessian_threeScale F a hcap z
  obtain ⟨hT0, hTplus, hTminus⟩ := hscales
  have hlin0 : MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) p = 0 :=
    linearPole_originEval_eq_zero p ell hlin
  have hlinMinus :
      MvPolynomial.aeval (fun i => -z i) p = 0 := by
    have hzz : MvPolynomial.aeval z
        (∑ i : Fin 3,
          (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i)) = 0 := by
      simpa only [hlin] using hpz
    have hs := transverseLinearForm_eval_smul ell z (-1 : K)
    rw [hlin]
    simpa only [neg_one_mul, hzz, mul_zero] using hs
  have hprofile :
      ∀ y : Fin 3 → K, MvPolynomial.aeval y p = 0 →
        let By := (ev y).mapMatrix (hessian F)
        (∀ i : Fin 3,
          (∑ j : Fin 3, By (.inr i) (.inr j) * w j) = 0) ∧
          (∑ j : Fin 3, By (.inl ()) (.inr j) * w j) = g := by
    exact sourceHessian_fixedPoleKernel_specializes_at
      F a p w g hBqrows hBqmix
  obtain ⟨hrows0, hpair0⟩ :=
    hprofile (fun _ => (0 : K)) hlin0
  obtain ⟨hrowsPlus, hpairPlus⟩ := hprofile z hpz
  obtain ⟨hrowsMinus, hpairMinus⟩ :=
    hprofile (fun i => -z i) hlinMinus
  have hsym (y : Fin 3 → K) :
      ((ev y).mapMatrix (hessian F)).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change (ev y) (pderiv i (pderiv j F)) =
      (ev y) (pderiv j (pderiv i F))
    rw [HC4.Newton.pderiv_comm_backport i j F]
  have hdet (y : Fin 3 → K) :
      ((ev y).mapMatrix (hessian F)).det = 1 := by
    calc
      ((ev y).mapMatrix (hessian F)).det =
        (ev y) (hessian F).det :=
          (RingHom.map_det (ev y) (hessian F)).symm
      _ = 1 := by
        change (ev y) (hessianDeterminant F) = 1
        rw [hdetOne]
        simp
  have hAcof : A.adjugate k k = 0 :=
    detOne_threePoint_borderedKernel_leadingCofactor_zero
      Bzero Bplus Bminus
      (hsym (fun _ => (0 : K)))
      (hsym z)
      (hsym (fun i => -z i))
      (hdet (fun _ => (0 : K)))
      (hdet z)
      (hdet (fun i => -z i))
      T A hT0 hTplus hTminus
      w hw hrows0 hrowsPlus hrowsMinus
      g hpair0 hpairPlus hpairMinus k hwk
  let evalz : B3 K →+* K := (MvPolynomial.aeval z).toRingHom
  have hmap : (H3.map evalz).adjugate = H3.adjugate.map evalz :=
    (evalz.map_adjugate H3).symm
  have hAeq : A = H3.map evalz := rfl
  rw [hAeq, hmap] at hAcof
  exact hAcof

end
end HC4.Polynomial.RankThreeCubic
