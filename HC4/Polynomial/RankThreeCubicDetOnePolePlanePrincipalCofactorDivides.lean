import HC4.Polynomial.RankThreeCubicLinearPolePointwiseDivisibility
import Mathlib.Tactic

/-!
# Source pole-plane cofactor vanishing lifts to exact polynomial divisibility

This is the missing link between the Lean-green three-scale
pointwise theorem and polynomial divisibility. In the fixed
no-transverse-repair branch of a genuine cubic source pole,
every principal cubic cofactor indexed by a NONZERO coordinate
of the constant transverse kernel vector is divisible by p.

No generic-point assumption is substituted for actual source
evaluation; the result uses evaluation on all K-points of the
true pole plane and the linear-pole hyperplane lemma.
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

theorem sourceCubic_fixedPoleKernel_cubicPrincipalCofactor_dvd
    (F : SB K) (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
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
    p ∣ ((sourceTransverseHessian a L3).adjugate k k) := by
  classical
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
  change A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) → _ → _
  intro hAker hCrows hdvd
  apply linearPole_dvd_of_forall_pointEval_zero
    p ((sourceTransverseHessian a L3).adjugate k k)
    ell hlin hell
  intro z hpz
  exact sourceCubic_fixedPoleKernel_cubicCofactor_vanishes_on_plane
    F a p ell hlin hcap hdetOne w hw k hwk
    hAker hCrows hdvd z hpz

end
end HC4.Polynomial.RankThreeCubic
