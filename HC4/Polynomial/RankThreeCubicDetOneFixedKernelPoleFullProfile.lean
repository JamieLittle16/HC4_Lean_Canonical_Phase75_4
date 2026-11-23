import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePoleLowJetSquareOrTriple
import HC4.Polynomial.RankThreeCubicDetOneSourceMixedAffineDegrees
import Mathlib.Tactic

/-!
# The actual fixed-kernel pole has constant full longitudinal response

Let p be the genuine linear denominator pole, q the reduction
K[y] → K[y]/(p), and w a constant transverse direction.

Suppose the cubic full source Hessian annihilates (0,w) modulo p,
the quadratic transverse rows annihilate w modulo p, and the
quadratic mixed longitudinal source row paired with w is
divisible by p.

The strictly subquadratic source remainder has NO transverse
Hessian and has a constant mixed directional response g.
Therefore the full source Hessian, not merely its leading part,
has on the genuine pole plane:

  Hess(F)_(yy) * w = 0,
  Hess(F)_(xy) · w = g  (a genuine scalar in K).

These are precisely the identities needed to compare the full
determinant-one Hessian at three scaled points of the pole plane.
This theorem makes no claim that the remaining transverse-repair
or triple branches are contradictory.
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

theorem sourceCubic_fixedPoleKernel_fullHessian_scalarResponse
    (F : SB K) (a : K) (p : B3 K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (w : Fin 3 → K) :
    let L3 : SB K := initialForm transverseCubicWeight 3 F
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let Rlow : SB K := (F - L3) - L2
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A := φ.mapMatrix (hessian L3)
    let C := φ.mapMatrix (hessian L2)
    let B := φ.mapMatrix (hessian F)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    let flow : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w j)
    A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) →
    p ∣ (∑ j : Fin 3,
      referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
        MvPolynomial.C (w j)) →
    (∀ i : Fin 3, (B *ᵥ v) (.inr i) = 0) ∧
      (B *ᵥ v) (.inl ()) = q (MvPolynomial.C (flow.coeff 0)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let D : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian Rlow)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  let flow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w j)
  change A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) → _ → _
  intro hAker hCrows hdvd
  have hF : F = L3 + L2 + Rlow := by
    dsimp [Rlow, L3, L2]
    ring
  have hdecomp : B = A + C + D := by
    ext i j
    change φ (hessian F i j) =
      φ (hessian L3 i j) + φ (hessian L2 i j) +
        φ (hessian Rlow i j)
    rw [hF]
    simp only [hessian_apply, map_add]
  have hDtrans (i j : Fin 3) :
      D (.inr i) (.inr j) = 0 := by
    change φ (hessian Rlow (.inr i) (.inr j)) = 0
    have hz : hessian Rlow (.inr i) (.inr j) = 0 := by
      change hessian
        ((F - initialForm transverseCubicWeight 3 F) -
          initialForm transverseCubicWeight 2 F)
        (.inr i) (.inr j) = 0
      rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
      exact sourceCubic_belowTwo_transverseHessian_zero F hcap i j
    rw [hz]
    simp
  have hDrows (i : Fin 3) : (D *ᵥ v) (.inr i) = 0 := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v,
      hDtrans]
  have hCmix : (C *ᵥ v) (.inl ()) = 0 := by
    let f2 : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
          MvPolynomial.C (w j)
    have hqf : q f2 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr hdvd)
    have hresp : (C *ᵥ v) (.inl ()) = q f2 := by
      simp [C, v, W, f2, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, φ, q, map_sum, map_mul]
    rw [hresp]
    exact hqf
  have hc : flow = MvPolynomial.C (flow.coeff 0) :=
    sourceCubic_subTwo_mixedDirectional_eq_C F hcap a w
  have hDmix : (D *ᵥ v) (.inl ()) =
      q (MvPolynomial.C (flow.coeff 0)) := by
    have hresp : (D *ᵥ v) (.inl ()) = q flow := by
      simp [D, v, W, flow, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, φ, q, map_sum, map_mul]
    rw [hresp, hc]
  have hBmul : B *ᵥ v = A *ᵥ v + C *ᵥ v + D *ᵥ v := by
    rw [hdecomp, Matrix.add_mulVec, Matrix.add_mulVec]
  have hArows (i : Fin 3) : (A *ᵥ v) (.inr i) = 0 :=
    congrFun hAker (.inr i)
  have hAlong : (A *ᵥ v) (.inl ()) = 0 :=
    congrFun hAker (.inl ())
  constructor
  · intro i
    have hi := congrFun hBmul (.inr i)
    simpa only [Pi.add_apply, hArows i, hCrows i,
      hDrows i, Pi.zero_apply, zero_add] using hi
  · have hi := congrFun hBmul (.inl ())
    simpa only [Pi.add_apply, hAlong, hCmix,
      hDmix, Pi.zero_apply, zero_add] using hi

end
end HC4.Polynomial.RankThreeCubic
