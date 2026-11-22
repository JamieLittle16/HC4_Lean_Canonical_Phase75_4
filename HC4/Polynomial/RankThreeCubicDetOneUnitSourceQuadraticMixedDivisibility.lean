import HC4.Polynomial.RankThreeCubicDetOneSourceMixedAffineDegrees
import Mathlib.Tactic

/-!
# A unit longitudinal repair forces the quadratic mixed row along
# the fixed cubic kernel to be divisible by the genuine pole

This theorem brings the affine-unit plane lemma back to the
ORIGINAL source polynomial F.

Let L3 and L2 be its actual transverse weight-three and
weight-two parts, and Rlow=F-L3-L2. For a constant transverse
vector w0, the longitudinal Hessian response decomposes into:
  f3(y): homogeneous quadratic, from L3;
  f2(y): homogeneous linear, from L2;
  flow: constant, from Rlow.

If the reduced full cubic Hessian kills (0,w0), then q(f3)=0.
If the full Hessian response is a unit in the pole quotient,
q(f2+flow) is a unit. The affine-unit divisibility theorem
therefore gives p | f2.

This source-level statement is conditional on the *existing*
fixed-kernel and longitudinal-unit facts. It adds no endpoint
assumption asserting an independently chosen repair.
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

/-- A source-derived fixed cubic kernel with a *unit*
longitudinal full-Hessian repair forces its homogeneous-linear
quadratic mixed response to vanish on the entire pole plane. -/
theorem sourceCubic_unitLongitudinal_implies_secondLayer_mixed_dvd
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (w0 : Fin 3 → K) :
    let L3 := initialForm transverseCubicWeight 3 F
    let L2 := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    (φ.mapMatrix (hessian L3)) *ᵥ v = 0 →
    IsUnit (((φ.mapMatrix (hessian F)) *ᵥ v) (.inl ())) →
    p ∣ (∑ j : Fin 3,
      referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w0 j))
  let v : Unit ⊕ Fin 3 → R := Sum.elim (fun _ : Unit => 0) W
  let fF : B3 K := ∑ j : Fin 3,
    referenceSlice a (hessian F (.inl ()) (.inr j)) *
      MvPolynomial.C (w0 j)
  let f3 : B3 K := ∑ j : Fin 3,
    referenceSlice a (hessian L3 (.inl ()) (.inr j)) *
      MvPolynomial.C (w0 j)
  let f2 : B3 K := ∑ j : Fin 3,
    referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
      MvPolynomial.C (w0 j)
  let flow : B3 K := ∑ j : Fin 3,
    referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
      MvPolynomial.C (w0 j)
  change A *ᵥ v = 0 →
    IsUnit ((B *ᵥ v) (.inl ())) → p ∣ f2
  intro hAker hunit
  have hfdecomp : fF = f3 + f2 + flow := by
    change
      (∑ j : Fin 3, referenceSlice a
        (hessian F (.inl ()) (.inr j)) * MvPolynomial.C (w0 j)) =
      f3 + f2 + flow
    calc
      _ = ∑ j : Fin 3,
          (referenceSlice a (hessian L3 (.inl ()) (.inr j)) +
            referenceSlice a (hessian L2 (.inl ()) (.inr j)) +
            referenceSlice a (hessian Rlow (.inl ()) (.inr j))) *
              MvPolynomial.C (w0 j) := by
          apply Finset.sum_congr rfl
          intro j _
          have hh := sourceCubic_hessian_three_two_lower_decomposition F
          have hj := congrFun (congrFun hh (.inl ())) (.inr j)
          rw [hj]
          simp only [Matrix.add_apply, map_add]
          rfl
      _ = f3 + f2 + flow := by
          simp only [add_mul, Finset.sum_add_distrib]
          rfl
  have hrespF : (B *ᵥ v) (.inl ()) = q fF := by
    simp [B, v, W, fF, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, φ, q, map_sum, map_mul]
  have hresp3 : (A *ᵥ v) (.inl ()) = q f3 := by
    simp [A, v, W, f3, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, φ, q, map_sum, map_mul]
  have hqf3 : q f3 = 0 := by
    rw [← hresp3]
    simpa only [Pi.zero_apply] using congrFun hAker (.inl ())
  have hunitF : IsUnit (q fF) := by
    rw [← hrespF]
    exact hunit
  have hunit2 : IsUnit (q (f2 + flow)) := by
    rw [hfdecomp, map_add, map_add, hqf3, zero_add] at hunitF
    simpa only [map_add] using hunitF
  have hf2hom : f2.IsHomogeneous 1 :=
    sourceCubic_secondLayer_mixedDirectional_homogeneous_one F a w0
  let gamma : Fin 3 → K := fun j => (pderiv j f2).coeff 0
  have hf2lin : f2 = ∑ j : Fin 3,
      (MvPolynomial.X j : B3 K) * MvPolynomial.C (gamma j) :=
    homogeneousOne_polynomial_linearForm f2 hf2hom
  have hflowC : flow = MvPolynomial.C (flow.coeff 0) :=
    sourceCubic_subTwo_mixedDirectional_eq_C F hcap a w0
  have haffine : IsUnit
      (q (MvPolynomial.C (flow.coeff 0) +
        ∑ j : Fin 3,
          (MvPolynomial.X j : B3 K) *
            MvPolynomial.C (gamma j))) := by
    rw [hf2lin, hflowC] at hunit2
    simpa only [add_comm] using hunit2
  have hpdiv :=
    linearPole_affineUnit_implies_linearPart_dvd
      p ell gamma (flow.coeff 0) hpoly hell haffine
  rw [hf2lin]
  exact hpdiv

end
end HC4.Polynomial.RankThreeCubic
