import HC4.Polynomial.RankThreeCubicDetOneSubTwoMixedOriginOrTriple
import HC4.Polynomial.RankThreeCubicAdaptedPlaneLinearVanishing
import HC4.Polynomial.RankThreeCubicLinearPoleFrame
import Mathlib.Tactic

/-!
# An affine unit on a linear pole plane has no tangential linear part

Over a field K, let p(y)=ell·y be a nonzero homogeneous linear
equation defining a plane, and let f(y)=c+gamma·y.
If the class of f in K[y]/(p) is invertible, then p divides the
linear polynomial gamma·y.

Indeed evaluation at every point of the pole plane descends
through the quotient, so f cannot vanish there. If gamma·z were
nonzero at any point z of the plane, scaling that point by
t=-c/(gamma·z) would make f(tz)=0, a contradiction. Therefore
gamma annihilates the whole plane; the existing adapted-frame
divisibility lemma converts this into exact polynomial divisibility.

This is a purely algebraic statement; no source endpoint
assumption or rank condition is added.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- Evaluating a quotient unit at any K-rational point of the
pole plane gives a nonzero scalar. -/
theorem poleQuotient_unit_eval_ne_zero
    (p f : B3 K) (z : Fin 3 → K)
    (hpz : MvPolynomial.aeval z p = 0)
    (hf : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) f)) :
    MvPolynomial.aeval z f ≠ 0 := by
  classical
  let ev : B3 K →+* K := (MvPolynomial.aeval z).toRingHom
  have hkill : ∀ x : B3 K, x ∈ Ideal.span {p} → ev x = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
    rw [ha, map_mul, show ev p = 0 from hpz, zero_mul]
  let evQ : (B3 K ⧸ Ideal.span {p}) →+* K :=
    Ideal.Quotient.lift (Ideal.span {p}) ev hkill
  have hunit : IsUnit (ev f) := by
    have h := hf.map evQ
    simpa only [Ideal.Quotient.lift_mk] using h
  exact isUnit_iff_ne_zero.mp hunit

/-- A homogeneous linear polynomial scales linearly under
simultaneous scaling of all transverse coordinates. -/
theorem transverseLinearForm_eval_smul
    (gamma : Fin 3 → K) (z : Fin 3 → K) (t : K) :
    MvPolynomial.aeval (fun i => t * z i)
      (∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i)) =
    t * MvPolynomial.aeval z
      (∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i)) := by
  simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- If c+gamma·y is invertible on the pole plane ell·y=0,
then gamma·y is divisible by the pole equation as a
polynomial in the original transverse variables. -/
theorem linearPole_affineUnit_implies_linearPart_dvd
    (p : B3 K) (ell gamma : Fin 3 → K) (c : K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {p})
      (MvPolynomial.C c +
        ∑ i : Fin 3,
          (MvPolynomial.X i : B3 K) *
            MvPolynomial.C (gamma i)))) :
    p ∣ (∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i)) := by
  classical
  let P : B3 K :=
    ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i)
  let f : B3 K := MvPolynomial.C c + P
  obtain ⟨M, hM, hM1, hM2⟩ :=
    exists_invertible_frame_annihilating_linearFunctional ell hell
  have hvanish (u v : K) :
      MvPolynomial.aeval (M.mulVec ![(0 : K), u, v]) P = 0 := by
    let z : Fin 3 → K := M.mulVec ![(0 : K), u, v]
    have hpz : MvPolynomial.aeval z p = 0 := by
      rw [polynomialLinearForm_evaluation_dot p ell hpoly z,
        frame_linearFunctional_at]
      simp [hM1, hM2]
    by_contra hd
    let d : K := MvPolynomial.aeval z P
    have hd0 : d ≠ 0 := hd
    let t : K := -c / d
    let tz : Fin 3 → K := fun i => t * z i
    have hptz : MvPolynomial.aeval tz p = 0 := by
      rw [hpoly]
      change MvPolynomial.aeval tz
        (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
          MvPolynomial.C (ell i)) = 0
      rw [show tz = (fun i => t * z i) from rfl,
        transverseLinearForm_eval_smul ell z t]
      rw [← hpoly, hpz, mul_zero]
    have hPtz : MvPolynomial.aeval tz P = t * d :=
      transverseLinearForm_eval_smul gamma z t
    have hct : c + t * d = 0 := by
      dsimp [t]
      field_simp [hd0]
      ring
    have hftz : MvPolynomial.aeval tz f = 0 := by
      change MvPolynomial.aeval tz (MvPolynomial.C c + P) = 0
      rw [map_add, MvPolynomial.aeval_C, hPtz]
      exact hct
    exact (poleQuotient_unit_eval_ne_zero p f tz hptz hunit) hftz
  have h1 : MvPolynomial.aeval
      (M.mulVec ![(0 : K), 1, 0]) P = 0 := hvanish 1 0
  have h2 : MvPolynomial.aeval
      (M.mulVec ![(0 : K), 0, 1]) P = 0 := hvanish 0 1
  change p ∣ P
  exact adaptedFrame_linearForm_dvd_of_tangentColumns_zero
    p ell gamma hpoly hell M hM hM1 hM2 h1 h2

end
end HC4.Polynomial.RankThreeCubic
