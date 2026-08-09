import HC4.RationalRigidity.RankThreeReducedTarget
import HC4.Polynomial.AutonomousODEQuadraticRigidity
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Monomial
import Mathlib.Tactic

/-!
# Infinity certificate for the logarithmic source

The autonomous lemma in the manuscript uses, for

    rho = E(phi) / phi,    E = X d/dX,

that if `D = deg phi > 0`, then

    rho(infinity) = D,     eta(infinity) = 0,

where `eta = E(rho)`.

This file replaces those asymptotic statements by exact degree and leading-
coefficient identities for Mathlib's canonical reduced fraction

    rho = N / Q.

The key facts are:

* `deg(E phi) = deg phi` in characteristic zero when `deg phi > 0`;
* the reduced numerator and denominator of `rho` have equal degree;
* their leading-coefficient ratio is exactly `deg phi`;
* the reduced numerator `(E N) Q - N (E Q)` for `eta` has vanishing
  coefficient in the would-be top degree `2 deg Q`, hence degree strictly
  below `2 deg Q` when the reduced source denominator has positive degree.

The last section also records the rank-three endpoint identity saying that a
singular logarithmic core with `eta = 0` forces the raw autonomous numerator
to vanish at that endpoint value.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Positive-degree Euler differentiation preserves natural degree. -/
theorem natDegree_eulerDerivative_eq_of_pos
    (phi : Polynomial K) (hdeg : 0 < phi.natDegree) :
    (HC4.Polynomial.eulerDerivative phi).natDegree = phi.natDegree := by
  have hphi : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have htop : phi.coeff phi.natDegree ≠ 0 := by
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  have hcast : (phi.natDegree : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdeg)
  apply le_antisymm (HC4.Polynomial.natDegree_eulerDerivative_le phi)
  by_contra hnot
  have hlt : (HC4.Polynomial.eulerDerivative phi).natDegree < phi.natDegree :=
    Nat.lt_of_not_ge hnot
  have hzero :
      (HC4.Polynomial.eulerDerivative phi).coeff phi.natDegree = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [HC4.Polynomial.coeff_eulerDerivative] at hzero
  exact (mul_ne_zero hcast htop) hzero

/-- Leading coefficient of `E(phi)` at positive degree. -/
theorem leadingCoeff_eulerDerivative_eq_of_pos
    (phi : Polynomial K) (hdeg : 0 < phi.natDegree) :
    (HC4.Polynomial.eulerDerivative phi).leadingCoeff =
      (phi.natDegree : K) * phi.leadingCoeff := by
  have hEdeg := natDegree_eulerDerivative_eq_of_pos phi hdeg
  change
    (HC4.Polynomial.eulerDerivative phi).coeff
        (HC4.Polynomial.eulerDerivative phi).natDegree =
      (phi.natDegree : K) * phi.coeff phi.natDegree
  rw [hEdeg, HC4.Polynomial.coeff_eulerDerivative]

/-- For positive-degree `phi`, the canonical reduced numerator and denominator
of `rho = E(phi)/phi` have the same natural degree. -/
theorem logarithmicSource_num_natDegree_eq_denom
    (phi : Polynomial K) (hdeg : 0 < phi.natDegree) :
    (logarithmicSourceNumerator phi).natDegree =
      (logarithmicSourceDenominator phi).natDegree := by
  have hphi : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hEdeg := natDegree_eulerDerivative_eq_of_pos phi hdeg
  have hE : HC4.Polynomial.eulerDerivative phi ≠ 0 := by
    intro hzero
    have : (HC4.Polynomial.eulerDerivative phi).natDegree = 0 := by
      rw [hzero]
      simp
    rw [hEdeg] at this
    omega
  have hQ : logarithmicSourceDenominator phi ≠ 0 :=
    logarithmicSource_denominator_ne_zero phi
  have hcross := logarithmicSource_cross_identity phi hphi
  have hNphi : logarithmicSourceNumerator phi * phi ≠ 0 := by
    rw [hcross]
    exact mul_ne_zero hE hQ
  have hN : logarithmicSourceNumerator phi ≠ 0 := by
    intro hzero
    apply hNphi
    simp [hzero]
  have hdegCross := congrArg Polynomial.natDegree hcross
  rw [Polynomial.natDegree_mul hN hphi,
    Polynomial.natDegree_mul hE hQ, hEdeg] at hdegCross
  omega

/-- The leading coefficient of the canonical reduced numerator of `rho` is
`deg(phi)` because the canonical denominator is monic. -/
theorem logarithmicSource_numerator_leadingCoeff_eq_natDegree
    (phi : Polynomial K) (hdeg : 0 < phi.natDegree) :
    (logarithmicSourceNumerator phi).leadingCoeff = (phi.natDegree : K) := by
  have hphi : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hcross := logarithmicSource_cross_identity phi hphi
  have hlc := congrArg Polynomial.leadingCoeff hcross
  simp only [Polynomial.leadingCoeff_mul] at hlc
  have hElc := leadingCoeff_eulerDerivative_eq_of_pos phi hdeg
  have hQlc : (logarithmicSourceDenominator phi).leadingCoeff = 1 := by
    exact logarithmicSource_denominator_monic phi
  rw [hElc, hQlc, mul_one] at hlc
  have hphilc : phi.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hphi
  apply mul_right_cancel₀ hphilc
  calc
    (logarithmicSourceNumerator phi).leadingCoeff * phi.leadingCoeff =
        (phi.natDegree : K) * phi.leadingCoeff := hlc

/-- Exact algebraic version of the manuscript statement
`rho(infinity) = deg phi`. -/
theorem logarithmicSource_rationalInfinityValue_eq_natDegree
    (phi : Polynomial K) (hdeg : 0 < phi.natDegree) :
    rationalInfinityValue
        (logarithmicSourceNumerator phi)
        (logarithmicSourceDenominator phi) =
      (phi.natDegree : K) := by
  have hND := logarithmicSource_num_natDegree_eq_denom phi hdeg
  have hNlc := logarithmicSource_numerator_leadingCoeff_eq_natDegree phi hdeg
  have hQlc : (logarithmicSourceDenominator phi).leadingCoeff = 1 := by
    exact logarithmicSource_denominator_monic phi
  unfold rationalInfinityValue
  have hcoeff :
      (logarithmicSourceNumerator phi).coeff
          (logarithmicSourceDenominator phi).natDegree =
        (logarithmicSourceNumerator phi).leadingCoeff := by
    rw [← hND]
    rfl
  rw [hcoeff, hNlc, hQlc, div_one]

/-- Generic top-coefficient cancellation for the reduced logarithmic
numerator `(E N)D - N(E D)` when `N` and `D` have the same positive degree. -/
theorem coeff_two_degree_reducedLogarithmicEtaNumerator_eq_zero
    {N D : Polynomial K}
    (hN : N ≠ 0) (hD : D ≠ 0)
    (hdegEq : N.natDegree = D.natDegree)
    (hdegPos : 0 < D.natDegree) :
    (reducedLogarithmicEtaNumerator N D).coeff
        (D.natDegree + D.natDegree) = 0 := by
  have hNpos : 0 < N.natDegree := by simpa [hdegEq] using hdegPos
  have hENdeg := natDegree_eulerDerivative_eq_of_pos N hNpos
  have hEDdeg := natDegree_eulerDerivative_eq_of_pos D hdegPos
  have hENtop := leadingCoeff_eulerDerivative_eq_of_pos N hNpos
  have hEDtop := leadingCoeff_eulerDerivative_eq_of_pos D hdegPos

  have hleft := Polynomial.coeff_mul_degree_add_degree
    (HC4.Polynomial.eulerDerivative N) D
  have hright := Polynomial.coeff_mul_degree_add_degree
    N (HC4.Polynomial.eulerDerivative D)
  change
    (HC4.Polynomial.eulerDerivative N * D).coeff
        ((HC4.Polynomial.eulerDerivative N).natDegree + D.natDegree) =
      (HC4.Polynomial.eulerDerivative N).leadingCoeff * D.leadingCoeff at hleft
  change
    (N * HC4.Polynomial.eulerDerivative D).coeff
        (N.natDegree + (HC4.Polynomial.eulerDerivative D).natDegree) =
      N.leadingCoeff * (HC4.Polynomial.eulerDerivative D).leadingCoeff at hright
  rw [hENdeg, hdegEq] at hleft
  rw [hEDdeg, hdegEq] at hright
  unfold reducedLogarithmicEtaNumerator
  rw [Polynomial.coeff_sub, hleft, hright, hENtop, hEDtop]
  rw [hdegEq]
  ring

/-- Degree form of `eta(infinity)=0`: the reduced eta numerator has degree
strictly smaller than the square of the reduced source denominator. -/
theorem logarithmicSourceEtaNumerator_natDegree_lt_two_denom
    (phi : Polynomial K)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    (logarithmicSourceEtaNumerator phi).natDegree <
      (logarithmicSourceDenominator phi).natDegree +
        (logarithmicSourceDenominator phi).natDegree := by
  let N := logarithmicSourceNumerator phi
  let D := logarithmicSourceDenominator phi
  have hD : D ≠ 0 := by
    simpa [D] using logarithmicSource_denominator_ne_zero phi
  have hdegEq : N.natDegree = D.natDegree := by
    -- Positive degree of the reduced denominator already implies `phi` has
    -- positive degree because `D ∣ phi`.
    have hdvd : D ∣ phi := by
      simpa [D] using logarithmicSource_denominator_dvd phi
    have hphi : phi ≠ 0 := by
      intro hzero
      subst phi
      simp [D, logarithmicSourceDenominator, canonicalReducedDenominator,
        polynomialPairRatFunc, HC4.Polynomial.eulerDerivative] at hSourceDegree
    have hphiDeg : 0 < phi.natDegree := by
      by_contra hnot
      have hphi0 : phi.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
      have hDle : D.natDegree ≤ phi.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hphi
      rw [hphi0] at hDle
      have hDpos : 0 < D.natDegree := by
        simpa [D] using hSourceDegree
      exact (Nat.not_lt_of_ge hDle) hDpos
    simpa [N, D] using logarithmicSource_num_natDegree_eq_denom phi hphiDeg
  have hN : N ≠ 0 := by
    intro hzero
    have : N.natDegree = 0 := by rw [hzero]; simp
    rw [hdegEq] at this
    rw [this] at hSourceDegree
    simp at hSourceDegree

  have htop :
      (reducedLogarithmicEtaNumerator N D).coeff
          (D.natDegree + D.natDegree) = 0 :=
    coeff_two_degree_reducedLogarithmicEtaNumerator_eq_zero
      hN hD hdegEq (by simpa [D] using hSourceDegree)

  have hENdeg : (HC4.Polynomial.eulerDerivative N).natDegree = D.natDegree := by
    rw [natDegree_eulerDerivative_eq_of_pos N]
    · exact hdegEq
    · simpa [hdegEq, D] using hSourceDegree
  have hEDdeg : (HC4.Polynomial.eulerDerivative D).natDegree = D.natDegree :=
    natDegree_eulerDerivative_eq_of_pos D (by simpa [D] using hSourceDegree)
  have hEN : HC4.Polynomial.eulerDerivative N ≠ 0 := by
    intro hzero
    have hz : (HC4.Polynomial.eulerDerivative N).natDegree = 0 := by
      rw [hzero]
      simp
    rw [hENdeg] at hz
    rw [hz] at hSourceDegree
    simp at hSourceDegree
  have hED : HC4.Polynomial.eulerDerivative D ≠ 0 := by
    intro hzero
    have hz : (HC4.Polynomial.eulerDerivative D).natDegree = 0 := by
      rw [hzero]
      simp
    rw [hEDdeg] at hz
    rw [hz] at hSourceDegree
    simp at hSourceDegree

  have hmulLeft :
      (HC4.Polynomial.eulerDerivative N * D).natDegree =
        D.natDegree + D.natDegree := by
    rw [Polynomial.natDegree_mul hEN hD, hENdeg]
  have hmulRight :
      (N * HC4.Polynomial.eulerDerivative D).natDegree =
        D.natDegree + D.natDegree := by
    rw [Polynomial.natDegree_mul hN hED, hdegEq, hEDdeg]

  have hle :
      (reducedLogarithmicEtaNumerator N D).natDegree ≤
        D.natDegree + D.natDegree := by
    unfold reducedLogarithmicEtaNumerator
    exact
      (Polynomial.natDegree_sub_le_iff_left (le_of_eq hmulRight)).2
        (le_of_eq hmulLeft)

  have hDpos : 0 < D.natDegree := by
    simpa [D] using hSourceDegree
  have htwoPos : 0 < D.natDegree + D.natDegree := by
    omega
  have hne :
      (reducedLogarithmicEtaNumerator N D).natDegree ≠
        D.natDegree + D.natDegree := by
    intro heq
    have hp : reducedLogarithmicEtaNumerator N D ≠ 0 := by
      intro hp0
      have hzeroDeg :
          (reducedLogarithmicEtaNumerator N D).natDegree = 0 := by
        rw [hp0]
        simp
      rw [heq] at hzeroDeg
      exact (Nat.ne_of_gt htwoPos) hzeroDeg
    have htopNe :
        (reducedLogarithmicEtaNumerator N D).coeff
            (reducedLogarithmicEtaNumerator N D).natDegree ≠ 0 := by
      change (reducedLogarithmicEtaNumerator N D).leadingCoeff ≠ 0
      exact (Polynomial.leadingCoeff_ne_zero).2 hp
    rw [heq] at htopNe
    exact htopNe htop
  have hlt :
      (reducedLogarithmicEtaNumerator N D).natDegree <
        D.natDegree + D.natDegree :=
    lt_of_le_of_ne hle hne
  simpa [logarithmicSourceEtaNumerator, N, D] using hlt

/-- At an endpoint where the rank-three logarithmic core is singular with
`eta = 0`, the raw autonomous numerator vanishes.  This is the endpoint
counterpart of the infinity certificate. -/
theorem rankThreeEtaNumerator_eq_zero_of_endpoint_core_det_zero
    {v2 v3 v4 w1 w2 w3 w4 rho : K}
    (hdet :
      (HC4.Polynomial.rankThreeLogHessianCore
        v2 v3 v4 w1 w2 w3 w4 rho 0).det = 0) :
    HC4.Polynomial.rankThreeEtaNumerator
      v2 v3 v4 w1 w2 w3 w4 rho = 0 := by
  rw [HC4.Polynomial.det_rankThreeLogHessianCore] at hdet
  simpa using hdet

/-- Polynomial-evaluation form of the preceding endpoint identity. -/
theorem rankThreeEtaNumeratorPolynomial_eval_eq_zero_of_endpoint_core_det_zero
    {v2 v3 v4 w1 w2 w3 w4 rho : K}
    (hdet :
      (HC4.Polynomial.rankThreeLogHessianCore
        v2 v3 v4 w1 w2 w3 w4 rho 0).det = 0) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      v2 v3 v4 w1 w2 w3 w4).eval rho = 0 := by
  rw [HC4.Polynomial.eval_rankThreeEtaNumeratorPolynomial]
  exact rankThreeEtaNumerator_eq_zero_of_endpoint_core_det_zero hdet

end

end HC4.RationalRigidity
