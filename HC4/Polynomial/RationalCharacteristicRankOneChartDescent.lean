import HC4.Polynomial.RationalCharacteristicRankOneRadial
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Descent of the normalized rational Euler equation to the source chart

The evaluation kernel at x/y is divisible by y T - x. Substitution
x = T y annihilates that factor in the polynomial chart ring.
This avoids constructing a separate rational function field
isomorphism. The actual chart polynomial relation follows from
self-adjointness and a normalized parameter factorization.

The last coefficient extraction from this polynomial relation is
separate from the descent proved here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev T (K : Type*) [Field K] := _root_.Polynomial (B K)

/-- The two distinct coordinate variables are relatively prime.
The elementary degree proof avoids needing an irreducibility API. -/
theorem rankOne_normalizedParameter_isRelPrime :
    IsRelPrime (X (0 : Fin 3) : B K) (X (1 : Fin 3)) := by
  classical
  intro d hd0 hd1
  obtain ⟨a, ha⟩ := hd0
  obtain ⟨b, hb⟩ := hd1
  have hd : d ≠ 0 := by
    intro hz
    apply MvPolynomial.X_ne_zero (R := K) (0 : Fin 3)
    rw [ha, hz, zero_mul]
  have ha0 : a ≠ 0 := by
    intro hz
    apply MvPolynomial.X_ne_zero (R := K) (0 : Fin 3)
    rw [ha, hz, mul_zero]
  have hdeg : d.totalDegree + a.totalDegree = 1 := by
    rw [← totalDegree_mul_of_isDomain hd ha0, ← ha, totalDegree_X]
  by_cases hzero : d.totalDegree = 0
  · exact (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
      ⟨isUnit_iff_ne_zero.mpr (by
        intro hc
        apply hd
        rw [totalDegree_eq_zero_iff_eq_C.mp hzero, hc, map_zero]), hzero⟩
  · have haz : a.totalDegree = 0 := by omega
    have hau : IsUnit a := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
      ⟨isUnit_iff_ne_zero.mpr (by
        intro hc
        apply ha0
        rw [totalDegree_eq_zero_iff_eq_C.mp haz, hc, map_zero]), haz⟩
    obtain ⟨v, hv⟩ := hau
    have hx : (X (0 : Fin 3) : B K) ∣ X (1 : Fin 3) := by
      refine ⟨(↑v⁻¹ : B K) * b, ?_⟩
      rw [hb, ha, ← hv, mul_assoc, ← mul_assoc (↑v : B K),
        Units.mul_inv, one_mul]
    have h := (MvPolynomial.X_dvd_X.mp hx)
    exact ((by decide : (0 : Fin 3) ≠ 1) h).elim

/-- The polynomial substitution x = T y, y = y, z = z, with
the chart parameter represented by X 0 in the target ring. -/
def rankOne_normalizedChart : B K →ₐ[K] B K :=
  MvPolynomial.aeval ![X 0 * X 1, X 1, X 2]

/-- The extended chart substitution also replaces the independent
time indeterminate by the target chart parameter. -/
def rankOne_normalizedChartTime : T K →+* B K :=
  _root_.Polynomial.eval₂RingHom
    (rankOne_normalizedChart (K := K)).toRingHom (X 0)

theorem rankOne_normalizedChartTime_C (p : B K) :
    rankOne_normalizedChartTime (_root_.Polynomial.C p) =
      rankOne_normalizedChart p := by
  change (_root_.Polynomial.C p).eval₂
    (rankOne_normalizedChart (K := K)).toRingHom (X 0) = _
  rw [_root_.Polynomial.eval₂_C] <;> rfl

theorem rankOne_normalizedChartTime_X :
    rankOne_normalizedChartTime (K := K) _root_.Polynomial.X = X 0 := by
  exact _root_.Polynomial.eval₂_X _ _

/-- Every polynomial relation at the rational normalized parameter
descends to an exact polynomial relation in the actual chart. -/
theorem rankOne_normalizedChartTime_zero_of_eval_zero
    (P : T K)
    (hP : P.eval₂ (algebraMap (B K) (E K))
      (rankOne_normalizedParameter (K := K)) = 0) :
    rankOne_normalizedChartTime P = 0 := by
  have hq : (X (1 : Fin 3) : B K) ≠ 0 := MvPolynomial.X_ne_zero _
  have hd := rationalParameter_linear_dvd_of_eval_zero
    (X (0 : Fin 3) : B K) (X (1 : Fin 3)) hq
    rankOne_normalizedParameter_isRelPrime P hP
  obtain ⟨R, hR⟩ := hd
  have hfactor : rankOne_normalizedChartTime
      (_root_.Polynomial.C (X (1 : Fin 3) : B K) * _root_.Polynomial.X -
        _root_.Polynomial.C (X (0 : Fin 3))) = 0 := by
    rw [map_sub, map_mul, rankOne_normalizedChartTime_C,
      rankOne_normalizedChartTime_X, rankOne_normalizedChartTime_C]
    simp [rankOne_normalizedChart, mul_comm]
  rw [hR, map_mul, hfactor, zero_mul]

/-- Evaluating a scalar parameter polynomial after embedding its
coefficients into the source polynomial ring is the same as
evaluating it by the ground-field algebra map. -/
private theorem rankOne_parameter_eval_map
    (U : _root_.Polynomial K) (t : E K) :
    (U.map (MvPolynomial.C : K →+* B K)).eval₂
      (algebraMap (B K) (E K)) t =
        U.eval₂ (algebraMap K (E K)) t := by
  induction U using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
    rw [_root_.Polynomial.map_add, _root_.Polynomial.eval₂_add,
      _root_.Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
    rw [_root_.Polynomial.map_monomial, _root_.Polynomial.eval₂_monomial,
      _root_.Polynomial.eval₂_monomial]
    have h : algebraMap (B K) (E K) (MvPolynomial.C a) =
        algebraMap K (E K) a :=
      (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    rw [h]

/-- Evaluation of the trace polynomial is precisely the source
gradient contracted with the evaluated parameter vector. -/
theorem rankOne_tracePolynomial_eval_normalized
    (f : B K) (U : Fin 3 → _root_.Polynomial K) :
    (rankOne_tracePolynomial f U).eval₂ (algebraMap (B K) (E K))
      (rankOne_normalizedParameter (K := K)) =
      ∑ i : Fin 3, (U i).eval₂ (algebraMap K (E K))
        (rankOne_normalizedParameter (K := K)) *
          algebraMap (B K) (E K) (pderiv i f) := by
  unfold rankOne_tracePolynomial
  rw [_root_.Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C,
    rankOne_parameter_eval_map, mul_comm]

variable [CharZero K]

/-- Self-adjointness and a normalized rank-one parameter factorization
give the exact polynomial chart Euler equation. -/
theorem rankOne_normalized_chartEuler_zero
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K)
    (hN : ∀ i j, N i j =
      (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N) :
    rankOne_normalizedChartTime (rankOne_tracePolynomial (transverseEuler f - f) U) = 0 := by
  apply rankOne_normalizedChartTime_zero_of_eval_zero
  rw [rankOne_tracePolynomial_eval_normalized]
  exact rankOne_normalized_eulerGradient_zero f N
    (fun i => (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter) hN hself

end
end HC4.Polynomial.RankThreeCubic
