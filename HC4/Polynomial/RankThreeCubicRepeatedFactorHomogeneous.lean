import HC4.Polynomial.RankThreeCubicDegreeOneAffineEuler
import Mathlib.Tactic

/-!
# A repeated linear factor of a homogeneous cubic passes through the origin

Suppose D = p²*c is homogeneous of degree three and both p,c
have total degree one. Applying the Euler operator yields

  p * (2*C(p.coeff 0)*c + C(c.coeff 0)*p) = 0.

The factor p is nonzero, and evaluation at the origin forces
the constant coefficient of c to vanish if that of p is nonzero.
The same Euler relation would then give c=0, a contradiction.

Hence p has zero constant term and its canonical degree-one
affine representation is actually a homogeneous linear form.
This uses the *actual factorisation* and no artificial choice
of pole coordinates.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

private def euler3 (P : B3 K) : B3 K :=
  ∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i P

private theorem euler3_mul (P Q : B3 K) :
    euler3 (P * Q) = euler3 P * Q + P * euler3 Q := by
  classical
  unfold euler3
  simp only [pderiv_mul]
  calc
    (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
      (pderiv i P * Q + P * pderiv i Q)) =
      ∑ i : Fin 3,
        (((MvPolynomial.X i : B3 K) * pderiv i P) * Q +
          P * ((MvPolynomial.X i : B3 K) * pderiv i Q)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i : Fin 3,
          ((MvPolynomial.X i : B3 K) * pderiv i P) * Q) +
        (∑ i : Fin 3,
          P * ((MvPolynomial.X i : B3 K) * pderiv i Q)) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i P) * Q +
          P * (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i Q) := by
            rw [Finset.sum_mul, Finset.mul_sum]

/-- A nonzero homogeneous cubic cannot have a repeated affine-linear
factor whose hyperplane misses the origin. -/
theorem homogeneousCubic_repeatedDegreeOneFactor_constantCoeff_zero
    (D p c : B3 K)
    (hDhom : D.IsHomogeneous 3)
    (hfact : D = (p * p) * c)
    (hp0 : p ≠ 0)
    (hc0 : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1) :
    p.coeff 0 = 0 := by
  classical
  have hpEuler : euler3 p = p - MvPolynomial.C (p.coeff 0) :=
    degreeOne_affineEuler p hpdeg
  have hcEuler : euler3 c = c - MvPolynomial.C (c.coeff 0) :=
    degreeOne_affineEuler c hcdeg
  have hDEuler : euler3 D = (3 : B3 K) * D := by
    have h := hDhom.sum_X_mul_pderiv
    simpa only [euler3, nsmul_eq_mul] using h
  have heq :
      (3 : B3 K) * ((p * p) * c) =
        ((p - MvPolynomial.C (p.coeff 0)) * p +
          p * (p - MvPolynomial.C (p.coeff 0))) * c +
        (p * p) * (c - MvPolynomial.C (c.coeff 0)) := by
    have hD : euler3 ((p * p) * c) = (3 : B3 K) * ((p * p) * c) := by
      simpa only [hfact] using hDEuler
    calc
      (3 : B3 K) * ((p * p) * c) = euler3 ((p * p) * c) := hD.symm
      _ = (euler3 (p * p)) * c + (p * p) * euler3 c := euler3_mul _ _
      _ = ((euler3 p) * p + p * euler3 p) * c +
          (p * p) * euler3 c := by rw [euler3_mul]
      _ = ((p - MvPolynomial.C (p.coeff 0)) * p +
          p * (p - MvPolynomial.C (p.coeff 0))) * c +
          (p * p) * (c - MvPolynomial.C (c.coeff 0)) := by
            rw [hpEuler, hcEuler]
  have hmul :
      p * ((2 : B3 K) * MvPolynomial.C (p.coeff 0) * c +
        MvPolynomial.C (c.coeff 0) * p) = 0 := by
    calc
      _ = (3 : B3 K) * ((p * p) * c) -
        (((p - MvPolynomial.C (p.coeff 0)) * p +
          p * (p - MvPolynomial.C (p.coeff 0))) * c +
          (p * p) * (c - MvPolynomial.C (c.coeff 0))) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  have hrelation :
      (2 : B3 K) * MvPolynomial.C (p.coeff 0) * c +
        MvPolynomial.C (c.coeff 0) * p = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hp0
  by_contra ha
  have hrelation0 :
      (2 : K) * p.coeff 0 * c.coeff 0 +
        c.coeff 0 * p.coeff 0 = 0 := by
    have h := congrArg
      (fun P : B3 K => (MvPolynomial.constantCoeff : B3 K →+* K) P)
      hrelation
    simpa only [map_add, map_mul, map_zero, map_ofNat,
      MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_eq]
      using h
  have hab : p.coeff 0 * c.coeff 0 = 0 := by
    have hthree : (3 : K) * (p.coeff 0 * c.coeff 0) = 0 := by
      calc
        (3 : K) * (p.coeff 0 * c.coeff 0) =
            (2 : K) * p.coeff 0 * c.coeff 0 +
              c.coeff 0 * p.coeff 0 := by ring
        _ = 0 := hrelation0
    exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)
  have hb : c.coeff 0 = 0 := (mul_eq_zero.mp hab).resolve_left ha
  have hcvanish : c = 0 := by
    have hrel := hrelation
    rw [hb, map_zero, zero_mul, add_zero] at hrel
    have htwo : (2 : B3 K) * MvPolynomial.C (p.coeff 0) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (MvPolynomial.C_ne_zero.mpr ha)
    exact (mul_eq_zero.mp hrel).resolve_left htwo
  exact hc0 hcvanish

/-- The repeated factor is a homogeneous linear form in the actual
transverse variables, with its nonzero coefficient vector derived
from its degree and nonvanishing. -/
theorem homogeneousCubic_repeatedDegreeOneFactor_linearForm
    (D p c : B3 K)
    (hDhom : D.IsHomogeneous 3)
    (hfact : D = (p * p) * c)
    (hp0 : p ≠ 0)
    (hc0 : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1) :
    ∃ ell : Fin 3 → K,
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      ell ≠ 0 := by
  classical
  let ell : Fin 3 → K := fun i => (pderiv i p).coeff 0
  have hzero : p.coeff 0 = 0 :=
    homogeneousCubic_repeatedDegreeOneFactor_constantCoeff_zero
      D p c hDhom hfact hp0 hc0 hpdeg hcdeg
  have hlinear : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) := by
    have hrepr := degreeOne_affineRepresentation p hpdeg
    simpa only [hzero, map_zero, zero_add] using hrepr
  refine ⟨ell, hlinear, ?_⟩
  intro hz
  apply hp0
  rw [hlinear, hz]
  simp


/-- The complementary degree-one factor is homogeneous linear too.
Once p(0)=0, the cubic Euler identity forces c(0)=0. -/
theorem homogeneousCubic_repeatedDegreeOneFactor_cofactorConstantCoeff_zero
    (D p c : B3 K)
    (hDhom : D.IsHomogeneous 3)
    (hfact : D = (p * p) * c)
    (hp0 : p ≠ 0)
    (hc0 : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1) :
    c.coeff 0 = 0 := by
  classical
  have hpc : p.coeff 0 = 0 :=
    homogeneousCubic_repeatedDegreeOneFactor_constantCoeff_zero
      D p c hDhom hfact hp0 hc0 hpdeg hcdeg
  have hpEuler : euler3 p = p := by
    have h := degreeOne_affineEuler p hpdeg
    simpa only [hpc, map_zero, sub_zero] using h
  have hcEuler : euler3 c = c - MvPolynomial.C (c.coeff 0) :=
    degreeOne_affineEuler c hcdeg
  have hDEuler : euler3 ((p * p) * c) =
      (3 : B3 K) * ((p * p) * c) := by
    have h := hDhom.sum_X_mul_pderiv
    have he : euler3 D = (3 : B3 K) * D := by
      simpa only [euler3, nsmul_eq_mul] using h
    simpa only [hfact] using he
  rw [euler3_mul, euler3_mul, hpEuler, hcEuler] at hDEuler
  have hprod : (p * p) * MvPolynomial.C (c.coeff 0) = 0 := by
    linear_combination -hDEuler
  have hp2 : p * p ≠ 0 := mul_ne_zero hp0 hp0
  have hC : MvPolynomial.C (c.coeff 0) = (0 : B3 K) :=
    (mul_eq_zero.mp hprod).resolve_left hp2
  exact MvPolynomial.C_eq_zero.mp hC

/-- The complementary cofactor has a genuine homogeneous linear
coordinate representation, derived from the repeated cubic
Hessian factorisation rather than assumed. -/
theorem homogeneousCubic_repeatedDegreeOneFactor_cofactorLinearForm
    (D p c : B3 K)
    (hDhom : D.IsHomogeneous 3)
    (hfact : D = (p * p) * c)
    (hp0 : p ≠ 0)
    (hc0 : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1) :
    ∃ gamma : Fin 3 → K,
      c = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i) := by
  classical
  let gamma : Fin 3 → K := fun i => (pderiv i c).coeff 0
  have hzero : c.coeff 0 = 0 :=
    homogeneousCubic_repeatedDegreeOneFactor_cofactorConstantCoeff_zero
      D p c hDhom hfact hp0 hc0 hpdeg hcdeg
  refine ⟨gamma, ?_⟩
  have hrepr := degreeOne_affineRepresentation c hcdeg
  simpa only [hzero, map_zero, zero_add] using hrepr

end
end HC4.Polynomial.RankThreeCubic
