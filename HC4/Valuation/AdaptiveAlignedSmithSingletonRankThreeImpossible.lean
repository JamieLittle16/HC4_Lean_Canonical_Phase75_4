import HC4.Valuation.AdaptiveAlignedSmithSingletonRankThreeTerminal
import HC4.Polynomial.AutonomousODEQuadraticRigidity
import HC4.Polynomial.ComplementaryEdgeRigidity
import Mathlib.Tactic

/-!
# A18.5.16: positive singular singleton Smith fibres are impossible

The vertical rank-three branch is stronger than a terminal certificate.
For

    F = x₁^b x₂^c x₃^d φ(x₀),      b,c,d > 0,

its rank-three logarithmic direction is `(1,0,0,0)`.  The universal rational
formula of `RankThreeLogHessian` then collapses to

    denominator = b c d (1 - b - c - d),
    numerator   = b c d ρ (1 - b - c - d - ρ).

Hence, writing `J=b+c+d`, singularity gives the *quadratic* autonomous ODE

    η = ρ + ρ²/(J-1).

But `J >= 3`.  The existing autonomous-ODE rigidity theorem
`no_quadraticAutonomous_positive_reciprocal` proves that a nonconstant
polynomial with nonzero constant term cannot satisfy exactly this equation.

A18.5.14 already showed that zero Hessian forces the constant term to be
nonzero, and a first longitudinal departure supplies nonconstancy.  Therefore
a positive singleton Smith fibre with first departure is contradictory.  No
algebraic closure, pole removal, or terminal classification is needed in this
vertical case.
-/

namespace HC4.Polynomial

noncomputable section

/-- Raw rank-three numerator in the vertical direction. -/
theorem rankThreeEtaNumerator_vertical
    {R : Type*} [CommRing R]
    (b c d rho : R) :
    rankThreeEtaNumerator b c d 1 0 0 0 rho =
      b * c * d * rho * (1 - b - c - d - rho) := by
  simp [rankThreeEtaNumerator, rankThreeLogProduct, rankThreeLogSum]
  ring

/-- Raw rank-three denominator in the vertical direction.  The apparent
`rho` dependence cancels identically. -/
theorem rankThreeEtaDenominator_vertical
    {R : Type*} [CommRing R]
    (b c d rho : R) :
    rankThreeEtaDenominator b c d 1 0 0 0 rho =
      b * c * d * (1 - b - c - d) := by
  simp [rankThreeEtaDenominator, rankThreeLogProduct, rankThreeLogSum,
    rankThreeWeightedCofactorSum, rankThreeDirectionDefect]
  ring

/-- Pure field algebra for the vertical fraction equation. -/
theorem rankThree_vertical_fraction_equation_clears
    {F : Type*} [Field F]
    {p E A b c d : F}
    (hp : p ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hJ : b + c + d - 1 ≠ 0)
    (hEq :
      rankThreeEtaNumerator b c d 1 0 0 0 (E / p) =
        (A / p^2) * rankThreeEtaDenominator b c d 1 0 0 0 (E / p)) :
    A = (1 / (b + c + d - 1)) * E^2 + p * E := by
  rw [rankThreeEtaNumerator_vertical,
    rankThreeEtaDenominator_vertical] at hEq
  have hBCD : b * c * d ≠ 0 := mul_ne_zero (mul_ne_zero hb hc) hd
  have hfactored :
      (b * c * d) *
          ((E / p) * (1 - b - c - d - E / p)) =
        (b * c * d) *
          ((A / p^2) * (1 - b - c - d)) := by
    calc
      (b * c * d) *
          ((E / p) * (1 - b - c - d - E / p)) =
        b * c * d * (E / p) * (1 - b - c - d - E / p) := by ring
      _ = (A / p^2) * (b * c * d * (1 - b - c - d)) := hEq
      _ = (b * c * d) *
          ((A / p^2) * (1 - b - c - d)) := by ring
  have hcancel :
      (E / p) * (1 - b - c - d - E / p) =
        (A / p^2) * (1 - b - c - d) :=
    mul_left_cancel₀ hBCD hfactored
  field_simp [hp] at hcancel
  field_simp [hJ]
  linear_combination hcancel

/-- A vertical rank-three fraction equation descends to the exact polynomial
quadratic autonomous log-ODE. -/
theorem quadraticAutonomousLogODE_of_rankThreeVerticalFractionEquation
    {K : Type*} [Field K]
    {phi : Polynomial K} {b c d : K}
    (hphi : phi ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hJ : b + c + d - 1 ≠ 0)
    (hEq : RankThreeFractionEquation phi b c d 1 0 0 0) :
    QuadraticAutonomousLogODE (1 / (b + c + d - 1)) 1 phi := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hp : ι phi ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr hphi
  have hbR : ι (Polynomial.C b) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr
      (Polynomial.C_ne_zero.mpr hb)
  have hcR : ι (Polynomial.C c) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr
      (Polynomial.C_ne_zero.mpr hc)
  have hdR : ι (Polynomial.C d) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr
      (Polynomial.C_ne_zero.mpr hd)
  have hJR :
      ι (Polynomial.C b) + ι (Polynomial.C c) + ι (Polynomial.C d) - 1 ≠ 0 := by
    have hmap : ι (Polynomial.C (b + c + d - 1)) ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff).not.mpr
        (Polynomial.C_ne_zero.mpr hJ)
    simpa [map_add, map_sub] using hmap
  have hfrac :
      rankThreeEtaNumerator
          (ι (Polynomial.C b)) (ι (Polynomial.C c)) (ι (Polynomial.C d))
          1 0 0 0 (ι (eulerDerivative phi) / ι phi) =
        (ι (logarithmicEtaNumerator phi) / (ι phi)^2) *
          rankThreeEtaDenominator
            (ι (Polynomial.C b)) (ι (Polynomial.C c)) (ι (Polynomial.C d))
            1 0 0 0 (ι (eulerDerivative phi) / ι phi) := by
    simpa [RankThreeFractionEquation, F, ι] using hEq
  have hclear :=
    rankThree_vertical_fraction_equation_clears
      (F := F)
      (p := ι phi)
      (E := ι (eulerDerivative phi))
      (A := ι (logarithmicEtaNumerator phi))
      (b := ι (Polynomial.C b))
      (c := ι (Polynomial.C c))
      (d := ι (Polynomial.C d))
      hp hbR hcR hdR hJR hfrac
  unfold QuadraticAutonomousLogODE
  apply IsFractionRing.injective (Polynomial K) F
  have hcoef :
      ι (Polynomial.C (1 / (b + c + d - 1))) =
        1 /
          (ι (Polynomial.C b) + ι (Polynomial.C c) +
            ι (Polynomial.C d) - 1) := by
    let κ : K →+* F := ι.comp Polynomial.C
    change κ (1 / (b + c + d - 1)) =
      1 / (κ b + κ c + κ d - 1)
    simp only [div_eq_mul_inv, one_mul, map_inv₀, map_add, map_sub, map_one]
  rw [map_add, map_mul, map_pow]
  rw [hcoef]
  simp only [map_one, map_mul]
  unfold logarithmicEtaOverRhoDenominator
  simp only [map_mul]
  simpa [mul_comm] using hclear

/-- **Vertical rank-three rigidity.**  A positive rank-three vertical line
with nonzero constant term and nonconstant coefficient polynomial cannot have
zero four-dimensional Hessian determinant. -/
theorem rankThreeVertical_hessian_impossible_of_nonconstant
    {K : Type*} [Field K] [CharZero K]
    {b c d : ℕ} {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hnonconstant : phi ≠ Polynomial.C (phi.coeff 0))
    (hdet : hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    False := by
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphi0
  have hcore :=
    rankThreeFractionCoreDetZero_of_vertical_hessianDeterminant_zero
      (K := K) (b := b) (c := c) (d := d) (phi := phi) hphi hdet
  have hEq := rankThree_fraction_equation_of_core_det_zero hcore
  have hbK : (b : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hJnat : 2 ≤ b + c + d := by omega
  have hJne : b + c + d ≠ 1 := by omega
  have hJK : ((b + c + d : ℕ) : K) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hJne
  have hode :
      QuadraticAutonomousLogODE
        (1 / (((b + c + d : ℕ) : K) - 1)) 1 phi := by
    have hJsep : (b : K) + (c : K) + (d : K) - 1 ≠ 0 := by
      simpa [Nat.cast_add] using hJK
    have hodeSep :=
      quadraticAutonomousLogODE_of_rankThreeVerticalFractionEquation
        hphi hbK hcK hdK hJsep hEq
    simpa [Nat.cast_add] using hodeSep
  rcases exists_positive_tail_factorisation
      (K := K) (phi := phi) hnonconstant with
    ⟨m, q, hm, hq0, hphiEq⟩
  have hode' :
      QuadraticAutonomousLogODE
        (1 / (((b + c + d : ℕ) : K) - 1)) 1
        (Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q) := by
    rw [← hphiEq]
    exact hode
  exact no_quadraticAutonomous_positive_reciprocal
    (K := K) (B := (1 : K))
    (m := m) (J := b + c + d)
    hm hJnat hphi0 hq0 hode'

end

end HC4.Polynomial

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A first longitudinal departure makes a positive singular vertical line
impossible; A18.5.14 supplies the formerly separate constant-term condition. -/
theorem positiveVertical_supportPair_hessian_impossible
    {b c d n q : ℕ} {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hq : 0 < q)
    (hn : phi.coeff n ≠ 0)
    (hnq : phi.coeff (n + q) ≠ 0)
    (hdet : hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    False := by
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hn
  have hphi0 : phi.coeff 0 ≠ 0 :=
    rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
      hb hc hd hphi hdet
  have hpos : 0 < n + q := by omega
  have hnonconstant : phi ≠ Polynomial.C (phi.coeff 0) :=
    nonconstant_of_positive_coeff_ne_zero (K := K) hpos hnq
  exact rankThreeVertical_hessian_impossible_of_nonconstant
    hb hc hd hphi0 hnonconstant hdet

/-- **Positive singular singleton Smith fibres with first departure do not
exist.**  This is the direct Newton-facing contradiction. -/
theorem positive_singletonSmithFiber_impossible
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
    (hdeparture : HasFirstExactSmithExponentLongitudinalDeparture F e)
    (hdet :
      hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0) :
    False := by
  rcases hdeparture with ⟨n, q, hq, hn, hnq, hbefore⟩
  have hvertical :
      hessianDeterminant
        (rankThreeVerticalPolynomial e.b e.c e.d
          (longitudinalCoefficientPolynomial e.b e.c e.d F)) = 0 := by
    rw [← smithSubfacePolynomial_singleton_eq_rankThreeVerticalPolynomial F e]
    exact hdet
  exact positiveVertical_supportPair_hessian_impossible
    hb hc hd hq hn hnq hvertical

end

end HC4.Valuation
