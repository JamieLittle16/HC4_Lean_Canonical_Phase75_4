import HC4.Valuation.AdaptiveAlignedSmithVerticalEndpoint
import HC4.Polynomial.RankThreeVerticalMomentRealisation
import HC4.Polynomial.AutonomousODEQuadraticRigidity
import HC4.Polynomial.ComplementaryEdgeRigidity
import Mathlib.Tactic

/-!
# A18.5.17: the positive vertical rank-three branch is impossible

For the vertical direction `w=(1,0,0,0)` the rank-three autonomous rational
function simplifies before any denominator-removal argument.  Writing

    J = b + c + d,

we have

    D(rho) = b c d (1-J)

and

    N(rho)/D(rho) = rho + rho^2/(J-1).

If `b,c,d > 0`, then `J >= 3`.  Hence the quadratic coefficient is the
positive reciprocal `1/(J-1)`, exactly the terminal case already ruled out by
`no_quadraticAutonomous_positive_reciprocal`.

This closes the vertical route outright: a nonconstant honest vertical line
with positive transverse exponents cannot have zero Hessian determinant.
No abstract rank-three terminal certificate is needed for this special case.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Explicit numerator of the vertical rank-three autonomous target. -/
theorem rankThreeEtaNumerator_vertical
    (B C D rho : K) :
    HC4.Polynomial.rankThreeEtaNumerator
        B C D 1 0 0 0 rho =
      B * C * D * rho * (1 - (B + C + D) - rho) := by
  simp [HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum]
  ring

/-- Explicit denominator of the vertical rank-three autonomous target. -/
theorem rankThreeEtaDenominator_vertical
    (B C D rho : K) :
    HC4.Polynomial.rankThreeEtaDenominator
        B C D 1 0 0 0 rho =
      B * C * D * (1 - (B + C + D)) := by
  simp [HC4.Polynomial.rankThreeEtaDenominator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    HC4.Polynomial.rankThreeWeightedCofactorSum,
    HC4.Polynomial.rankThreeDirectionDefect]
  ring

/-- The vertical fraction-core equation is precisely the positive-reciprocal
quadratic autonomous logarithmic ODE. -/
theorem quadraticAutonomousLogODE_of_vertical_core_det_zero
    {b c d : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphi : phi ≠ 0)
    (hcore :
      HC4.Polynomial.RankThreeFractionCoreDetZero
        phi (b : K) (c : K) (d : K) 1 0 0 0) :
    HC4.Polynomial.QuadraticAutonomousLogODE
      (1 / (((b + c + d : ℕ) : K) - 1)) 1 phi := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p : F := ι phi
  let E : F := ι (HC4.Polynomial.eulerDerivative phi)
  let A : F := ι (HC4.Polynomial.logarithmicEtaNumerator phi)
  let B : F := ι (Polynomial.C (b : K))
  let C : F := ι (Polynomial.C (c : K))
  let D : F := ι (Polynomial.C (d : K))
  let rho : F := E / p
  let eta : F := A / p ^ 2

  have hp : p ≠ 0 := by
    dsimp [p]
    exact RatFunc.algebraMap_ne_zero hphi

  have hB : B ≠ 0 := by
    dsimp [B]
    apply RatFunc.algebraMap_ne_zero
    simp
    exact_mod_cast (Nat.ne_of_gt hb)
  have hC : C ≠ 0 := by
    dsimp [C]
    apply RatFunc.algebraMap_ne_zero
    simp
    exact_mod_cast (Nat.ne_of_gt hc)
  have hD : D ≠ 0 := by
    dsimp [D]
    apply RatFunc.algebraMap_ne_zero
    simp
    exact_mod_cast (Nat.ne_of_gt hd)
  have hBCD : B * C * D ≠ 0 :=
    mul_ne_zero (mul_ne_zero hB hC) hD

  let J : ℕ := b + c + d
  have hJ : 2 ≤ J := by
    dsimp [J]
    omega
  have hJm1 : 0 < J - 1 := by omega
  have hLK : ((J : K) - 1) ≠ 0 := by
    have hNat : (J - 1 : ℕ) ≠ 0 := Nat.ne_of_gt hJm1
    have hcast : (((J - 1 : ℕ) : K)) ≠ 0 := by exact_mod_cast hNat
    have hJone : 1 ≤ J := by omega
    have heq : (((J - 1 : ℕ) : K)) = (J : K) - 1 := by
      exact_mod_cast (Nat.sub_add_cancel hJone).symm
    simpa [heq] using hcast

  let L : F := B + C + D - 1
  have hLmap :
      L = ι (Polynomial.C ((J : K) - 1)) := by
    dsimp [L, B, C, D, J, ι]
    simp
    congr 1
    push_cast
    ring
  have hL : L ≠ 0 := by
    rw [hLmap]
    apply RatFunc.algebraMap_ne_zero
    simp [hLK]

  have hEq :=
    HC4.Polynomial.rankThree_fraction_equation_of_core_det_zero hcore
  have hEq' :
      HC4.Polynomial.rankThreeEtaNumerator
          B C D 1 0 0 0 rho =
        eta *
          HC4.Polynomial.rankThreeEtaDenominator
            B C D 1 0 0 0 rho := by
    simpa [HC4.Polynomial.RankThreeFractionEquation,
      F, ι, p, E, A, B, C, D, rho, eta] using hEq

  rw [rankThreeEtaNumerator_vertical,
    rankThreeEtaDenominator_vertical] at hEq'

  have hsmall :
      rho * (1 - (B + C + D) - rho) =
        eta * (1 - (B + C + D)) := by
    apply mul_left_cancel₀ hBCD
    calc
      (B * C * D) * (rho * (1 - (B + C + D) - rho)) =
          B * C * D * rho * (1 - (B + C + D) - rho) := by ring
      _ = eta * (B * C * D * (1 - (B + C + D))) := hEq'
      _ = (B * C * D) * (eta * (1 - (B + C + D))) := by ring

  have hrel : eta * L = rho * L + rho ^ 2 := by
    dsimp [L]
    linear_combination -hsmall

  have heta : eta = rho + rho ^ 2 / L := by
    calc
      eta = (rho * L + rho ^ 2) / L := by
        apply (eq_div_iff hL).2
        exact hrel
      _ = rho + rho ^ 2 / L := by
        field_simp [hL]
        <;> ring

  let qK : K := 1 / ((J : K) - 1)
  have hqmap :
      ι (Polynomial.C qK) = (1 : F) / L := by
    dsimp [qK]
    rw [hLmap]
    simp [ι]
    field_simp [hLK]

  have heta' :
      eta = rho + ι (Polynomial.C qK) * rho ^ 2 := by
    rw [heta, hqmap]
    ring

  have hAeq : A = ι (Polynomial.C qK) * E ^ 2 + p * E := by
    calc
      A = (A / p ^ 2) * p ^ 2 := by
        symm
        exact div_mul_cancel₀ A (pow_ne_zero 2 hp)
      _ = (rho + ι (Polynomial.C qK) * rho ^ 2) * p ^ 2 := by
        rw [← heta']
        rfl
      _ = ι (Polynomial.C qK) * E ^ 2 + p * E := by
        dsimp [rho]
        field_simp [hp]
        <;> ring

  apply RatFunc.algebraMap_injective K
  change
    A = ι
      (Polynomial.C qK * (HC4.Polynomial.eulerDerivative phi) ^ 2 +
        Polynomial.C 1 *
          HC4.Polynomial.logarithmicEtaOverRhoDenominator phi)
  simp only [map_add, map_mul, map_pow]
  unfold HC4.Polynomial.logarithmicEtaOverRhoDenominator
  dsimp [A, E, p]
  rw [hAeq]
  ring

/-- A singular positive vertical line is impossible as soon as its coefficient
polynomial is nonconstant and has nonzero constant term. -/
theorem rankThreeVertical_hessian_impossible
    {b c d : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdeg : 0 < phi.natDegree)
    (hconst : phi.coeff 0 ≠ 0)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) = 0) : False := by
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hconst
  have hcore :
      HC4.Polynomial.RankThreeFractionCoreDetZero
        phi (b : K) (c : K) (d : K) 1 0 0 0 :=
    HC4.Polynomial.rankThreeFractionCoreDetZero_of_vertical_hessianDeterminant_zero
      hphi hdet
  have hode :=
    quadraticAutonomousLogODE_of_vertical_core_det_zero
      hb hc hd hphi hcore

  have hnonconstant : phi ≠ Polynomial.C (phi.coeff 0) := by
    intro heq
    have hzeroDeg : phi.natDegree = 0 := by
      rw [heq]
      simp
    omega
  rcases HC4.Polynomial.exists_positive_tail_factorisation
      (K := K) hnonconstant with
    ⟨m, q, hm, hq0, hphiEq⟩
  rw [hphiEq] at hode

  let J : ℕ := b + c + d
  have hJ : 2 ≤ J := by
    dsimp [J]
    omega
  exact HC4.Polynomial.no_quadraticAutonomous_positive_reciprocal
    (K := K) (B := (1 : K)) (c := phi.coeff 0)
    (q := q) (m := m) (J := J)
    hm hJ hconst hq0 (by simpa [J] using hode)

/-- The nonzero constant coefficient is itself forced by singularity, so a
nonconstant positive vertical line can never be Hessian-degenerate. -/
theorem rankThreeVertical_hessian_impossible_of_nonconstant
    {b c d : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphi : phi ≠ 0)
    (hdeg : 0 < phi.natDegree)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) = 0) : False := by
  have hconst : phi.coeff 0 ≠ 0 :=
    HC4.Valuation.rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
      hb hc hd hphi hdet
  exact rankThreeVertical_hessian_impossible hb hc hd hdeg hconst hdet

end

end HC4.RationalRigidity
