import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurUnivariateLogDerivativeRigidity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Stage 4B21: affine-line reduction of the logarithmic-gradient residual

Stage 4B19 supplies, for the rank-one homogeneous transverse residual, a
nonzero pivot gradient component `P` and the identities

    P * ∂_j Q = Q * ∂_j P

for every other gradient component `Q` and every transverse variable `j`.
Stage 4B20 proves the corresponding one-variable rigidity theorem.

This file is the exact adapter between those two statements.  We substitute
an arbitrary affine line

    X_i = a_i + v_i T

into a ternary polynomial and prove the formal chain rule

    d/dT (F(a+vT)) = sum_i v_i (∂_i F)(a+vT).

Consequently the B19 cross identities restrict to

    p q' = q p'

on every affine line.  Whenever the pivot restriction `p` is nonzero, B20
therefore gives `q = c p` on that line.

No global proportionality is asserted here: the next stage only has to prove
that these linewise constants agree.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- Substitute the affine line `X_i = a_i + v_i T` into a ternary
multivariate polynomial. -/
def transverseAffineLineSpecialisation
    (a v : Fin 3 → K) :
    MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

@[simp] theorem transverseAffineLineSpecialisation_C
    (a v : Fin 3 → K) (c : K) :
    transverseAffineLineSpecialisation a v (MvPolynomial.C c) =
      Polynomial.C c := by
  simp [transverseAffineLineSpecialisation]

@[simp] theorem transverseAffineLineSpecialisation_X
    (a v : Fin 3 → K) (i : Fin 3) :
    transverseAffineLineSpecialisation a v (MvPolynomial.X i) =
      Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X := by
  simp [transverseAffineLineSpecialisation]

/-- Exact formal chain rule for affine-line substitution in three variables. -/
theorem derivative_transverseAffineLineSpecialisation
    (a v : Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) :
    (transverseAffineLineSpecialisation a v F).derivative =
      ∑ i : Fin 3,
        Polynomial.C (v i) *
          transverseAffineLineSpecialisation a v
            (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [transverseAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq, mul_add, Finset.sum_add_distrib]
  · intro p n hp
    simp only [map_mul, transverseAffineLineSpecialisation_X,
      Polynomial.derivative_mul, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases n <;> simp [Fin.sum_univ_succ] <;> ring

/-- A complete multivariate logarithmic-derivative cross system restricts to
the corresponding one-variable identity on every affine line. -/
theorem transverseAffineLine_logDerivative_cross
    (P Q : MvPolynomial (Fin 3) K)
    (hcross :
      ∀ j : Fin 3,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 3 → K) :
    transverseAffineLineSpecialisation a v P *
        (transverseAffineLineSpecialisation a v Q).derivative =
      transverseAffineLineSpecialisation a v Q *
        (transverseAffineLineSpecialisation a v P).derivative := by
  rw [derivative_transverseAffineLineSpecialisation,
    derivative_transverseAffineLineSpecialisation]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmap := congrArg (transverseAffineLineSpecialisation a v) (hcross j)
  simp only [map_mul] at hmap
  calc
    transverseAffineLineSpecialisation a v P *
          (Polynomial.C (v j) *
            transverseAffineLineSpecialisation a v
              (MvPolynomial.pderiv j Q)) =
        Polynomial.C (v j) *
          (transverseAffineLineSpecialisation a v P *
            transverseAffineLineSpecialisation a v
              (MvPolynomial.pderiv j Q)) := by ring
    _ = Polynomial.C (v j) *
          (transverseAffineLineSpecialisation a v Q *
            transverseAffineLineSpecialisation a v
              (MvPolynomial.pderiv j P)) := by rw [hmap]
    _ = transverseAffineLineSpecialisation a v Q *
          (Polynomial.C (v j) *
            transverseAffineLineSpecialisation a v
              (MvPolynomial.pderiv j P)) := by ring

/-- B20 applied after affine-line restriction.  The only extra hypothesis is
that the chosen pivot polynomial does not vanish identically on the line. -/
theorem transverseAffineLine_eq_C_mul_of_logDerivative_cross
    (P Q : MvPolynomial (Fin 3) K)
    (hcross :
      ∀ j : Fin 3,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 3 → K)
    (hPline : transverseAffineLineSpecialisation a v P ≠ 0) :
    ∃ c : K,
      transverseAffineLineSpecialisation a v Q =
        Polynomial.C c * transverseAffineLineSpecialisation a v P := by
  exact polynomial_eq_C_mul_of_logDerivative_cross
    (transverseAffineLineSpecialisation a v P)
    (transverseAffineLineSpecialisation a v Q)
    hPline
    (transverseAffineLine_logDerivative_cross P Q hcross a v)

namespace RankOneHomogeneousLogGradientData

/-- Every gradient component in the B19 residual is proportional to the pivot
component after restriction to any affine line on which the pivot restriction
is nonzero. -/
theorem affineLine_gradientComponent_proportional
    {H : MvPolynomial (Fin 3) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m)
    (i : Fin 3)
    (a v : Fin 3 → K)
    (hpivotLine :
      transverseAffineLineSpecialisation a v
        (MvPolynomial.pderiv G.pivot H) ≠ 0) :
    ∃ c : K,
      transverseAffineLineSpecialisation a v
          (MvPolynomial.pderiv i H) =
        Polynomial.C c *
          transverseAffineLineSpecialisation a v
            (MvPolynomial.pderiv G.pivot H) := by
  apply transverseAffineLine_eq_C_mul_of_logDerivative_cross
  · intro j
    simpa [HC4.Polynomial.hessian_apply] using G.cross i j
  · exact hpivotLine

end RankOneHomogeneousLogGradientData

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-level B21 interface: the final B19 rank-one residual has linewise
constant gradient ratios on every affine line where the pivot survives. -/
theorem FirstKeyRankOneLogGradientResidualData.affineLine_gradientComponent_proportional
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyRankOneLogGradientResidualData D F)
    (i : Fin 3)
    (a v : Fin 3 → K)
    (hpivotLine :
      transverseAffineLineSpecialisation a v
        (MvPolynomial.pderiv R.logGradient.pivot
          D.transverseSourceProfile) ≠ 0) :
    ∃ c : K,
      transverseAffineLineSpecialisation a v
          (MvPolynomial.pderiv i D.transverseSourceProfile) =
        Polynomial.C c *
          transverseAffineLineSpecialisation a v
            (MvPolynomial.pderiv R.logGradient.pivot
              D.transverseSourceProfile) := by
  exact R.logGradient.affineLine_gradientComponent_proportional
    i a v hpivotLine

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
