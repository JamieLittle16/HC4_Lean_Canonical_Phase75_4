import HC4.Valuation.FourOrdinaryReverseRees
import Mathlib.Tactic

/-!
# Exact collision transport for the ordinary reverse-Rees family

The ordinary reverse-Rees parameter is source-honest not only at the
Hessian-determinant level.  If the original source polynomial has an exact
gradient collision at two constant points `a,b`, then

    R_D(F)(tau,x) = tau^D F(x/tau)

has an exact polynomial-family collision at the moving sections

    tau*a, tau*b.

Rather than divide by `tau` or manipulate the informal expression `x/tau`,
we use the already-formal reinflation identity

    R_D(F)(tau, tau*x) = tau^D F(x).

Differentiate this identity in one source coordinate.  Simultaneous source
inflation contributes exactly one factor `tau` to that derivative.  Evaluate
at `a` and `b`, use the original source collision on the right, and cancel
that common nonzero factor.  No Smith, blocker, or auxiliary clock appears.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- A constant source point multiplied coordinatewise by the family
parameter. -/
def fourReverseReesScaledSection
    (a : Fin 4 → K) : Fin 4 → Polynomial K :=
  fun i => Polynomial.X * Polynomial.C (a i)

/-- Evaluation after simultaneous unit source inflation is evaluation of the
original family at the parameter-scaled source section. -/
theorem eval_fourUnitSourceInflateFamily_constantSection
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → K) :
    MvPolynomial.eval (polynomialConstantSection a)
        (fourUnitSourceInflateFamily P) =
      MvPolynomial.eval (fourReverseReesScaledSection a) P := by
  unfold fourUnitSourceInflateFamily unitTransverseInflateFamily
  rw [eval_kernelInflateHom]
  rw [eval_kernelInflateHom]
  rw [eval_kernelInflateHom]
  rw [eval_kernelInflateHom]
  apply congrArg (fun s : Fin 4 → Polynomial K => MvPolynomial.eval s P)
  funext i
  fin_cases i <;>
    simp [kernelBlowupSection, polynomialConstantSection,
      fourReverseReesScaledSection]

/-- Every spatial derivative of the simultaneous four-coordinate inflation
acquires exactly one parameter factor. -/
theorem pderiv_fourUnitSourceInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i : Fin 4) :
    MvPolynomial.pderiv i (fourUnitSourceInflateFamily P) =
      MvPolynomial.C Polynomial.X *
        fourUnitSourceInflateFamily (MvPolynomial.pderiv i P) := by
  unfold fourUnitSourceInflateFamily unitTransverseInflateFamily
  rw [pderiv_kernelInflateHom]
  rw [pderiv_kernelInflateHom]
  rw [pderiv_kernelInflateHom]
  rw [pderiv_kernelInflateHom]
  fin_cases i <;>
    simp [kernelInflateDerivativeCoefficient, map_mul] <;>
    ring

/-- Extending coefficients from `K` to `K[tau]` and evaluating at a constant
polynomial section is the constant-polynomial image of ordinary evaluation. -/
theorem eval_map_polynomialC_constantSection
    (G : MvPolynomial (Fin 4) K)
    (a : Fin 4 → K) :
    MvPolynomial.eval (polynomialConstantSection a)
        (MvPolynomial.map Polynomial.C G) =
      Polynomial.C (MvPolynomial.eval a G) := by
  rw [MvPolynomial.eval_map]
  simpa [polynomialConstantSection] using
    (MvPolynomial.eval₂_comp
      (Polynomial.C : K →+* Polynomial K)
      a G).symm

/-- **Exact source-honest collision on the ordinary reverse-Rees family.** -/
theorem fourOrdinaryReverseReesFamily_exactGradientCollision
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (a b : Fin 4 → K)
    (hcoll : HasExactGradientCollision F a b) :
    HasPolynomialFamilyExactGradientCollision
      (fourOrdinaryReverseReesFamily F D)
      (fourReverseReesScaledSection a)
      (fourReverseReesScaledSection b) := by
  intro i
  let R := fourOrdinaryReverseReesFamily F D
  have hreinflate :
      fourUnitSourceInflateFamily R =
        MvPolynomial.C (Polynomial.X ^ D) *
          MvPolynomial.map Polynomial.C F := by
    dsimp [R]
    exact fourUnitSourceInflate_reverseRees_eq F D hmax
  have hpd := congrArg (MvPolynomial.pderiv i) hreinflate
  have hpd' :
      MvPolynomial.C Polynomial.X *
          fourUnitSourceInflateFamily (MvPolynomial.pderiv i R) =
        MvPolynomial.C (Polynomial.X ^ D) *
          MvPolynomial.map Polynomial.C (MvPolynomial.pderiv i F) := by
    rw [pderiv_fourUnitSourceInflateFamily] at hpd
    simpa [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_map] using hpd
  have ha :=
    congrArg
      (MvPolynomial.eval (polynomialConstantSection a)) hpd'
  have hb :=
    congrArg
      (MvPolynomial.eval (polynomialConstantSection b)) hpd'
  simp only [map_mul, MvPolynomial.eval_C] at ha hb
  rw [eval_fourUnitSourceInflateFamily_constantSection] at ha hb
  rw [eval_map_polynomialC_constantSection] at ha hb
  have hsource := hcoll i
  unfold mvGradientComponentAt at hsource
  have hwithX :
      Polynomial.X *
          MvPolynomial.eval (fourReverseReesScaledSection a)
            (MvPolynomial.pderiv i R) =
        Polynomial.X *
          MvPolynomial.eval (fourReverseReesScaledSection b)
            (MvPolynomial.pderiv i R) := by
    calc
      Polynomial.X *
          MvPolynomial.eval (fourReverseReesScaledSection a)
            (MvPolynomial.pderiv i R) =
        Polynomial.X ^ D *
          Polynomial.C
            (MvPolynomial.eval a (MvPolynomial.pderiv i F)) := ha
      _ = Polynomial.X ^ D *
          Polynomial.C
            (MvPolynomial.eval b (MvPolynomial.pderiv i F)) := by
            rw [hsource]
      _ = Polynomial.X *
          MvPolynomial.eval (fourReverseReesScaledSection b)
            (MvPolynomial.pderiv i R) := hb.symm
  have hcancel :=
    polynomial_X_pow_mul_cancel (K := K) 1
      (by simpa [pow_one] using hwithX)
  simpa [R] using hcancel

end

end HC4.Valuation
