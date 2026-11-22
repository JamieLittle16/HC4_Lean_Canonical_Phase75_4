import HC4.Polynomial.RankThreeCubicSourceHessianThirdDerivative
import HC4.Polynomial.RankThreeCubicThirdDerivativeBasePolynomialTime
import Mathlib.Tactic

/-!
# The constant time coefficient is the actual transverse Hessian derivative

For any straight rational characteristic of the cubic source, the t⁰
coefficient of a line-evaluated source third transverse derivative is
the derivative of the polynomial transverse Hessian at the source slice.

The identity holds for arbitrary transverse rational velocities; in
particular it transports the source quadratic pole-residue equations
to the very same matrix derivative used in Jacobi's determinant formula.
No source-geometry closing assumption is introduced.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Public version of the source line-evaluation constant-coefficient
identity, avoiding an independent analytic Taylor-series argument. -/
theorem lineEval_coeff_zero_source
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z V : ι → F3 K) (P : MvPolynomial ι K) :
    (lineEval z V P).coeff 0 = MvPolynomial.aeval z P := by
  classical
  let E := lineEval (K := K) z V
  have hev :
      (_root_.Polynomial.constantCoeff.comp E.toRingHom) =
        (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] F3 K).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, lineEval,
        IsScalarTower.algebraMap_apply K (F3 K) (_root_.Polynomial (F3 K)),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      simp [E, lineEval]
  exact RingHom.congr_fun hev P

/-- Without assuming any polynomial transverse velocity, the actual
third-derivative time constant equals the transverse Hessian derivative
at the source longitudinal slice, embedded into the fraction field. -/
theorem sourceCubic_thirdLineEval_coeffZero_eq_HessianDerivative
    (a : K) (L : SB K)
    (V : Unit ⊕ Fin 3 → F3 K) (i j k : Fin 3) :
    (lineEval (transverseGenericPoint a) V
      (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))).coeff 0 =
      algebraMap (B3 K) (F3 K)
        (pderiv i (sourceTransverseHessian a L j k)) := by
  let P : SB K :=
    pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
  calc
    (lineEval (transverseGenericPoint a) V P).coeff 0 =
        MvPolynomial.aeval (transverseGenericPoint a) P :=
      lineEval_coeff_zero_source _ _ P
    _ = algebraMap (B3 K) (F3 K) (referenceSlice a P) :=
      (referenceSlice_fractionEvaluation a P).symm
    _ = algebraMap (B3 K) (F3 K)
        (pderiv i (sourceTransverseHessian a L j k)) := by
          congr 1
          exact (sourceTransverseHessian_pderiv_eq_third a L i j k).symm

/-- A source-grounded polynomial-time representative has constant
coefficient exactly equal to the polynomial Hessian derivative,
not just some unspecified regular element of the fraction field. -/
theorem sourceCubic_thirdBasePolynomial_coeffZero_eq_HessianDerivative
    (a : K) (L : SB K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (Q : _root_.Polynomial (B3 K))
    (i j k : Fin 3)
    (hQ :
      Q.map (algebraMap (B3 K) (F3 K)) =
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) :
    Q.coeff 0 = pderiv i (sourceTransverseHessian a L j k) := by
  apply IsFractionRing.injective (B3 K) (F3 K)
  have hc := congrArg
    (fun P : _root_.Polynomial (F3 K) => P.coeff 0) hQ
  simpa only [_root_.Polynomial.coeff_map] using
    (hc.trans
      (sourceCubic_thirdLineEval_coeffZero_eq_HessianDerivative
        a L V i j k))

end
end HC4.Polynomial.RankThreeCubic
