import HC4.Valuation.QuadraticTransverseCapRankThreeAffineDescent
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# The field of constants of the rational X-derivation in characteristic zero

A K-linear derivation D on RatFunc K that extends ordinary polynomial
differentiation has EXACTLY the ground-field constants K.

We do not assume this as an extra final-resolution axiom:
the proof uses the normalized and coprime RatFunc numerator and
denominator, differentiates the denominator-cleared identity
z * denom(z) = num(z), and applies Euclid's lemma:

  denom(z) | num(z) * denom(z)' ,
  IsCoprime num(z) denom(z)
  => denom(z) | denom(z)'.

The EXISTING lemma Polynomial.dvd_derivative_iff gives denom'=0;
characteristic zero makes denom constant. The numerator derivative
then vanishes too and the rational function is a scalar constant.

The only input still to construct is a K-linear derivation on
RatFunc K that acts on the polynomial embedding by differentiation.
This is an algebraic localisation task, not a new HC4 geometric
assumption.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Rational field constants rigidity, conditional only on
the genuine polynomial derivative compatibility of D.**

There is no abstract field-of-constants hypothesis here. It is a
theorem from the coprime numerator/denominator of RatFunc K. -/
theorem quadraticTransverse_ratFunc_derivation_constants
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hpoly : ∀ p : Polynomial K,
      D ((algebraMap (Polynomial K) (RatFunc K)) p) =
        (algebraMap (Polynomial K) (RatFunc K))
          (Polynomial.derivative p)) :
    ∀ z : RatFunc K, D z = 0 →
      ∃ c : K,
        z = (algebraMap (Polynomial K) (RatFunc K))
          (Polynomial.C c) := by
  intro z hz
  let p : Polynomial K := RatFunc.num z
  let q : Polynomial K := RatFunc.denom z
  let f : Polynomial K →+* RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K)
  have hq : q ≠ 0 := RatFunc.denom_ne_zero z
  have hqf : f q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hrepr : f p / f q = z := RatFunc.num_div_denom z
  have hmul : z * f q = f p := by
    calc
      z * f q = (f p / f q) * f q := by rw [hrepr]
      _ = f p := div_mul_cancel₀ _ hqf
  have hdiff : z * f (Polynomial.derivative q) =
      f (Polynomial.derivative p) := by
    have h := congrArg D hmul
    rw [D.leibniz, hz, hpoly q, hpoly p] at h
    simpa [smul_eq_mul] using h
  have hpolyeq :
      Polynomial.derivative p * q =
        p * Polynomial.derivative q := by
    apply RatFunc.algebraMap_injective K
    change f (Polynomial.derivative p * q) =
      f (p * Polynomial.derivative q)
    simp only [map_mul]
    calc
      f (Polynomial.derivative p) * f q =
          (z * f (Polynomial.derivative q)) * f q := by
            rw [hdiff]
      _ = (z * f q) * f (Polynomial.derivative q) := by ring
      _ = f p * f (Polynomial.derivative q) := by rw [hmul]
  have hqdiv : q ∣ Polynomial.derivative q := by
    have hdiv : q ∣ p * Polynomial.derivative q := by
      refine ⟨Polynomial.derivative p, ?_⟩
      calc
        p * Polynomial.derivative q =
            Polynomial.derivative p * q := hpolyeq.symm
        _ = q * Polynomial.derivative p := by ring
    exact (RatFunc.isCoprime_num_denom z).symm.dvd_of_dvd_mul_left hdiv
  have hqzero : Polynomial.derivative q = 0 :=
    Polynomial.dvd_derivative_iff.mp hqdiv
  have hqconst : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hqzero
  have hpcancel : f (Polynomial.derivative p) = 0 := by
    rw [← hdiff, hqzero]
    simp
  have hpzero : Polynomial.derivative p = 0 := by
    apply RatFunc.algebraMap_injective K
    change f (Polynomial.derivative p) = f 0
    simpa only [map_zero] using hpcancel
  have hpconst : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hpzero
  have hc : q.coeff 0 ≠ 0 := by
    intro hczero
    apply hq
    rw [hqconst, hczero]
    simp
  refine ⟨p.coeff 0 / q.coeff 0, ?_⟩
  calc
    z = f p / f q := hrepr.symm
    _ = f (Polynomial.C (p.coeff 0)) /
          f (Polynomial.C (q.coeff 0)) := by
            conv_lhs => rw [hpconst, hqconst]
    _ = f (Polynomial.C (p.coeff 0 / q.coeff 0)) := by
      apply (div_eq_iff
        (RatFunc.algebraMap_ne_zero
          (Polynomial.C_ne_zero.mpr hc))).mpr
      calc
        f (Polynomial.C (p.coeff 0)) =
          f (Polynomial.C ((p.coeff 0 / q.coeff 0) * q.coeff 0)) := by
            rw [div_mul_cancel₀ _ hc]
        _ = f (Polynomial.C (p.coeff 0 / q.coeff 0)) *
              f (Polynomial.C (q.coeff 0)) := by
                rw [map_mul, map_mul]

/-- **Full rank-three integrality from the RATIONAL Riccati identity.**

Assuming only that D really differentiates rational polynomials and
the genuine Riccati equation holds for the matrix C over K(x),
the inverse already belongs to K[x], and det C is a nonzero
constant. The constants-field argument is proved above from
coprime numerator/denominator; it is NOT an additional assumption.

The outstanding proofs are the construction of the compatible
rational derivation D and extraction of Riccati from the ACTUAL
four-variable represented Hessian. -/
theorem quadraticTransverse_ratFuncRiccati_polynomialInverse
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hpoly : ∀ p : Polynomial K,
      D ((algebraMap (Polynomial K) (RatFunc K)) p) =
        (algebraMap (Polynomial K) (RatFunc K))
          (Polynomial.derivative p))
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) (RatFunc K))
    (hCM : C.map (algebraMap (Polynomial K) (RatFunc K)) * M = 1)
    (hMC : M * C.map (algebraMap (Polynomial K) (RatFunc K)) = 1)
    (hRiccati :
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D
            (C.map (algebraMap (Polynomial K) (RatFunc K)))) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D
                (C.map (algebraMap (Polynomial K) (RatFunc K))) * M) *
          quadraticTransverse_fieldMatrixDerivative D
            (C.map (algebraMap (Polynomial K) (RatFunc K))))) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      C * P = 1 ∧ P * C = 1 ∧
        ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  exact quadraticTransverse_compatibleDerivation_integralInverse
    (algebraMap (Polynomial K) (RatFunc K))
    (RatFunc.algebraMap_injective K)
    D hpoly
    (quadraticTransverse_ratFunc_derivation_constants D hpoly)
    C M hCM hMC hRiccati

end

end HC4.Valuation
