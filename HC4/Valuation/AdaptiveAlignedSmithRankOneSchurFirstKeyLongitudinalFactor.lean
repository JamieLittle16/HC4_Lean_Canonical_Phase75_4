import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyHomogeneousSlice
import HC4.Valuation.AdaptiveAlignedSmithHomogeneousCoefficientRigidity
import Mathlib.Tactic

/-!
# Common longitudinal monomial factor of the first Schur source key

Stage 4B3 selected a nonzero ordinary-homogeneous slice `R` of the first
positive transverse source key.  Every supported monomial of `R` has

    total transverse degree = m,
    x₀-exponent             = D - m.

The homogeneous coefficient-rigidity library already proves something
slightly stronger than the support statement: after freezing a transverse
exponent `(b,c,d)`, the resulting longitudinal coefficient polynomial is a
single monomial.

This file composes that existing theorem with the Stage-4B3 fixed exponent.
Consequently every nonzero frozen transverse fibre is literally

    a * X^(D-m),

and such a fibre can occur only when `b+c+d = m`.

Thus the Stage-4B3 slice is coefficientwise exactly of the form

    x₀^(D-m) * H_m(x₁,x₂,x₃)

with `H_m` transverse homogeneous of degree `m`.  We deliberately keep this
as the coefficient-fibre API already used throughout the Smith code rather
than introduce a second polynomial factorisation construction.

No Hessian, Schur, packet-classification, or repair result is reproved here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace FirstTransverseKeyHomogeneousSliceData

/-- A nonzero frozen transverse fibre of the homogeneous first-key slice can
occur only at the selected total transverse degree `m`. -/
theorem longitudinalCoefficient_transverseDegree
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (b c d : ℕ)
    (hne : longitudinalCoefficientPolynomial b c d S.slice ≠ 0) :
    b + c + d = m := by
  rcases Polynomial.support_nonempty.mpr hne with ⟨n, hn⟩
  have hcoeffP :
      (longitudinalCoefficientPolynomial b c d S.slice).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeffSlice :
      MvPolynomial.coeff
          ((smithTransverseExponent b c d).cons n) S.slice ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hcoeffP
  have htrans :=
    S.slice_exactTransverseDegree
      ((smithTransverseExponent b c d).cons n) hcoeffSlice
  have h1 :
      ((smithTransverseExponent b c d).cons n) (1 : Fin 4) = b := by
    change ((smithTransverseExponent b c d).cons n)
      (Fin.succ (0 : Fin 3)) = b
    rw [Finsupp.cons_succ]
    exact smithTransverseExponent_zero b c d
  have h2 :
      ((smithTransverseExponent b c d).cons n) (2 : Fin 4) = c := by
    change ((smithTransverseExponent b c d).cons n)
      (Fin.succ (1 : Fin 3)) = c
    rw [Finsupp.cons_succ]
    exact smithTransverseExponent_one b c d
  have h3 :
      ((smithTransverseExponent b c d).cons n) (3 : Fin 4) = d := by
    change ((smithTransverseExponent b c d).cons n)
      (Fin.succ (2 : Fin 3)) = d
    rw [Finsupp.cons_succ]
    exact smithTransverseExponent_two b c d
  unfold pureLongitudinalTransverseDegree at htrans
  rw [h1, h2, h3] at htrans
  exact htrans

/-- The homogeneous-fibre theorem already present in the library sharpens,
on the Stage-4B3 slice, to a *fixed* longitudinal exponent `D-m` independent
of the transverse monomial. -/
theorem longitudinalCoefficient_eq_fixedMonomial
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (b c d : ℕ)
    (hne : longitudinalCoefficientPolynomial b c d S.slice ≠ 0) :
    ∃ a : K,
      a ≠ 0 ∧
      longitudinalCoefficientPolynomial b c d S.slice =
        Polynomial.monomial (S.ordinaryDegree - m) a := by
  rcases
      homogeneous_longitudinalCoefficient_eq_monomial
        S.slice S.ordinaryDegree b c d S.slice_homogeneous hne with
    ⟨n, a, ha, hmono⟩

  have hcoeffP :
      (longitudinalCoefficientPolynomial b c d S.slice).coeff n ≠ 0 := by
    rw [hmono]
    simpa using ha

  have hcoeffSlice :
      MvPolynomial.coeff
          ((smithTransverseExponent b c d).cons n) S.slice ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hcoeffP

  have hn : n = S.ordinaryDegree - m := by
    have h :=
      S.slice_longitudinalExponent
        ((smithTransverseExponent b c d).cons n) hcoeffSlice
    simpa using h

  refine ⟨a, ha, ?_⟩
  simpa [hn] using hmono

/-- Frozen transverse fibres of the slice vanish away from total transverse
degree `m`. -/
theorem longitudinalCoefficient_eq_zero_of_transverseDegree_ne
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (b c d : ℕ)
    (hdeg : b + c + d ≠ m) :
    longitudinalCoefficientPolynomial b c d S.slice = 0 := by
  by_contra hne
  exact hdeg (S.longitudinalCoefficient_transverseDegree b c d hne)

/-- Compact coefficientwise factor profile of the homogeneous first-key
slice.  This is the precise API needed by the next Schur-active transverse
classification: every nonzero transverse coefficient has degree `m` and the
same longitudinal monomial factor `X^(D-m)`. -/
theorem longitudinalMonomialFactorProfile
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m) :
    ∀ b c d : ℕ,
      longitudinalCoefficientPolynomial b c d S.slice ≠ 0 →
        b + c + d = m ∧
          ∃ a : K,
            a ≠ 0 ∧
            longitudinalCoefficientPolynomial b c d S.slice =
              Polynomial.monomial (S.ordinaryDegree - m) a := by
  intro b c d hne
  exact
    ⟨S.longitudinalCoefficient_transverseDegree b c d hne,
      S.longitudinalCoefficient_eq_fixedMonomial b c d hne⟩

end FirstTransverseKeyHomogeneousSliceData

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing assembly: every first source key has a nonzero homogeneous
slice whose complete longitudinal coefficient profile has one common
longitudinal monomial exponent. -/
theorem HasFirstTransverseSourceKey.exists_homogeneousSlice_with_longitudinalFactor
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    ∃ hpos :
        (positiveTransverseSourceSupport
          (polynomialFamilySpecialFiber C.family)).Nonempty,
      let F₀ := polynomialFamilySpecialFiber C.family
      let m := firstPositiveTransverseSourceDegree F₀ hpos
      let Q :=
        HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) F₀
      ∃ S : FirstTransverseKeyHomogeneousSliceData Q m,
        ∀ b c d : ℕ,
          longitudinalCoefficientPolynomial b c d S.slice ≠ 0 →
            b + c + d = m ∧
              ∃ a : K,
                a ≠ 0 ∧
                longitudinalCoefficientPolynomial b c d S.slice =
                  Polynomial.monomial (S.ordinaryDegree - m) a := by
  rcases hkey.exists_homogeneousSlice with ⟨hpos, hS⟩
  refine ⟨hpos, ?_⟩
  dsimp only at hS ⊢
  rcases hS with ⟨S⟩
  exact ⟨S, S.longitudinalMonomialFactorProfile⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
