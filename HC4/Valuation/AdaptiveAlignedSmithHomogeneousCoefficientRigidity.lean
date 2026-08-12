import HC4.Valuation.AdaptiveAlignedSmithBlockerDegreeEndpoints
import HC4.Valuation.AdaptiveAlignedSmithBlockerResidual
import HC4.Valuation.AdaptiveAlignedSmithBlockerFirstWall
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# Homogeneous longitudinal coefficient rigidity

This is a deliberately API-stable version of the coefficient argument used
to eliminate degree-pure transverse blockers.

The proof avoids expanding `Finsupp.degree` or relying on definitional
simplification of `Finsupp.cons`.  Instead it computes the ordinary
homogeneous weight directly from the four coordinates of a cons exponent.

For a homogeneous four-variable polynomial, fixing the three transverse
coordinates leaves at most one possible longitudinal exponent.  Hence every
nonzero fixed-transverse coefficient fibre is a single univariate monomial.

Right recentering acts on that fibre by `Polynomial.taylor 1`.  A transverse
blocker coefficient has the factor `X * (X - 1)`, so its recentered fibre
vanishes at `X = -1`.  A nonzero monomial cannot vanish there.  Therefore a
concrete blocker whose right-recentered fibre is homogeneous must be the
pure-longitudinal constructor.

The remaining pure-longitudinal derivative case is intentionally left for
the next file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Exact ordinary weight of a source exponent obtained by adjoining the
longitudinal exponent `n` to a fixed Smith transverse exponent. -/
theorem weight_one_cons_smithTransverseExponent
    (b c d n : ℕ) :
    Finsupp.weight (1 : Fin 4 → ℕ)
        ((smithTransverseExponent b c d).cons n) =
      n + b + c + d := by
  have h0 :
      ((smithTransverseExponent b c d).cons n) (0 : Fin 4) = n := by
    simp
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
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp only [Fin.sum_univ_four]
    rw [h0, h1, h2, h3]
    simp
  · intro i
    simp

/-- In a homogeneous four-variable polynomial, a fixed transverse
coefficient fibre has at most one nonzero longitudinal coefficient. -/
theorem homogeneous_longitudinalCoefficient_coeff_unique
    (G : MvPolynomial (Fin 4) K)
    (D b c d k l : ℕ)
    (hhom : G.IsHomogeneous D)
    (hk :
      (longitudinalCoefficientPolynomial b c d G).coeff k ≠ 0)
    (hl :
      (longitudinalCoefficientPolynomial b c d G).coeff l ≠ 0) :
    k = l := by
  have hkG :
      MvPolynomial.coeff
          ((smithTransverseExponent b c d).cons k) G ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hk
  have hlG :
      MvPolynomial.coeff
          ((smithTransverseExponent b c d).cons l) G ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hl

  have hkWeight :
      Finsupp.weight (1 : Fin 4 → ℕ)
          ((smithTransverseExponent b c d).cons k) = D :=
    hhom hkG
  have hlWeight :
      Finsupp.weight (1 : Fin 4 → ℕ)
          ((smithTransverseExponent b c d).cons l) = D :=
    hhom hlG

  have hkSum :
      k + b + c + d = D :=
    (weight_one_cons_smithTransverseExponent b c d k).symm.trans hkWeight
  have hlSum :
      l + b + c + d = D :=
    (weight_one_cons_smithTransverseExponent b c d l).symm.trans hlWeight
  omega

/-- Every nonzero fixed-transverse coefficient fibre of a homogeneous
polynomial is literally one univariate monomial. -/
theorem homogeneous_longitudinalCoefficient_eq_monomial
    (G : MvPolynomial (Fin 4) K)
    (D b c d : ℕ)
    (hhom : G.IsHomogeneous D)
    (hne : longitudinalCoefficientPolynomial b c d G ≠ 0) :
    ∃ n : ℕ, ∃ a : K,
      a ≠ 0 ∧
      longitudinalCoefficientPolynomial b c d G =
        Polynomial.monomial n a := by
  have hsupp :
      (longitudinalCoefficientPolynomial b c d G).support.Nonempty := by
    exact Polynomial.support_nonempty.mpr hne
  rcases hsupp with ⟨n, hn⟩
  have hcn :
      (longitudinalCoefficientPolynomial b c d G).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn

  refine
    ⟨n,
      (longitudinalCoefficientPolynomial b c d G).coeff n,
      hcn, ?_⟩
  apply Polynomial.ext
  intro k
  by_cases hkn : k = n
  · subst k
    simp
  · have hkzero :
        (longitudinalCoefficientPolynomial b c d G).coeff k = 0 := by
      by_contra hk
      have huniq : k = n :=
        homogeneous_longitudinalCoefficient_coeff_unique
          G D b c d k n hhom hk hcn
      exact hkn huniq
    rw [hkzero]
    symm
    exact
      Polynomial.coeff_monomial_of_ne
        ((longitudinalCoefficientPolynomial b c d G).coeff n) hkn

/-- A nonzero fixed-transverse coefficient fibre of a homogeneous
four-variable polynomial cannot vanish at `X = -1`. -/
theorem homogeneous_longitudinalCoefficient_eval_neg_one_ne_zero
    (G : MvPolynomial (Fin 4) K)
    (D b c d : ℕ)
    (hhom : G.IsHomogeneous D)
    (hne : longitudinalCoefficientPolynomial b c d G ≠ 0) :
    Polynomial.eval (-1 : K)
        (longitudinalCoefficientPolynomial b c d G) ≠ 0 := by
  rcases
      homogeneous_longitudinalCoefficient_eq_monomial
        G D b c d hhom hne with
    ⟨n, a, ha, hmono⟩
  rw [hmono]
  simp [ha]

/-- Taylor translation by `1` preserves nonzeroness.  This is just the
existing Taylor-zero equivalence, packaged in the direction needed below. -/
theorem polynomial_taylor_one_ne_zero
    (P : Polynomial K)
    (hP : P ≠ 0) :
    Polynomial.taylor 1 P ≠ 0 := by
  have htaylor :
      Polynomial.taylor 1 P ≠ 0 ↔ P ≠ 0 :=
    not_congr (Polynomial.taylor_eq_zero (1 : K) P)
  exact htaylor.mpr hP

/-- **Transverse endpoint-factor contradiction.**

If a source longitudinal coefficient has the two-endpoint factor
`X * (X - 1)`, then its right-recentered coefficient fibre vanishes at
`X = -1`.  It therefore cannot be both nonzero and contained in a homogeneous
recentered four-variable polynomial.
-/
theorem transverse_twoEndpointResidual_incompatible_with_recenteredHomogeneous
    (F : MvPolynomial (Fin 4) K)
    (D b c d : ℕ)
    (A R : Polynomial K)
    (hA : A ≠ 0)
    (hAeq :
      A = longitudinalCoefficientPolynomial b c d F)
    (hfactor :
      A =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R)
    (hhom :
      (longitudinalRightRecenterHom (K := K) F).IsHomogeneous D) :
    False := by
  let G := longitudinalRightRecenterHom (K := K) F
  let P := longitudinalCoefficientPolynomial b c d G

  have htranslate :
      P =
        Polynomial.taylor 1
          (longitudinalCoefficientPolynomial b c d F) := by
    dsimp [P, G]
    exact
      longitudinalCoefficientPolynomial_longitudinalRightRecenterHom
        b c d F

  have hsourceNe :
      longitudinalCoefficientPolynomial b c d F ≠ 0 := by
    rw [← hAeq]
    exact hA

  have hPne : P ≠ 0 := by
    rw [htranslate]
    exact polynomial_taylor_one_ne_zero
      (longitudinalCoefficientPolynomial b c d F) hsourceNe

  have hPneg :
      Polynomial.eval (-1 : K) P = 0 := by
    rw [htranslate]
    rw [Polynomial.taylor_eval]
    rw [← hAeq, hfactor]
    simp

  have hPneg_ne :
      Polynomial.eval (-1 : K) P ≠ 0 := by
    dsimp [P, G]
    exact
      homogeneous_longitudinalCoefficient_eval_neg_one_ne_zero
        (longitudinalRightRecenterHom (K := K) F)
        D b c d hhom hPne

  exact hPneg_ne hPneg

/-- Under recentered ordinary homogeneity, every concrete blocker residual
normal form is necessarily the pure-longitudinal constructor.  The three
transverse constructors are impossible by the endpoint-factor argument. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.pureLongitudinal_of_recenteredHomogeneous
    {degreeCap D : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (R :
      AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
        (K := K) B)
    (hhom :
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber).IsHomogeneous D) :
    Nonempty
      (AdaptiveAlignedSmithPureLongitudinalResidual (K := K) B) := by
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact
        ⟨{
          axis := A
          residual := C
          pattern := hpattern
          axis_ne_zero := hA
          axis_eq := hAeq
          residual_ne_zero := hC
          derivative_factor := hfactor
          degree_drop := hdegree
          normal := normal
        }⟩
  | lowNegativeFirst A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact False.elim <|
        transverse_twoEndpointResidual_incompatible_with_recenteredHomogeneous
          B.aligned.endpoint.rawSpecialFiber D
          B.exponent.b B.exponent.c B.exponent.d
          A C hA hAeq hfactor hhom
  | lowNegativeSecond A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact False.elim <|
        transverse_twoEndpointResidual_incompatible_with_recenteredHomogeneous
          B.aligned.endpoint.rawSpecialFiber D
          B.exponent.b B.exponent.c B.exponent.d
          A C hA hAeq hfactor hhom
  | wLinear A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact False.elim <|
        transverse_twoEndpointResidual_incompatible_with_recenteredHomogeneous
          B.aligned.endpoint.rawSpecialFiber D
          B.exponent.b B.exponent.c B.exponent.d
          A C hA hAeq hfactor hhom

end

end HC4.Valuation
