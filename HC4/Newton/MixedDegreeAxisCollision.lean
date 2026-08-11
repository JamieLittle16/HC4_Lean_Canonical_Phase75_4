import HC4.Newton.SymmetricSmithMinimality
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic

/-!
# Longitudinal coefficient polynomials

The Smith projection forgets source coordinate `0`.  Without source
homogeneity, the monomials over one projected transverse exponent must be
retained as a polynomial in that longitudinal coordinate.  This file defines
that polynomial using `MvPolynomial.finSuccEquiv` and proves its exact
coefficient formula.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [CommRing K]

/-- Coefficient formula for partial derivatives over a general commutative
ring.  The existing older backport is field-specialised, while the pointed
family application has coefficient ring `Polynomial K`. -/
theorem coeff_pderiv_mixedDegree
    {σ : Type*}
    (i : σ)
    (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv i F) =
      MvPolynomial.coeff (m + Finsupp.single i 1) F *
        ((m i + 1 : ℕ) : K) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp [hP, hQ, add_mul]
  | monomial n a =>
      rw [MvPolynomial.pderiv_monomial,
        MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : n = m + Finsupp.single i 1
      · simp [h]
      · simp only [h, if_false, zero_mul]
        by_cases hn : n i = 0
        · simp [hn]
        · apply if_neg
          have hle : Finsupp.single i 1 ≤ n := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr hn
          intro hsub
          apply h
          exact (tsub_eq_iff_eq_add_of_le hle).mp hsub

/-- The transverse exponent `(b,c,d)` on source coordinates `1,2,3`, viewed
as an exponent on `Fin 3`. -/
def smithTransverseExponent (b c d : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 b + Finsupp.single 1 c + Finsupp.single 2 d

@[simp] theorem smithTransverseExponent_zero (b c d : ℕ) :
    smithTransverseExponent b c d 0 = b := by
  simp [smithTransverseExponent]

@[simp] theorem smithTransverseExponent_one (b c d : ℕ) :
    smithTransverseExponent b c d 1 = c := by
  simp [smithTransverseExponent]

@[simp] theorem smithTransverseExponent_two (b c d : ℕ) :
    smithTransverseExponent b c d 2 = d := by
  simp [smithTransverseExponent]

/-- Collect all monomials with fixed transverse exponent `m` into a
polynomial in the longitudinal source coordinate `0`. -/
def longitudinalCoefficientPolynomialAt
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K) : Polynomial K :=
  let Q := MvPolynomial.finSuccEquiv K 3 F
  ∑ a ∈ Q.support,
    Polynomial.monomial a (MvPolynomial.coeff m (Q.coeff a))

/-- The `(b,c,d)` longitudinal coefficient polynomial used by the Smith
projection. -/
def longitudinalCoefficientPolynomial
    (b c d : ℕ)
    (F : MvPolynomial (Fin 4) K) : Polynomial K :=
  longitudinalCoefficientPolynomialAt
    (smithTransverseExponent b c d) F

/-- Exact coefficient formula before translating the `Fin 3` exponent back
to a four-variable source exponent. -/
theorem coeff_longitudinalCoefficientPolynomialAt
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K)
    (a : ℕ) :
    (longitudinalCoefficientPolynomialAt m F).coeff a =
      MvPolynomial.coeff m
        ((MvPolynomial.finSuccEquiv K 3 F).coeff a) := by
  classical
  unfold longitudinalCoefficientPolynomialAt
  dsimp only
  by_cases ha : a ∈ (MvPolynomial.finSuccEquiv K 3 F).support
  · simp [Polynomial.coeff_monomial, ha]
  · have hcoeff :
        (MvPolynomial.finSuccEquiv K 3 F).coeff a = 0 := by
      exact Polynomial.notMem_support_iff.mp ha
    simp [Polynomial.coeff_monomial, ha, hcoeff]

/-- Exact reconstruction formula: the coefficient of `X^a` is the original
four-variable coefficient at longitudinal exponent `a` and transverse
exponent `m`. -/
theorem coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K)
    (a : ℕ) :
    (longitudinalCoefficientPolynomialAt m F).coeff a =
      MvPolynomial.coeff (m.cons a) F := by
  rw [coeff_longitudinalCoefficientPolynomialAt]
  exact MvPolynomial.finSuccEquiv_coeff_coeff m F a

theorem coeff_longitudinalCoefficientPolynomial
    (b c d : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (a : ℕ) :
    (longitudinalCoefficientPolynomial b c d F).coeff a =
      MvPolynomial.coeff ((smithTransverseExponent b c d).cons a) F := by
  exact coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff
    (smithTransverseExponent b c d) F a

/-! ## Restriction to the distinguished axis -/

/-- Restrict a four-variable polynomial to the longitudinal coordinate `0`
by setting coordinates `1,2,3` to zero. -/
def longitudinalAxisRestriction
    (F : MvPolynomial (Fin 4) K) : Polynomial K :=
  Polynomial.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))
    (MvPolynomial.finSuccEquiv K 3 F)

/-- Longitudinal-only right-endpoint recentering.  The convention is
explicitly `old x = new x + 1`; transverse source variables are fixed. -/
noncomputable def longitudinalRightRecenterHom :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases
      (MvPolynomial.X (0 : Fin 4) + MvPolynomial.C 1)
      (fun j : Fin 3 => MvPolynomial.X j.succ))

@[simp] theorem longitudinalRightRecenterHom_X_zero :
    longitudinalRightRecenterHom (K := K) (MvPolynomial.X (0 : Fin 4)) =
      MvPolynomial.X 0 + MvPolynomial.C 1 := by
  simp [longitudinalRightRecenterHom]

@[simp] theorem longitudinalRightRecenterHom_X_succ
    (j : Fin 3) :
    longitudinalRightRecenterHom (K := K) (MvPolynomial.X j.succ) =
      MvPolynomial.X j.succ := by
  simp [longitudinalRightRecenterHom]

/-- Under `finSuccEquiv`, actual longitudinal source recentering is exactly
univariate Taylor translation of the outer polynomial. -/
theorem finSuccEquiv_longitudinalRightRecenterHom
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.finSuccEquiv K 3
        (longitudinalRightRecenterHom (K := K) F) =
      Polynomial.taylor (1 : MvPolynomial (Fin 3) K)
        (MvPolynomial.finSuccEquiv K 3 F) := by
  change
    (((MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom.comp
      (longitudinalRightRecenterHom (K := K))) F) =
    (((Polynomial.taylorAlgHom
        (1 : MvPolynomial (Fin 3) K)).toRingHom.comp
      (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom) F)
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [longitudinalRightRecenterHom,
      MvPolynomial.finSuccEquiv_apply, Polynomial.taylor_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [longitudinalRightRecenterHom,
        MvPolynomial.finSuccEquiv_apply, Polynomial.taylor_apply]
    · simp [longitudinalRightRecenterHom,
        MvPolynomial.finSuccEquiv_apply, Polynomial.taylor_apply]

/-- Transverse coefficient extraction commutes with every Hasse derivative
of the outer longitudinal polynomial and evaluation at `1`. -/
theorem coeff_eval_hasseDeriv_finSuccEquiv_eq
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ) :
    MvPolynomial.coeff m
        ((Polynomial.hasseDeriv n
          (MvPolynomial.finSuccEquiv K 3 F)).eval 1) =
      (Polynomial.hasseDeriv n
        (longitudinalCoefficientPolynomialAt m F)).eval 1 := by
  classical
  let Q := MvPolynomial.finSuccEquiv K 3 F
  change MvPolynomial.coeff m ((Polynomial.hasseDeriv n Q).eval 1) = _
  unfold longitudinalCoefficientPolynomialAt
  dsimp only
  conv_lhs => rw [Q.as_sum_support]
  simp_rw [map_sum, Polynomial.eval_finset_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  rw [show (i.choose n : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (i.choose n : K) by simp]
  simp only [one_pow, mul_one]
  rw [MvPolynomial.coeff_C_mul]

/-- Recentring acts on each fixed transverse longitudinal fibre by the
same univariate Taylor translation. -/
theorem longitudinalCoefficientPolynomialAt_longitudinalRightRecenterHom
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomialAt m
        (longitudinalRightRecenterHom (K := K) F) =
      Polynomial.taylor 1 (longitudinalCoefficientPolynomialAt m F) := by
  ext n
  rw [coeff_longitudinalCoefficientPolynomialAt,
    finSuccEquiv_longitudinalRightRecenterHom,
    Polynomial.taylor_coeff, Polynomial.taylor_coeff]
  exact coeff_eval_hasseDeriv_finSuccEquiv_eq m F n

theorem longitudinalCoefficientPolynomial_longitudinalRightRecenterHom
    (b c d : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomial b c d
        (longitudinalRightRecenterHom (K := K) F) =
      Polynomial.taylor 1 (longitudinalCoefficientPolynomial b c d F) := by
  exact longitudinalCoefficientPolynomialAt_longitudinalRightRecenterHom
    (smithTransverseExponent b c d) F

/-- Transverse coefficient extraction commutes with evaluating the outer
longitudinal derivative at `1`. -/
theorem coeff_eval_derivative_finSuccEquiv_eq
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.coeff m
        ((MvPolynomial.finSuccEquiv K 3 F).derivative.eval 1) =
      (longitudinalCoefficientPolynomialAt m F).derivative.eval 1 := by
  classical
  let Q := MvPolynomial.finSuccEquiv K 3 F
  change MvPolynomial.coeff m (Q.derivative.eval 1) = _
  unfold longitudinalCoefficientPolynomialAt
  dsimp only
  change MvPolynomial.coeff m (Q.derivative.eval 1) =
    (∑ i ∈ Q.support,
      Polynomial.monomial i (MvPolynomial.coeff m (Q.coeff i))).derivative.eval 1
  conv_lhs => rw [Q.as_sum_support]
  simp_rw [map_sum]
  simp_rw [Polynomial.eval_finset_sum]
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.derivative_monomial, Polynomial.eval_monomial,
    one_pow, mul_one]
  rw [show (i : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (i : K) by simp]
  rw [mul_comm (Q.coeff i)]
  rw [MvPolynomial.coeff_C_mul]
  rw [mul_comm]

/-- The concrete source coefficient with new longitudinal exponent `1` is
the first Taylor coefficient of its fixed transverse longitudinal fibre. -/
theorem coeff_cons_one_longitudinalRightRecenterHom
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.coeff (m.cons 1)
        (longitudinalRightRecenterHom (K := K) F) =
      (longitudinalCoefficientPolynomialAt m F).derivative.eval 1 := by
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff m
    (longitudinalRightRecenterHom (K := K) F) 1]
  rw [finSuccEquiv_longitudinalRightRecenterHom]
  rw [Polynomial.taylor_coeff_one]
  exact coeff_eval_derivative_finSuccEquiv_eq m F

/-- A nonzero first Taylor coefficient is therefore an actual multivariate
support point, without any minimality claim. -/
theorem cons_one_mem_support_longitudinalRightRecenterHom
    (m : Fin 3 →₀ ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hfirst :
      (longitudinalCoefficientPolynomialAt m F).derivative.eval 1 ≠ 0) :
    m.cons 1 ∈ (longitudinalRightRecenterHom (K := K) F).support := by
  rw [MvPolynomial.mem_support_iff]
  rw [coeff_cons_one_longitudinalRightRecenterHom]
  exact hfirst

/-- The support witness retains exactly the fixed transverse Smith exponent;
longitudinal recentering does not mix transverse fibres. -/
theorem smithSupportExponentOf_cons_one_smithTransverseExponent
    (e : SmithSupportExponent) :
    ((smithTransverseExponent e.b e.c e.d).cons 1) (1 : Fin 4) = e.b ∧
    ((smithTransverseExponent e.b e.c e.d).cons 1) (2 : Fin 4) = e.c ∧
    ((smithTransverseExponent e.b e.c e.d).cons 1) (3 : Fin 4) = e.d := by
  constructor
  · change ((smithTransverseExponent e.b e.c e.d).cons 1)
        (Fin.succ (0 : Fin 3)) = e.b
    rw [Finsupp.cons_succ]
    exact smithTransverseExponent_zero e.b e.c e.d
  · constructor
    · change ((smithTransverseExponent e.b e.c e.d).cons 1)
          (Fin.succ (1 : Fin 3)) = e.c
      rw [Finsupp.cons_succ]
      exact smithTransverseExponent_one e.b e.c e.d
    · change ((smithTransverseExponent e.b e.c e.d).cons 1)
          (Fin.succ (2 : Fin 3)) = e.d
      rw [Finsupp.cons_succ]
      exact smithTransverseExponent_two e.b e.c e.d

/-- The transverse coordinates are unchanged for every longitudinal source
exponent, not only for the first recentered layer. -/
theorem smithSupportExponentOf_cons_smithTransverseExponent
    (e : SmithSupportExponent) (n : ℕ) :
    ((smithTransverseExponent e.b e.c e.d).cons n) (1 : Fin 4) = e.b ∧
    ((smithTransverseExponent e.b e.c e.d).cons n) (2 : Fin 4) = e.c ∧
    ((smithTransverseExponent e.b e.c e.d).cons n) (3 : Fin 4) = e.d := by
  constructor
  · change ((smithTransverseExponent e.b e.c e.d).cons n)
        (Fin.succ (0 : Fin 3)) = e.b
    rw [Finsupp.cons_succ]
    exact smithTransverseExponent_zero e.b e.c e.d
  · constructor
    · change ((smithTransverseExponent e.b e.c e.d).cons n)
          (Fin.succ (1 : Fin 3)) = e.c
      rw [Finsupp.cons_succ]
      exact smithTransverseExponent_one e.b e.c e.d
    · change ((smithTransverseExponent e.b e.c e.d).cons n)
          (Fin.succ (2 : Fin 3)) = e.d
      rw [Finsupp.cons_succ]
      exact smithTransverseExponent_two e.b e.c e.d

/-- A two-endpoint blocker with nonvanishing residual value produces the
promised concrete support point in the actually recentered multivariate
polynomial.  Its transverse coordinates are exactly the original projected
Smith exponent. -/
theorem twoEndpointResidual_exactFirst_recenteredSupportWitness
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (B : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hBfirst : Polynomial.eval 1 B ≠ 0) :
    let d := (smithTransverseExponent e.b e.c e.d).cons 1
    d ∈ (longitudinalRightRecenterHom (K := K) F).support ∧
      d (1 : Fin 4) = e.b ∧
      d (2 : Fin 4) = e.c ∧
      d (3 : Fin 4) = e.d := by
  dsimp only
  have hderivative :
      (longitudinalCoefficientPolynomial e.b e.c e.d F).derivative.eval 1 =
        Polynomial.eval 1 B := by
    rw [hfactor]
    simp [Polynomial.derivative_mul]
  refine ⟨cons_one_mem_support_longitudinalRightRecenterHom
      (smithTransverseExponent e.b e.c e.d) F ?_, ?_⟩
  · rw [longitudinalCoefficientPolynomial] at hderivative
    intro hzero
    apply hBfirst
    rw [← hderivative]
    exact hzero
  · exact smithSupportExponentOf_cons_one_smithTransverseExponent e

/-- Axis restriction is exactly the longitudinal coefficient polynomial over
the zero transverse exponent. -/
theorem longitudinalAxisRestriction_eq_coefficient_zero
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestriction F =
      longitudinalCoefficientPolynomialAt 0 F := by
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt]
  simp only [longitudinalAxisRestriction, Polynomial.coeff_map]
  rw [MvPolynomial.eval_zero']
  rw [MvPolynomial.constantCoeff_eq]

/-- Evaluation on the distinguished axis is univariate evaluation of the
axis restriction. -/
theorem eval_finCons_zero_eq_longitudinalAxisRestriction
    (F : MvPolynomial (Fin 4) K)
    (x : K) :
    MvPolynomial.eval (Fin.cons x (fun _ : Fin 3 => (0 : K))) F =
      Polynomial.eval x (longitudinalAxisRestriction F) := by
  rw [MvPolynomial.eval_eq_eval_mv_eval']
  rfl

/-- The coefficient polynomial of a transverse-linear block is the axis
restriction of the corresponding transverse derivative. -/
theorem longitudinalCoefficient_single_eq_axisRestriction_pderiv
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) K) :
    longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F =
      longitudinalAxisRestriction (MvPolynomial.pderiv j.succ F) := by
  rw [longitudinalAxisRestriction_eq_coefficient_zero]
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
  rw [coeff_pderiv_mixedDegree (K := K) j.succ F
    ((0 : Fin 3 →₀ ℕ).cons a)]
  have hexponent :
      (0 : Fin 3 →₀ ℕ).cons a + Finsupp.single j.succ 1 =
        (Finsupp.single j 1).cons a := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · by_cases hjk : j = k
      · subst k
        simp
      · simp [hjk]
  rw [hexponent]
  simp

/-- Exact transverse-gradient identity on the longitudinal axis. -/
theorem eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) K)
    (x : K) :
    MvPolynomial.eval (Fin.cons x (fun _ : Fin 3 => (0 : K)))
        (MvPolynomial.pderiv j.succ F) =
      Polynomial.eval x
        (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F) := by
  rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
    longitudinalCoefficient_single_eq_axisRestriction_pderiv]

/-! ## Pure longitudinal derivative -/

/-- Differentiation in source coordinate `0` becomes ordinary univariate
differentiation after restriction to the distinguished axis. -/
theorem longitudinalAxisRestriction_pderiv_zero
    (F : MvPolynomial (Fin 4) K) :
    longitudinalAxisRestriction (MvPolynomial.pderiv (0 : Fin 4) F) =
      (longitudinalAxisRestriction F).derivative := by
  rw [longitudinalAxisRestriction_eq_coefficient_zero,
    longitudinalAxisRestriction_eq_coefficient_zero]
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    coeff_pderiv_mixedDegree]
  rw [Polynomial.coeff_derivative,
    coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
  have hexponent :
      (0 : Fin 3 →₀ ℕ).cons a + Finsupp.single (0 : Fin 4) 1 =
        (0 : Fin 3 →₀ ℕ).cons (a + 1) := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp
  rw [hexponent]
  simp [mul_comm]

/-- The longitudinal gradient on the axis is evaluation of the derivative
of the axis restriction. -/
theorem eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative
    (F : MvPolynomial (Fin 4) K)
    (x : K) :
    MvPolynomial.eval (Fin.cons x (fun _ : Fin 3 => (0 : K)))
        (MvPolynomial.pderiv (0 : Fin 4) F) =
      Polynomial.eval x (longitudinalAxisRestriction F).derivative := by
  rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
    longitudinalAxisRestriction_pderiv_zero]

/-! ## Smith-pattern coordinate adapter -/

/-- The old `w`-linear Smith pattern is exactly transverse exponent
`single 2 1`; its endpoint algebra is therefore the uniform `j = 2` case. -/
theorem smithTransverseExponent_eq_single_two_of_wLinear
    (e : SmithSupportExponent)
    (hpat : IsWLinearSmithPattern e) :
    smithTransverseExponent e.b e.c e.d = Finsupp.single 2 1 := by
  rcases hpat with ⟨hb, hc, hd⟩
  simp [smithTransverseExponent, hb, hc, hd]

theorem smithTransverseExponent_eq_single_one_of_lowNegativeFirst
    (e : SmithSupportExponent)
    (hpat : IsLowNegativeFirstSmithPattern e) :
    smithTransverseExponent e.b e.c e.d = Finsupp.single 1 1 := by
  rcases hpat with ⟨hb, hc, hd⟩
  simp [smithTransverseExponent, hb, hc, hd]

theorem smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
    (e : SmithSupportExponent)
    (hpat : IsLowNegativeSecondSmithPattern e) :
    smithTransverseExponent e.b e.c e.d = Finsupp.single 0 1 := by
  rcases hpat with ⟨hb, hc, hd⟩
  simp [smithTransverseExponent, hb, hc, hd]

theorem smithTransverseExponent_eq_zero_of_pureLongitudinal
    (e : SmithSupportExponent)
    (hpat : IsPureLongitudinalSmithPattern e) :
    smithTransverseExponent e.b e.c e.d = 0 := by
  rcases hpat with ⟨hb, hc, hd⟩
  simp [smithTransverseExponent, hb, hc, hd]

/-! ## Exact collision and endpoint divisibility -/

section Field

variable {L : Type*} [Field L]

/-- Every exponent in the canonical projected Smith support gives a nonzero
longitudinal coefficient polynomial.  This is the mixed-degree replacement
for reconstructing a single longitudinal monomial by homogeneity. -/
theorem longitudinalCoefficientPolynomial_ne_zero_of_mem_projectedSupport
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F) :
    longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 := by
  rcases smithProjectedSupport_realised (1 : Fin 4) 2 3 F e he with
    ⟨d, hd, hproj⟩
  intro hzero
  have hcoeffZero := congrArg (fun A : Polynomial L => A.coeff (d 0)) hzero
  dsimp at hcoeffZero
  rw [coeff_longitudinalCoefficientPolynomial] at hcoeffZero
  have hexponent :
      (smithTransverseExponent e.b e.c e.d).cons (d 0) = d := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · fin_cases k
      · rw [Finsupp.cons_succ]
        simpa [smithTransverseExponent, smithSupportExponentOf] using
          congrArg SmithSupportExponent.b hproj.symm
      · rw [Finsupp.cons_succ]
        simpa [smithTransverseExponent, smithSupportExponentOf] using
          congrArg SmithSupportExponent.c hproj.symm
      · rw [Finsupp.cons_succ]
        simpa [smithTransverseExponent, smithSupportExponentOf] using
          congrArg SmithSupportExponent.d hproj.symm
  rw [hexponent] at hcoeffZero
  simp at hcoeffZero
  exact hd hcoeffZero

/-- Projected Smith support is exactly nonvanishing of the corresponding
longitudinal coefficient polynomial. -/
theorem longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent) :
    longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 ↔
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F := by
  rcases e with ⟨b, c, d⟩
  constructor
  · intro hne
    let a := (longitudinalCoefficientPolynomial b c d F).natDegree
    have hcoeff :
        (longitudinalCoefficientPolynomial b c d F).coeff a ≠ 0 := by
      exact Polynomial.leadingCoeff_ne_zero.mpr hne
    have hsource :
        MvPolynomial.coeff
          ((smithTransverseExponent b c d).cons a) F ≠ 0 := by
      rw [← coeff_longitudinalCoefficientPolynomial]
      exact hcoeff
    classical
    unfold smithProjectedSupport
    apply Finset.mem_image.mpr
    refine ⟨(smithTransverseExponent b c d).cons a,
      MvPolynomial.mem_support_iff.mpr hsource, ?_⟩
    simp only [smithSupportExponentOf]
    congr 1
    · change ((smithTransverseExponent b c d).cons a) (Fin.succ 0) = b
      rw [Finsupp.cons_succ]
      simp
    · change ((smithTransverseExponent b c d).cons a) (Fin.succ 1) = c
      rw [Finsupp.cons_succ]
      simp
    · change ((smithTransverseExponent b c d).cons a) (Fin.succ 2) = d
      rw [Finsupp.cons_succ]
      simp
  · exact longitudinalCoefficientPolynomial_ne_zero_of_mem_projectedSupport
      F ⟨b, c, d⟩

/-- Longitudinal translation can create or cancel individual source
monomials, but it preserves exactly the Smith support after forgetting the
longitudinal exponent. -/
theorem smithProjectedSupport_longitudinalRightRecenterHom
    (F : MvPolynomial (Fin 4) L) :
    smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom (K := L) F) =
      smithProjectedSupport (1 : Fin 4) 2 3 F := by
  classical
  ext e
  have htaylor :
      Polynomial.taylor 1
          (longitudinalCoefficientPolynomial e.b e.c e.d F) ≠ 0 ↔
        longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 :=
    not_congr (Polynomial.taylor_eq_zero (1 : L)
      (longitudinalCoefficientPolynomial e.b e.c e.d F))
  rw [← longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport,
    longitudinalCoefficientPolynomial_longitudinalRightRecenterHom,
    htaylor,
    longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport]

/-- In the mixed-degree setting, raw collision on the distinguished axis
gives equality of the two endpoint values of each transverse-linear
coefficient polynomial.  It does not by itself make either value zero. -/
theorem longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0))) :
    Polynomial.eval 1
        (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F) =
      Polynomial.eval 0
        (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F) := by
  rw [← eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single,
    ← eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
  exact (hcoll j.succ).symm

/-- If the left transverse gradient is normalized to zero, exact collision
makes the right endpoint value zero as well. -/
theorem longitudinalCoefficient_single_eval_one_eq_zero_of_collision
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv j.succ F) = 0) :
    Polynomial.eval 1
        (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F) = 0 := by
  rw [longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
    j F hcoll]
  rw [← eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
  exact hzero

/-- Clean endpoint factorization after zero-gradient normalization. -/
theorem X_sub_one_dvd_longitudinalCoefficient_single_of_collision
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv j.succ F) = 0) :
    Polynomial.X - Polynomial.C 1 ∣
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F := by
  let A := longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F
  have hdvd :
      Polynomial.X - Polynomial.C (1 : L) ∣
        A - Polynomial.C (Polynomial.eval 1 A) :=
    Polynomial.X_sub_C_dvd_sub_C_eval
  have heval : Polynomial.eval 1 A = 0 :=
    longitudinalCoefficient_single_eval_one_eq_zero_of_collision
      j F hcoll hzero
  simpa [A, heval] using hdvd

/-- Zero gradient at the left endpoint supplies the missing factor `X` in
every transverse-linear longitudinal coefficient. -/
theorem X_dvd_longitudinalCoefficient_single_of_zeroGradient
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) L)
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv j.succ F) = 0) :
    Polynomial.X ∣
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F := by
  let A := longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F
  have hdvd :=
    Polynomial.X_sub_C_dvd_sub_C_eval (p := A) (a := (0 : L))
  have heval : Polynomial.eval 0 A = 0 := by
    rw [← eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    exact hzero
  simpa [A, heval] using hdvd

/-- The two normalized collision endpoints are coprime, so every
transverse-linear blocker contains their product. -/
theorem X_mul_X_sub_one_dvd_longitudinalCoefficient_single_of_collision
    (j : Fin 3)
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv j.succ F) = 0) :
    Polynomial.X * (Polynomial.X - Polynomial.C 1) ∣
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F := by
  have hcoprime :
      IsCoprime Polynomial.X
        (Polynomial.X - Polynomial.C (1 : L)) := by
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : L)) (b := (1 : L)) (by simp))
  exact hcoprime.mul_dvd
    (X_dvd_longitudinalCoefficient_single_of_zeroGradient j F hzero)
    (X_sub_one_dvd_longitudinalCoefficient_single_of_collision
      j F hcoll hzero)

/-- Zero-gradient normalization makes the derivative of the pure
longitudinal axis restriction vanish at the left endpoint. -/
theorem axisRestriction_derivative_eval_zero_eq_zero
    (F : MvPolynomial (Fin 4) L)
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv (0 : Fin 4) F) = 0) :
    Polynomial.eval 0 (longitudinalAxisRestriction F).derivative = 0 := by
  rw [← eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
  exact hzero

/-- Exact collision transfers the normalized longitudinal derivative
vanishing to the right endpoint. -/
theorem axisRestriction_derivative_eval_one_eq_zero
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv (0 : Fin 4) F) = 0) :
    Polynomial.eval 1 (longitudinalAxisRestriction F).derivative = 0 := by
  rw [← eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
  exact (hcoll 0).symm.trans hzero

/-- The normalized left endpoint supplies the factor `X` in `L'`. -/
theorem X_dvd_axisRestriction_derivative
    (F : MvPolynomial (Fin 4) L)
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv (0 : Fin 4) F) = 0) :
    Polynomial.X ∣ (longitudinalAxisRestriction F).derivative := by
  have hdvd :=
    Polynomial.X_sub_C_dvd_sub_C_eval
      (p := (longitudinalAxisRestriction F).derivative) (a := (0 : L))
  have heval := axisRestriction_derivative_eval_zero_eq_zero F hzero
  simpa [heval] using hdvd

/-- The collided right endpoint supplies the factor `X - 1` in `L'`. -/
theorem X_sub_one_dvd_axisRestriction_derivative
    (F : MvPolynomial (Fin 4) L)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (MvPolynomial.pderiv (0 : Fin 4) F) = 0) :
    Polynomial.X - Polynomial.C 1 ∣
      (longitudinalAxisRestriction F).derivative := by
  have hdvd :=
    Polynomial.X_sub_C_dvd_sub_C_eval
      (p := (longitudinalAxisRestriction F).derivative) (a := (1 : L))
  have heval :=
    axisRestriction_derivative_eval_one_eq_zero F hcoll hzero
  simpa [heval] using hdvd

/-! ## Packaged mixed-degree Smith blockers -/

/-- A projected transverse-linear Smith blocker supplies a nonzero
longitudinal coefficient polynomial with the normalized endpoint factor.
The hypothesis identifying its transverse exponent is kept explicit so the
three old blocker patterns can share one proof. -/
theorem projectedSupport_transverseLinear_factorData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (j : Fin 3)
    (htransverse :
      smithTransverseExponent e.b e.c e.d = Finsupp.single j 1)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A : Polynomial L,
      A ≠ 0 ∧
      A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
      Polynomial.X - Polynomial.C 1 ∣ A := by
  refine ⟨longitudinalCoefficientPolynomial e.b e.c e.d F,
    longitudinalCoefficientPolynomial_ne_zero_of_mem_projectedSupport
      F e he, rfl, ?_⟩
  have hdvd :=
    X_sub_one_dvd_longitudinalCoefficient_single_of_collision
      j F hcoll (hzero j.succ)
  simpa [longitudinalCoefficientPolynomial, htransverse] using hdvd

/-- The old `w`-linear zero-grade blocker is the `j = 2` instance of the
uniform transverse package. -/
theorem projectedSupport_wLinear_factorData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hpat : IsWLinearSmithPattern e)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A : Polynomial L,
      A ≠ 0 ∧ A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
        Polynomial.X - Polynomial.C 1 ∣ A :=
  projectedSupport_transverseLinear_factorData F e he 2
    (smithTransverseExponent_eq_single_two_of_wLinear e hpat) hcoll hzero

/-- Mixed-degree replacement for the first old low-negative blocker. -/
theorem projectedSupport_lowNegativeFirst_factorData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hpat : IsLowNegativeFirstSmithPattern e)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A : Polynomial L,
      A ≠ 0 ∧ A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
        Polynomial.X - Polynomial.C 1 ∣ A :=
  projectedSupport_transverseLinear_factorData F e he 1
    (smithTransverseExponent_eq_single_one_of_lowNegativeFirst e hpat)
    hcoll hzero

/-- Mixed-degree replacement for the second old low-negative blocker. -/
theorem projectedSupport_lowNegativeSecond_factorData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hpat : IsLowNegativeSecondSmithPattern e)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A : Polynomial L,
      A ≠ 0 ∧ A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
        Polynomial.X - Polynomial.C 1 ∣ A :=
  projectedSupport_transverseLinear_factorData F e he 0
    (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond e hpat)
    hcoll hzero

/-- A projected pure-longitudinal blocker supplies a nonzero axis
restriction; the derivative of that restriction has both normalized
endpoint factors.  Nonvanishing of the derivative is deliberately not
claimed here, since projected support alone does not exclude a constant
axis term. -/
theorem projectedSupport_pureLongitudinal_factorData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hpat : IsPureLongitudinalSmithPattern e)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A : Polynomial L,
      A ≠ 0 ∧ A = longitudinalAxisRestriction F ∧
        Polynomial.X ∣ A.derivative ∧
        Polynomial.X - Polynomial.C 1 ∣ A.derivative := by
  have htransverse :=
    smithTransverseExponent_eq_zero_of_pureLongitudinal e hpat
  have hne :=
    longitudinalCoefficientPolynomial_ne_zero_of_mem_projectedSupport F e he
  have haxis :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        longitudinalAxisRestriction F := by
    rw [longitudinalAxisRestriction_eq_coefficient_zero]
    simp [longitudinalCoefficientPolynomial, htransverse]
  refine ⟨longitudinalAxisRestriction F, ?_, rfl,
    X_dvd_axisRestriction_derivative F (hzero 0),
    X_sub_one_dvd_axisRestriction_derivative F hcoll (hzero 0)⟩
  rw [← haxis]
  exact hne

/-! ## Residual endpoint complexity -/

/-- Removing a forced endpoint factor from a nonzero longitudinal
coefficient produces a nonzero residual polynomial of strictly smaller
univariate degree.  This is only an algebraic complexity drop: no geometric
restart or source-degree decrease is asserted. -/
theorem exists_endpointResidual_natDegree_lt
    (A : Polynomial L)
    (hA : A ≠ 0)
    (hdvd : Polynomial.X - Polynomial.C 1 ∣ A) :
    ∃ B : Polynomial L,
      B ≠ 0 ∧
      A = (Polynomial.X - Polynomial.C 1) * B ∧
      B.natDegree < A.natDegree := by
  rcases hdvd with ⟨B, hB⟩
  have hBne : B ≠ 0 := by
    intro hzero
    subst B
    simp at hB
    exact hA hB
  refine ⟨B, hBne, hB, ?_⟩
  have hfactor : Polynomial.X - Polynomial.C (1 : L) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero 1
  rw [hB, Polynomial.natDegree_mul hfactor hBne,
    Polynomial.natDegree_X_sub_C]
  omega

/-- Removing both forced collision-endpoint factors lowers longitudinal
degree by two. -/
theorem exists_twoEndpointResidual_natDegree_lt
    (A : Polynomial L)
    (hA : A ≠ 0)
    (hdvd : Polynomial.X * (Polynomial.X - Polynomial.C 1) ∣ A) :
    ∃ B : Polynomial L,
      B ≠ 0 ∧
      A = (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B ∧
      B.natDegree + 2 = A.natDegree := by
  rcases hdvd with ⟨B, hB⟩
  have hfactor :
      Polynomial.X * (Polynomial.X - Polynomial.C (1 : L)) ≠ 0 :=
    mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)
  have hBne : B ≠ 0 := by
    intro hzero
    subst B
    simp at hB
    exact hA hB
  refine ⟨B, hBne, hB, ?_⟩
  rw [hB, Polynomial.natDegree_mul hfactor hBne,
    Polynomial.natDegree_mul (by simp : (Polynomial.X : Polynomial L) ≠ 0)
      (Polynomial.X_sub_C_ne_zero 1),
    Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]
  omega

/-- Projected transverse Smith support, normalized collision, and the
coordinate adapter together yield a nonzero two-endpoint residual. -/
theorem projectedSupport_transverseLinear_twoEndpointResidualData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (j : Fin 3)
    (htransverse :
      smithTransverseExponent e.b e.c e.d = Finsupp.single j 1)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A B : Polynomial L,
      A ≠ 0 ∧
      A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
      B ≠ 0 ∧
      A = (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B ∧
      B.natDegree + 2 = A.natDegree := by
  let A := longitudinalCoefficientPolynomial e.b e.c e.d F
  have hA : A ≠ 0 :=
    longitudinalCoefficientPolynomial_ne_zero_of_mem_projectedSupport F e he
  have hdvdSingle :=
    X_mul_X_sub_one_dvd_longitudinalCoefficient_single_of_collision
      j F hcoll (hzero j.succ)
  have hdvd : Polynomial.X * (Polynomial.X - Polynomial.C 1) ∣ A := by
    simpa [A, longitudinalCoefficientPolynomial, htransverse] using hdvdSingle
  rcases exists_twoEndpointResidual_natDegree_lt A hA hdvd with
    ⟨B, hB, hfactor, hdegree⟩
  exact ⟨A, B, hA, rfl, hB, hfactor, hdegree⟩

/-- At the recentered endpoint, a residual either has a nonzero exact first
coefficient or acquires another `X - 1` factor. -/
theorem endpointResidual_eval_one_ne_zero_or_extraFactor
    (B : Polynomial L) :
    Polynomial.eval 1 B ≠ 0 ∨
      Polynomial.X - Polynomial.C 1 ∣ B := by
  by_cases h : Polynomial.eval 1 B = 0
  · right
    have hdvd :=
      Polynomial.X_sub_C_dvd_sub_C_eval (p := B) (a := (1 : L))
    simpa [h] using hdvd
  · exact Or.inl h

/-! ## Recentring a two-endpoint residual -/

/-- Exact univariate identity after moving the right endpoint `1` to the
new origin. -/
theorem taylor_one_twoEndpointResidual
    (B : Polynomial L) :
    Polynomial.taylor 1
        (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B) =
      Polynomial.X * (Polynomial.X + Polynomial.C 1) *
        Polynomial.taylor 1 B := by
  simp only [Polynomial.taylor_mul, Polynomial.taylor_X,
    map_sub, Polynomial.taylor_C]
  ring

/-- The recentered two-endpoint expression has zero constant coefficient. -/
theorem coeff_zero_taylor_one_twoEndpointResidual
    (B : Polynomial L) :
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 0 = 0 := by
  rw [Polynomial.taylor_coeff_zero]
  simp

/-- Its coefficient of the first local coordinate is exactly the residual
value `B(1)`. -/
theorem coeff_one_taylor_one_twoEndpointResidual
    (B : Polynomial L) :
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 1 =
        Polynomial.eval 1 B := by
  rw [Polynomial.taylor_coeff_one]
  simp [Polynomial.derivative_mul]

/-- Consequently a nonzero residual value gives an explicit exact
first-order recentered term.  This does not yet assert minimality among all
Smith patterns of a multivariate family. -/
theorem recentered_twoEndpointResidual_exactOrderOneCoefficients
    (B : Polynomial L)
    (hB : Polynomial.eval 1 B ≠ 0) :
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 0 = 0 ∧
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 1 ≠ 0 := by
  exact ⟨coeff_zero_taylor_one_twoEndpointResidual B,
    coeff_one_taylor_one_twoEndpointResidual B ▸ hB⟩

/-- Complete algebraic recentering dichotomy.  Either the candidate has an
exact nonzero first local coefficient, or another endpoint factor can be
removed, producing a nonzero residual whose degree drops by one. -/
theorem recenteredBlocker_exactFirstLayer_or_strictResidual
    (B : Polynomial L)
    (hB : B ≠ 0) :
    ((Polynomial.taylor 1
        (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 0 = 0 ∧
      (Polynomial.taylor 1
        (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff 1 ≠ 0) ∨
      ∃ C : Polynomial L,
        C ≠ 0 ∧
        B = (Polynomial.X - Polynomial.C 1) * C ∧
        C.natDegree + 1 = B.natDegree := by
  rcases endpointResidual_eval_one_ne_zero_or_extraFactor B with
    hfirst | hextra
  · exact Or.inl
      (recentered_twoEndpointResidual_exactOrderOneCoefficients B hfirst)
  · right
    rcases hextra with ⟨C, hCeq⟩
    have hfactor : Polynomial.X - Polynomial.C (1 : L) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero 1
    have hC : C ≠ 0 := by
      intro hzero
      subst C
      simp at hCeq
      exact hB hCeq
    refine ⟨C, hC, hCeq, ?_⟩
    rw [hCeq, Polynomial.natDegree_mul hfactor hC,
      Polynomial.natDegree_X_sub_C]
    omega

/-- Normal form reached by the inner endpoint-residual recursion.  The
geometry is unchanged: only all further copies of the right-endpoint factor
`X - 1` have been removed. -/
structure EndpointResidualNormalForm (B : Polynomial L) where
  multiplicity : ℕ
  terminal : Polynomial L
  terminal_ne_zero : terminal ≠ 0
  terminal_eval_one_ne_zero : Polynomial.eval 1 terminal ≠ 0
  factorization :
    B = (Polynomial.X - Polynomial.C 1) ^ multiplicity * terminal
  degree_eq : terminal.natDegree + multiplicity = B.natDegree

/-- Repeated endpoint stripping terminates by strict `natDegree` descent.
This is the honest inner recursion available from the blocker certificates;
it deliberately constructs no new geometric family. -/
theorem exists_endpointResidualNormalForm
    (B : Polynomial L) (hB : B ≠ 0) :
    Nonempty (EndpointResidualNormalForm B) := by
  induction hdegree : B.natDegree using Nat.strong_induction_on generalizing B with
  | h n ih =>
      rcases endpointResidual_eval_one_ne_zero_or_extraFactor B with hterminal | hdvd
      · exact ⟨
          { multiplicity := 0
            terminal := B
            terminal_ne_zero := hB
            terminal_eval_one_ne_zero := hterminal
            factorization := by simp
            degree_eq := by simp }⟩
      · rcases exists_endpointResidual_natDegree_lt B hB hdvd with
          ⟨C, hC, hfactor, hlt⟩
        have hCdegree : C.natDegree < n := by simpa [hdegree] using hlt
        rcases ih C.natDegree hCdegree C hC rfl with ⟨hnormal⟩
        exact ⟨
          { multiplicity := hnormal.multiplicity + 1
            terminal := hnormal.terminal
            terminal_ne_zero := hnormal.terminal_ne_zero
            terminal_eval_one_ne_zero := hnormal.terminal_eval_one_ne_zero
            factorization := by
              calc
                B = (Polynomial.X - Polynomial.C 1) * C := hfactor
                _ = (Polynomial.X - Polynomial.C 1) *
                    ((Polynomial.X - Polynomial.C 1) ^
                      hnormal.multiplicity * hnormal.terminal) := by
                      exact congrArg
                        (fun Z => (Polynomial.X - Polynomial.C 1) * Z)
                        hnormal.factorization
                _ = (Polynomial.X - Polynomial.C 1) ^
                      (hnormal.multiplicity + 1) * hnormal.terminal := by
                      rw [pow_succ]
                      ring
            degree_eq := by
              have hstep : B.natDegree = 1 + C.natDegree := by
                rw [hfactor, Polynomial.natDegree_mul
                  (Polynomial.X_sub_C_ne_zero (1 : L)) hC,
                  Polynomial.natDegree_X_sub_C]
              have hterminalDegree := hnormal.degree_eq
              omega }⟩

/-- The terminal residual identifies the exact first nonzero layer after
right-endpoint recentering.  If `q` further copies of `X - 1` were stripped,
the first layer occurs at order `q + 1`; no new family is introduced. -/
theorem EndpointResidualNormalForm.exactRecenteredLayer
    {B : Polynomial L} (h : EndpointResidualNormalForm B) :
    (∀ k < h.multiplicity + 1,
      (Polynomial.taylor 1
        (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff k = 0) ∧
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff
        (h.multiplicity + 1) = Polynomial.eval 1 h.terminal ∧
    (Polynomial.taylor 1
      (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B)).coeff
        (h.multiplicity + 1) ≠ 0 := by
  let G := (Polynomial.X + Polynomial.C 1) * Polynomial.taylor 1 h.terminal
  have htaylorB :
      Polynomial.taylor 1 B =
        Polynomial.X ^ h.multiplicity * Polynomial.taylor 1 h.terminal := by
    calc
      Polynomial.taylor 1 B = Polynomial.taylor 1
          ((Polynomial.X - Polynomial.C 1) ^ h.multiplicity * h.terminal) :=
        congrArg (Polynomial.taylor 1) h.factorization
      _ = Polynomial.X ^ h.multiplicity *
          Polynomial.taylor 1 h.terminal := by
        simp [Polynomial.taylor_mul]
  have hidentity :
      Polynomial.taylor 1
          (Polynomial.X * (Polynomial.X - Polynomial.C 1) * B) =
        Polynomial.X ^ (h.multiplicity + 1) * G := by
    rw [taylor_one_twoEndpointResidual, htaylorB]
    dsimp [G]
    rw [pow_succ]
    ring
  constructor
  · intro k hk
    rw [hidentity, Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hk]
  · constructor
    · rw [hidentity, Polynomial.coeff_X_pow_mul']
      simp [G, Polynomial.taylor_coeff_zero]
    · rw [hidentity, Polynomial.coeff_X_pow_mul']
      simpa [G, Polynomial.taylor_coeff_zero] using
        h.terminal_eval_one_ne_zero

/-- The exact terminal layer is an actual source-support monomial of the
recentered polynomial, over the same transverse Smith exponent. -/
theorem endpointResidualNormalForm_recenteredSupportWitness
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (B : Polynomial L)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
    (hnormal : EndpointResidualNormalForm B) :
    let n := hnormal.multiplicity + 1
    let d := (smithTransverseExponent e.b e.c e.d).cons n
    d ∈ (longitudinalRightRecenterHom (K := L) F).support ∧
      d (1 : Fin 4) = e.b ∧
      d (2 : Fin 4) = e.c ∧
      d (3 : Fin 4) = e.d := by
  dsimp only
  have hlayer := hnormal.exactRecenteredLayer
  have hcoeff :
      (longitudinalCoefficientPolynomial e.b e.c e.d
        (longitudinalRightRecenterHom (K := L) F)).coeff
          (hnormal.multiplicity + 1) ≠ 0 := by
    rw [longitudinalCoefficientPolynomial_longitudinalRightRecenterHom,
      hfactor]
    exact hlayer.2.2
  refine ⟨MvPolynomial.mem_support_iff.mpr ?_, ?_⟩
  · rw [← coeff_longitudinalCoefficientPolynomial]
    exact hcoeff
  · exact smithSupportExponentOf_cons_smithTransverseExponent
      e (hnormal.multiplicity + 1)

/-- The transverse blocker package therefore always has a strictly smaller
residual polynomial.  Whether the Smith wall passes geometrically to this
residual is intentionally left to the survival/elimination analysis. -/
theorem projectedSupport_transverseLinear_residualData
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (j : Fin 3)
    (htransverse :
      smithTransverseExponent e.b e.c e.d = Finsupp.single j 1)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) :
    ∃ A B : Polynomial L,
      A ≠ 0 ∧
      A = longitudinalCoefficientPolynomial e.b e.c e.d F ∧
      B ≠ 0 ∧
      A = (Polynomial.X - Polynomial.C 1) * B ∧
      B.natDegree < A.natDegree := by
  rcases projectedSupport_transverseLinear_factorData
      F e he j htransverse hcoll hzero with ⟨A, hA, hAeq, hdvd⟩
  rcases exists_endpointResidual_natDegree_lt A hA hdvd with
    ⟨B, hB, hfactor, hdegree⟩
  exact ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩

/-- Pure-longitudinal endpoint factors split into the harmless constant
case and a nonzero residual of strictly smaller degree.  This is again only
univariate algebra; the later wall theorem must decide whether the residual
is the geometry actually exposed by recentering. -/
theorem pureLongitudinal_constant_or_derivativeResidual
    [CharZero L]
    (A : Polynomial L)
    (hX : Polynomial.X ∣ A.derivative)
    (hXone : Polynomial.X - Polynomial.C 1 ∣ A.derivative) :
    A = Polynomial.C (A.coeff 0) ∨
      ∃ C : Polynomial L,
        C ≠ 0 ∧
        A.derivative =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * C ∧
        C.natDegree < A.derivative.natDegree := by
  by_cases hderiv : A.derivative = 0
  · exact Or.inl (Polynomial.eq_C_of_derivative_eq_zero hderiv)
  · right
    have hcoprime :
        IsCoprime Polynomial.X
          (Polynomial.X - Polynomial.C (1 : L)) := by
      simpa using
        (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
          (a := (0 : L)) (b := (1 : L)) (by simp))
    have hproduct :
        Polynomial.X * (Polynomial.X - Polynomial.C (1 : L)) ∣
          A.derivative :=
      hcoprime.mul_dvd hX hXone
    rcases hproduct with ⟨C, hC⟩
    have hfactor :
        Polynomial.X * (Polynomial.X - Polynomial.C (1 : L)) ≠ 0 :=
      mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)
    have hCne : C ≠ 0 := by
      intro hzero
      subst C
      simp at hC
      exact hderiv hC
    refine ⟨C, hCne, hC, ?_⟩
    rw [hC, Polynomial.natDegree_mul hfactor hCne,
      Polynomial.natDegree_mul (by simp : (Polynomial.X : Polynomial L) ≠ 0)
        (Polynomial.X_sub_C_ne_zero 1),
      Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]
    omega

/-- With the zero-value normalization imposed as well, the constant branch
of a projected pure-longitudinal blocker is impossible.  Thus its
derivative always has a nonzero two-endpoint residual. -/
theorem projectedSupport_pureLongitudinal_twoEndpointResidualData
    [CharZero L]
    (F : MvPolynomial (Fin 4) L)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hpat : IsPureLongitudinalSmithPattern e)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : L) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : L) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : L) (fun _ : Fin 3 => 0)) F = 0) :
    ∃ A C : Polynomial L,
      A ≠ 0 ∧ A = longitudinalAxisRestriction F ∧
      C ≠ 0 ∧
      A.derivative =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * C ∧
      C.natDegree < A.derivative.natDegree := by
  rcases projectedSupport_pureLongitudinal_factorData
      F e he hpat hcoll hzero with ⟨A, hA, hAeq, hX, hXone⟩
  rcases pureLongitudinal_constant_or_derivativeResidual
      A hX hXone with hconstant | ⟨C, hC, hfactor, hdegree⟩
  · have hevalA : Polynomial.eval 0 A = 0 := by
      rw [hAeq]
      rw [← eval_finCons_zero_eq_longitudinalAxisRestriction]
      exact hvalue
    have hcoeff : A.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hevalA
    exfalso
    apply hA
    simpa [hcoeff] using hconstant
  · exact ⟨A, C, hA, hAeq, hC, hfactor, hdegree⟩

end Field

end

end HC4.Newton
