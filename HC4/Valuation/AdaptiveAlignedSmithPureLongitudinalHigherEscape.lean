import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalLinearEscape
import HC4.Polynomial.TopProduct
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Elimination of higher transverse support in the pure-longitudinal blocker

The previous green frontier leaves one finite possibility:

* the canonical blocker is pure longitudinal;
* every `2 x 2` minor of the finite right-recentered Hessian vanishes;
* the recentered fibre has positive transverse support;
* no transverse-linear projected support point occurs.

This file eliminates that possibility intrinsically, without JC2.

Use the transverse-order weight

    wt(x0) = 0,   wt(x1) = wt(x2) = wt(x3) = -1.

Let `m` be the least positive total transverse degree in the recentered
special fibre.  Linear transverse support has already been removed, hence
`m >= 2`.  The exact component `Q` of weight `-m` is nonzero.

The pure blocker residual gives a nonzero longitudinal Hessian pivot on the
axis.  Taking the weight `-m+2` component of the all-minors identity

    H00 Hij - H0j Hi0 = 0

shows that

    H00(axis) * (d_i d_j Q) = 0,

because both mixed factors on the right start at weight at most `-m+1`, so
their product starts strictly below `-m+2`.  Since the coefficient ring is a
domain and the axis pivot is nonzero, every transverse second derivative of
`Q` vanishes.

Finally, characteristic zero and exact transverse degree `m >= 2` force
`Q = 0`, contradicting its construction.  Thus the higher-support branch is
impossible: the pure-longitudinal blocker is either transverse-free or has
already entered one of the persistent quadratic packet exits.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## The transverse filtration -/

/-- Total exponent in the three Smith-transverse source variables. -/
def pureLongitudinalTransverseDegree (d : Fin 4 →₀ ℕ) : ℕ :=
  d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4)

/-- Negative transverse-order weight.  Highest weight means least transverse
order, while the longitudinal variable is invisible. -/
def pureLongitudinalTransverseWeight (i : Fin 4) : ℤ :=
  if i = 0 then 0 else -1

@[simp] theorem pureLongitudinalTransverseWeight_zero :
    pureLongitudinalTransverseWeight (0 : Fin 4) = 0 := by
  simp [pureLongitudinalTransverseWeight]

@[simp] theorem pureLongitudinalTransverseWeight_succ (j : Fin 3) :
    pureLongitudinalTransverseWeight j.succ = -1 := by
  simp [pureLongitudinalTransverseWeight]

/-- The negative weight is exactly minus total transverse degree. -/
theorem weight_pureLongitudinalTransverseWeight
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight pureLongitudinalTransverseWeight d =
      -(pureLongitudinalTransverseDegree d : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [pureLongitudinalTransverseWeight,
      pureLongitudinalTransverseDegree]
    ring
  · intro i
    simp

/-- Source monomials of genuinely positive transverse order. -/
def positiveTransverseSourceSupport
    (F : MvPolynomial (Fin 4) K) : Finset (Fin 4 →₀ ℕ) :=
  F.support.filter (fun d => 0 < pureLongitudinalTransverseDegree d)

/-- The least positive transverse source degree. -/
noncomputable def firstPositiveTransverseSourceDegree
    (F : MvPolynomial (Fin 4) K)
    (h : (positiveTransverseSourceSupport F).Nonempty) : ℕ :=
  ((positiveTransverseSourceSupport F).image
      pureLongitudinalTransverseDegree).min'
    (h.image pureLongitudinalTransverseDegree)

/-- The least positive degree is realised by an actual source monomial. -/
theorem exists_source_firstPositiveTransverseSourceDegree
    (F : MvPolynomial (Fin 4) K)
    (h : (positiveTransverseSourceSupport F).Nonempty) :
    ∃ d ∈ F.support,
      0 < pureLongitudinalTransverseDegree d ∧
      pureLongitudinalTransverseDegree d =
        firstPositiveTransverseSourceDegree F h := by
  have hmem :
      firstPositiveTransverseSourceDegree F h ∈
        (positiveTransverseSourceSupport F).image
          pureLongitudinalTransverseDegree := by
    unfold firstPositiveTransverseSourceDegree
    exact Finset.min'_mem _ (h.image pureLongitudinalTransverseDegree)
  rcases Finset.mem_image.mp hmem with ⟨d, hd, heq⟩
  have hd' := Finset.mem_filter.mp hd
  exact ⟨d, hd'.1, hd'.2, heq⟩

/-- Minimality among all positive-transverse source monomials. -/
theorem firstPositiveTransverseSourceDegree_le
    (F : MvPolynomial (Fin 4) K)
    (h : (positiveTransverseSourceSupport F).Nonempty)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ F.support)
    (hpos : 0 < pureLongitudinalTransverseDegree d) :
    firstPositiveTransverseSourceDegree F h ≤
      pureLongitudinalTransverseDegree d := by
  unfold firstPositiveTransverseSourceDegree
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨d, Finset.mem_filter.mpr ⟨hd, hpos⟩, rfl⟩

/-- A source monomial of transverse degree one projects to one of the three
pure transverse-linear Smith exponents. -/
theorem projectedSupport_linear_of_source_transverseDegree_one
    (F : MvPolynomial (Fin 4) K)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ F.support)
    (hdeg : pureLongitudinalTransverseDegree d = 1) :
    ({ b := 1, c := 0, d := 0 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3 F ∨
      ({ b := 0, c := 1, d := 0 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3 F ∨
      ({ b := 0, c := 0, d := 1 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3 F := by
  have hproj := smithSupportExponentOf_mem_projectedSupport F d hd
  have hcases :
      (d (1 : Fin 4) = 1 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
      (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 1 ∧ d (3 : Fin 4) = 0) ∨
      (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 1) := by
    unfold pureLongitudinalTransverseDegree at hdeg
    omega
  rcases hcases with hfirst | hsecond | hthird
  · left
    simpa [smithSupportExponentOf, hfirst.1, hfirst.2.1, hfirst.2.2]
      using hproj
  · right; left
    simpa [smithSupportExponentOf, hsecond.1, hsecond.2.1, hsecond.2.2]
      using hproj
  · right; right
    simpa [smithSupportExponentOf, hthird.1, hthird.2.1, hthird.2.2]
      using hproj

/-- Every polynomial has transverse weight at most zero. -/
theorem isWeightLE_zero_pureLongitudinalTransverseWeight
    (F : MvPolynomial (Fin 4) K) :
    IsWeightLE pureLongitudinalTransverseWeight 0 F := by
  intro d hd
  rw [weight_pureLongitudinalTransverseWeight]
  exact neg_nonpos.mpr (by positivity)

/-- After removing the transverse-degree-zero component, minimality of `m`
gives the exact weak upper bound `-m` on the remainder. -/
theorem remainder_isWeightLE_neg_firstPositiveTransverseSourceDegree
    (F : MvPolynomial (Fin 4) K)
    (h : (positiveTransverseSourceSupport F).Nonempty) :
    let m := firstPositiveTransverseSourceDegree F h
    let F0 := initialForm pureLongitudinalTransverseWeight 0 F
    IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ)) (F - F0) := by
  dsimp only
  intro d hd
  have hcoeffDiff : MvPolynomial.coeff d
      (F - initialForm pureLongitudinalTransverseWeight 0 F) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcoeffF : MvPolynomial.coeff d F ≠ 0 := by
    intro hz
    apply hcoeffDiff
    rw [MvPolynomial.coeff_sub, hz, coeff_initialForm]
    simp [hz]
  have hdF : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hcoeffF
  have hweight_ne_zero :
      Finsupp.weight pureLongitudinalTransverseWeight d ≠ 0 := by
    intro hw
    apply hcoeffDiff
    rw [MvPolynomial.coeff_sub, coeff_initialForm]
    simp [hw]
  have hdegpos : 0 < pureLongitudinalTransverseDegree d := by
    by_contra hnot
    have hdegzero : pureLongitudinalTransverseDegree d = 0 := by omega
    apply hweight_ne_zero
    rw [weight_pureLongitudinalTransverseWeight, hdegzero]
    simp
  have hle := firstPositiveTransverseSourceDegree_le F h hdF hdegpos
  have hleZ :
      (firstPositiveTransverseSourceDegree F h : ℤ) ≤
        (pureLongitudinalTransverseDegree d : ℤ) := by
    exact_mod_cast hle
  rw [weight_pureLongitudinalTransverseWeight]
  omega

/-- The first positive transverse exact component is genuinely nonzero. -/
theorem firstPositiveTransverseInitialForm_ne_zero
    (F : MvPolynomial (Fin 4) K)
    (h : (positiveTransverseSourceSupport F).Nonempty) :
    initialForm pureLongitudinalTransverseWeight
        (-(firstPositiveTransverseSourceDegree F h : ℤ)) F ≠ 0 := by
  rcases exists_source_firstPositiveTransverseSourceDegree F h with
    ⟨d, hd, _hpos, hdeg⟩
  have hcoeff : MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  intro hzero
  have hc :
      MvPolynomial.coeff d
          (initialForm pureLongitudinalTransverseWeight
            (-(firstPositiveTransverseSourceDegree F h : ℤ)) F) = 0 := by
    rw [hzero]
    simp
  rw [coeff_initialForm] at hc
  have hw :
      Finsupp.weight pureLongitudinalTransverseWeight d =
        -(firstPositiveTransverseSourceDegree F h : ℤ) := by
    rw [weight_pureLongitudinalTransverseWeight, hdeg]
  simp [hw, hcoeff] at hc

/-- The degree-zero exact component contains no transverse variables. -/
theorem pderiv_transverse_initialForm_zero_eq_zero
    (F : MvPolynomial (Fin 4) K)
    (j : Fin 3) :
    MvPolynomial.pderiv j.succ
      (initialForm pureLongitudinalTransverseWeight 0 F) = 0 := by
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hcoeff
  rw [coeff_initialForm] at hcoeff
  split at hcoeff
  next hw =>
    have hdegzero : pureLongitudinalTransverseDegree d = 0 := by
      rw [weight_pureLongitudinalTransverseWeight] at hw
      omega
    unfold pureLongitudinalTransverseDegree at hdegzero
    have : d j.succ = 0 := by
      fin_cases j <;> simp at hdegzero ⊢ <;> omega
    exact this
  next hne => simp at hcoeff

/-! ## A binary top-component product lemma -/

/-- Under weak upper bounds, the exact top component of a binary product is
the product of the exact top components. -/
theorem initialForm_mul_eq_mul_initialForm_of_isWeightLE
    {σ : Type*} [DecidableEq σ]
    {w : σ → ℤ} {a b : ℤ}
    {P Q : MvPolynomial σ K}
    (hP : IsWeightLE w a P)
    (hQ : IsWeightLE w b Q) :
    initialForm w (a + b) (P * Q) =
      initialForm w a P * initialForm w b Q := by
  let P0 := initialForm w a P
  let Q0 := initialForm w b Q
  have hP0hom : MvPolynomial.IsWeightedHomogeneous w P0 a := by
    exact initialForm_isWeightedHomogeneous w a P
  have hQ0hom : MvPolynomial.IsWeightedHomogeneous w Q0 b := by
    exact initialForm_isWeightedHomogeneous w b Q
  have hP0LE : IsWeightLE w a P0 :=
    isWeightLE_of_isWeightedHomogeneous hP0hom
  have hQ0LE : IsWeightLE w b Q0 :=
    isWeightLE_of_isWeightedHomogeneous hQ0hom
  have hPdiff : IsWeightLT w a (P - P0) := by
    simpa [P0] using sub_initialForm_isWeightLT hP
  have hQdiff : IsWeightLT w b (Q - Q0) := by
    simpa [Q0] using sub_initialForm_isWeightLT hQ
  have hdiff : IsWeightLT w (a + b) (P * Q - P0 * Q0) := by
    have h1 : IsWeightLT w (a + b) ((P - P0) * Q) :=
      hPdiff.mul_le hQ
    have h2 : IsWeightLT w (a + b) (P0 * (Q - Q0)) :=
      hP0LE.mul_lt hQdiff
    have hid : P * Q - P0 * Q0 =
        (P - P0) * Q + P0 * (Q - Q0) := by ring
    rw [hid]
    exact h1.add h2
  have hzero : initialForm w (a + b) (P * Q - P0 * Q0) = 0 :=
    initialForm_eq_zero_of_isWeightLT hdiff (le_refl _)
  have htopHom :
      MvPolynomial.IsWeightedHomogeneous w (P0 * Q0) (a + b) :=
    MvPolynomial.IsWeightedHomogeneous.mul hP0hom hQ0hom
  have htop : initialForm w (a + b) (P0 * Q0) = P0 * Q0 :=
    initialForm_eq_self_of_isWeightedHomogeneous htopHom
  have hdecomp : P * Q = (P * Q - P0 * Q0) + P0 * Q0 := by ring
  rw [hdecomp, initialForm_add, hzero, htop, zero_add]

/-! ## Negative transverse degree with zero transverse Hessian is impossible -/

/-- A nonzero exact transverse component of degree at least two cannot have
all transverse second partial derivatives zero in characteristic zero. -/
theorem eq_zero_of_transverseSecondDerivatives_zero_of_exactNegativeWeight
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hm : 2 ≤ m)
    (hhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)))
    (hsecond :
      ∀ i j : Fin 3,
        HC4.Polynomial.hessian Q i.succ j.succ = 0) :
    Q = 0 := by
  have hmZ : (2 : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hm
  have hfirst :
      ∀ i : Fin 3, MvPolynomial.pderiv i.succ Q = 0 := by
    intro i
    by_contra hne
    rcases MvPolynomial.support_nonempty.mpr hne with ⟨d, hd⟩
    have hcoeff : MvPolynomial.coeff d
        (MvPolynomial.pderiv i.succ Q) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hhomFirst := pderiv_isWeightedHomogeneous hhom i.succ
    have h1 : d (1 : Fin 4) = 0 :=
      exponent_eq_zero_of_pderiv_eq_zero
        (1 : Fin 4) (MvPolynomial.pderiv i.succ Q)
        (by
          have hz := hsecond i 0
          simpa [HC4.Polynomial.hessian_apply] using hz)
        d hcoeff
    have h2 : d (2 : Fin 4) = 0 :=
      exponent_eq_zero_of_pderiv_eq_zero
        (2 : Fin 4) (MvPolynomial.pderiv i.succ Q)
        (by
          have hz := hsecond i 1
          simpa [HC4.Polynomial.hessian_apply] using hz)
        d hcoeff
    have h3 : d (3 : Fin 4) = 0 :=
      exponent_eq_zero_of_pderiv_eq_zero
        (3 : Fin 4) (MvPolynomial.pderiv i.succ Q)
        (by
          have hz := hsecond i 2
          simpa [HC4.Polynomial.hessian_apply] using hz)
        d hcoeff
    have hw0 : Finsupp.weight pureLongitudinalTransverseWeight d = 0 := by
      rw [weight_pureLongitudinalTransverseWeight]
      simp [pureLongitudinalTransverseDegree, h1, h2, h3]
    have hw := hhomFirst hcoeff
    rw [hw0] at hw
    simp only [pureLongitudinalTransverseWeight_succ] at hw
    omega

  by_contra hQ
  rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d, hd⟩
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have h1 : d (1 : Fin 4) = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      (1 : Fin 4) Q (hfirst 0) d hcoeff
  have h2 : d (2 : Fin 4) = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      (2 : Fin 4) Q (hfirst 1) d hcoeff
  have h3 : d (3 : Fin 4) = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      (3 : Fin 4) Q (hfirst 2) d hcoeff
  have hw0 : Finsupp.weight pureLongitudinalTransverseWeight d = 0 := by
    rw [weight_pureLongitudinalTransverseWeight]
    simp [pureLongitudinalTransverseDegree, h1, h2, h3]
  have hw := hhom hcoeff
  rw [hw0] at hw
  omega

/-! ## The minimal positive transverse layer contradicts rank-one Hessian -/

/-- The degree-zero Hessian pivot remains nonzero after passing to the exact
weight-zero component. -/
theorem hessian_zero_zero_initialForm_zero_ne_zero_of_axisRestriction_ne_zero
    (G : MvPolynomial (Fin 4) K)
    (hpivot :
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) ≠ 0) :
    HC4.Polynomial.hessian
        (initialForm pureLongitudinalTransverseWeight 0 G)
        (0 : Fin 4) (0 : Fin 4) ≠ 0 := by
  intro hzero
  have hinit :
      initialForm pureLongitudinalTransverseWeight 0
          (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) = 0 := by
    have hh := hessian_initialForm_entry
      pureLongitudinalTransverseWeight 0 G (0 : Fin 4) (0 : Fin 4)
    have hh' :
        HC4.Polynomial.hessian
            (initialForm pureLongitudinalTransverseWeight 0 G) 0 0 =
          initialForm pureLongitudinalTransverseWeight 0
            (HC4.Polynomial.hessian G 0 0) := by
      simpa using hh
    rw [hzero] at hh'
    exact hh'.symm
  apply hpivot
  rw [longitudinalAxisRestriction_eq_coefficient_zero]
  ext a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
  let d : Fin 4 →₀ ℕ := (0 : Fin 3 →₀ ℕ).cons a
  have hc :
      MvPolynomial.coeff d
          (initialForm pureLongitudinalTransverseWeight 0
            (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4))) = 0 := by
    rw [hinit]
    simp
  rw [coeff_initialForm] at hc
  have hw : Finsupp.weight pureLongitudinalTransverseWeight d = 0 := by
    rw [weight_pureLongitudinalTransverseWeight]
    simp [pureLongitudinalTransverseDegree, d]
  simpa [d, hw] using hc

/-- If a positive transverse layer exists but no transverse-linear layer
exists, the all-minors identities contradict the nonzero longitudinal pivot.
This is the final finite-support elimination lemma for the pure blocker. -/
theorem higherTransverseSupport_impossible_of_axisPivot_of_allMinors
    (G : MvPolynomial (Fin 4) K)
    (hpivot :
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) ≠ 0)
    (hall :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l -
          HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j = 0)
    (hpos : (positiveTransverseSourceSupport G).Nonempty)
    (hlinearFree :
      ¬ (({ b := 1, c := 0, d := 0 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G ∨
          ({ b := 0, c := 1, d := 0 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G ∨
          ({ b := 0, c := 0, d := 1 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G)) :
    False := by
  let m := firstPositiveTransverseSourceDegree G hpos
  let G0 := initialForm pureLongitudinalTransverseWeight 0 G
  let R := G - G0
  let Q := initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) G

  have hmpos : 0 < m := by
    rcases exists_source_firstPositiveTransverseSourceDegree G hpos with
      ⟨d, _hd, hdegpos, hdeg⟩
    simpa [m, hdeg] using hdegpos

  have hm2 : 2 ≤ m := by
    have hmne1 : m ≠ 1 := by
      intro hm1
      rcases exists_source_firstPositiveTransverseSourceDegree G hpos with
        ⟨d, hd, _hdegpos, hdeg⟩
      have hproj := projectedSupport_linear_of_source_transverseDegree_one
        G hd (by simpa [m, hm1] using hdeg)
      exact hlinearFree hproj
    omega

  have hQne : Q ≠ 0 := by
    simpa [Q, m] using firstPositiveTransverseInitialForm_ne_zero G hpos

  have hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)) := by
    exact initialForm_isWeightedHomogeneous
      pureLongitudinalTransverseWeight (-(m : ℤ)) G

  have hG0trans :
      ∀ j : Fin 3, MvPolynomial.pderiv j.succ G0 = 0 := by
    intro j
    simpa [G0] using pderiv_transverse_initialForm_zero_eq_zero G j

  have hRLE :
      IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ)) R := by
    simpa [R, G0, m] using
      remainder_isWeightLE_neg_firstPositiveTransverseSourceDegree G hpos

  have hGLE : IsWeightLE pureLongitudinalTransverseWeight 0 G :=
    isWeightLE_zero_pureLongitudinalTransverseWeight G

  have hT00ne : HC4.Polynomial.hessian G0 0 0 ≠ 0 := by
    simpa [G0] using
      hessian_zero_zero_initialForm_zero_ne_zero_of_axisRestriction_ne_zero
        G hpivot

  have hsecond :
      ∀ i j : Fin 3, HC4.Polynomial.hessian Q i.succ j.succ = 0 := by
    intro i j

    have hGdecomp : G = R + G0 := by
      dsimp [R]
      ring

    have hG0ij : HC4.Polynomial.hessian G0 i.succ j.succ = 0 := by
      simp [HC4.Polynomial.hessian_apply, hG0trans i]

    have hG00j : HC4.Polynomial.hessian G0 0 j.succ = 0 := by
      rw [HC4.Polynomial.hessian_apply,
        pderiv_comm_commRing]
      simp [hG0trans j]

    have hG0i0 : HC4.Polynomial.hessian G0 i.succ 0 = 0 := by
      simp [HC4.Polynomial.hessian_apply, hG0trans i]

    have hHijEq :
        HC4.Polynomial.hessian G i.succ j.succ =
          HC4.Polynomial.hessian R i.succ j.succ := by
      rw [hGdecomp]
      simp [HC4.Polynomial.hessian_apply, hG0trans i]

    have hH0jEq :
        HC4.Polynomial.hessian G 0 j.succ =
          HC4.Polynomial.hessian R 0 j.succ := by
      have hz :
          MvPolynomial.pderiv j.succ (MvPolynomial.pderiv (0 : Fin 4) G0) = 0 := by
        rw [← pderiv_comm_commRing (0 : Fin 4) j.succ G0, hG0trans j]
        simp
      rw [hGdecomp]
      simp [HC4.Polynomial.hessian_apply, hz]

    have hHi0Eq :
        HC4.Polynomial.hessian G i.succ 0 =
          HC4.Polynomial.hessian R i.succ 0 := by
      rw [hGdecomp]
      simp [HC4.Polynomial.hessian_apply, hG0trans i]

    have hH00LE :
        IsWeightLE pureLongitudinalTransverseWeight 0
          (HC4.Polynomial.hessian G 0 0) := by
      simpa using hGLE.hessian_entry (0 : Fin 4) (0 : Fin 4)

    have hHijLE :
        IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
          (HC4.Polynomial.hessian G i.succ j.succ) := by
      rw [hHijEq]
      have hh := hRLE.hessian_entry i.succ j.succ
      simp only [pureLongitudinalTransverseWeight_succ, sub_neg_eq_add] at hh
      convert hh using 1 <;> ring

    have hH0jLE :
        IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ) + 1)
          (HC4.Polynomial.hessian G 0 j.succ) := by
      rw [hH0jEq]
      simpa using hRLE.hessian_entry (0 : Fin 4) j.succ

    have hHi0LE :
        IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ) + 1)
          (HC4.Polynomial.hessian G i.succ 0) := by
      rw [hHi0Eq]
      simpa using hRLE.hessian_entry i.succ (0 : Fin 4)

    have htop00 :
        initialForm pureLongitudinalTransverseWeight 0
            (HC4.Polynomial.hessian G 0 0) =
          HC4.Polynomial.hessian G0 0 0 := by
      have hh := hessian_initialForm_entry
        pureLongitudinalTransverseWeight 0 G (0 : Fin 4) (0 : Fin 4)
      simpa [G0] using hh.symm

    have htopij :
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
            (HC4.Polynomial.hessian G i.succ j.succ) =
          HC4.Polynomial.hessian Q i.succ j.succ := by
      have hh := hessian_initialForm_entry
        pureLongitudinalTransverseWeight (-(m : ℤ)) G i.succ j.succ
      simp only [pureLongitudinalTransverseWeight_succ, sub_neg_eq_add] at hh
      have hshift : (-(m : ℤ) + 1 + 1) = -(m : ℤ) + 2 := by ring
      rw [hshift] at hh
      simpa [Q] using hh.symm

    have hleftTop :
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
          (HC4.Polynomial.hessian G 0 0 *
            HC4.Polynomial.hessian G i.succ j.succ) =
          HC4.Polynomial.hessian G0 0 0 *
            HC4.Polynomial.hessian Q i.succ j.succ := by
      have hmul := initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hH00LE hHijLE
      rw [show (0 : ℤ) + (-(m : ℤ) + 2) = -(m : ℤ) + 2 by ring] at hmul
      rw [htop00, htopij] at hmul
      exact hmul

    have hrightLE :
        IsWeightLE pureLongitudinalTransverseWeight
          ((-(m : ℤ) + 1) + (-(m : ℤ) + 1))
          (HC4.Polynomial.hessian G 0 j.succ *
            HC4.Polynomial.hessian G i.succ 0) :=
      hH0jLE.mul hHi0LE

    have hrightTop :
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
          (HC4.Polynomial.hessian G 0 j.succ *
            HC4.Polynomial.hessian G i.succ 0) = 0 := by
      apply initialForm_eq_zero_of_isWeightLE hrightLE
      have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.succ_le_iff.mpr hmpos
      omega

    have hminor := hall (0 : Fin 4) (0 : Fin 4) i.succ j.succ
    have heq :
        HC4.Polynomial.hessian G 0 0 *
            HC4.Polynomial.hessian G i.succ j.succ =
          HC4.Polynomial.hessian G 0 j.succ *
            HC4.Polynomial.hessian G i.succ 0 :=
      sub_eq_zero.mp hminor
    have htopEq := congrArg
      (fun P : MvPolynomial (Fin 4) K =>
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2) P)
      heq
    change
      initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
          (HC4.Polynomial.hessian G 0 0 *
            HC4.Polynomial.hessian G i.succ j.succ) =
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ) + 2)
          (HC4.Polynomial.hessian G 0 j.succ *
            HC4.Polynomial.hessian G i.succ 0) at htopEq
    rw [hleftTop, hrightTop] at htopEq
    have hprod :
        HC4.Polynomial.hessian G0 0 0 *
          HC4.Polynomial.hessian Q i.succ j.succ = 0 := by
      simpa using htopEq
    exact (mul_eq_zero.mp hprod).resolve_left hT00ne

  have hQzero :=
    eq_zero_of_transverseSecondDerivatives_zero_of_exactNegativeWeight
      Q m hm2 hQhom hsecond
  exact hQne hQzero

/-! ## Blocker-facing closure of the final pure branch -/

/-- Convert the all-minors certificate in the identity chart into the raw
Hessian-minor identity used by the filtration argument. -/
theorem rightRecentered_hessian_allMinors_raw
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    let G := longitudinalRightRecenterHom
      (K := K) B.aligned.endpoint.rawSpecialFiber
    ∀ i j k l : Fin 4,
      HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l -
        HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j = 0 := by
  dsimp only
  let H := adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
    (Equiv.refl (Fin 4)) B.aligned.endpoint
  have hH := hall (Equiv.refl (Fin 4))
  have hsymm :
      ∀ i j : Fin 4,
        HC4.Polynomial.hessian
            (longitudinalRightRecenterHom
              (K := K) B.aligned.endpoint.rawSpecialFiber) i j =
          HC4.Polynomial.hessian
            (longitudinalRightRecenterHom
              (K := K) B.aligned.endpoint.rawSpecialFiber) j i := by
    intro i j
    simp only [HC4.Polynomial.hessian_apply]
    exact pderiv_comm_commRing _ _ _
  have hmatrix :
      H.matrix = HC4.Polynomial.hessian
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber) := by
    simpa [H, adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock]
      using GeneralFourBlock.matrix_ofSymmetricMatrix
        (HC4.Polynomial.hessian
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)) hsymm
  intro i j k l
  have h := hH i j k l
  rw [hmatrix] at h
  exact h

/-- **Final elimination of the higher-support pure blocker.** -/
theorem AdaptiveAlignedSmithBlockerEndpoint.no_higherTransverseSupport_of_pureLongitudinal_allMinors
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hpure : IsPureLongitudinalSmithPattern B.exponent)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    ¬ HasRightRecenteredHigherTransverseSupport B := by
  intro hhigher
  rcases B.pureLongitudinalResidual_of_pattern hpure with ⟨P⟩
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber

  have hpivot :
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian G (0 : Fin 4) (0 : Fin 4)) ≠ 0 := by
    simpa [G] using P.rightRecentered_hessian_zero_zero_axis_ne_zero

  have hraw := rightRecentered_hessian_allMinors_raw B hall
  dsimp only at hraw

  have hposSource : (positiveTransverseSourceSupport G).Nonempty := by
    rcases hhigher.2 with ⟨e, he, hpositive⟩
    unfold smithProjectedSupport at he
    rcases Finset.mem_image.mp he with ⟨d, hd, hed⟩
    refine ⟨d, Finset.mem_filter.mpr ⟨hd, ?_⟩⟩
    subst e
    unfold HasPositiveTotalTransverseDegree at hpositive
    simpa [pureLongitudinalTransverseDegree, smithSupportExponentOf] using hpositive

  have hlinearFree :
      ¬ (({ b := 1, c := 0, d := 0 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G ∨
          ({ b := 0, c := 1, d := 0 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G ∨
          ({ b := 0, c := 0, d := 1 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3 G) := by
    have hfree := hhigher.1
    unfold IsRightRecenteredTransverseLinearFree at hfree
    unfold HasRightRecenteredTransverseLinearCompetitor at hfree
    dsimp only at hfree
    simpa [G] using hfree

  exact higherTransverseSupport_impossible_of_axisPivot_of_allMinors
    G hpivot hraw hposSource hlinearFree

/-- The pure-longitudinal all-minors branch is now exhausted by either
complete transverse freeness or one of the already-green quadratic packet
endpoints. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_transverseFree_or_quadraticPacket
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hpure : IsPureLongitudinalSmithPattern B.exponent)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    (∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
        d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
      Nonempty
        (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
          (K := K) B) ∨
      Nonempty
        (AdaptiveAlignedSmithWSquarePacketEndpoint
          (K := K) B) := by
  rcases B.pureLongitudinal_transverseFree_or_quadraticPacket_or_higherSupport
      hpure hall with hfree | hplanar | hw | hhigher
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hplanar)
  · exact Or.inr (Or.inr hw)
  · exact False.elim
      (B.no_higherTransverseSupport_of_pureLongitudinal_allMinors
        hpure hall hhigher)

end

end HC4.Valuation
