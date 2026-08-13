import HC4.Valuation.AdaptiveAlignedSmithFirstContactMarkedSupport
import HC4.Valuation.AdaptiveAlignedSmithPlanarTerminalFrontier
import HC4.Newton.TerminalWeightPermutation
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# Unique-zero terminal elimination for the adaptive first-contact branch

The honest first-contact terminal cocharacter is nonnegative, non-scalar,
and already has the distinguished longitudinal zero weight `lambda 0 = 0`.

This file closes the case in which that is the *only* zero weight.

The nondegenerate terminal Hessian supplies a complement-matching
permutation

    lambda (pi i) + lambda i = d.

At `i = 0` this produces a degree-`d` coordinate.  Summing the matching
relations over all four coordinates gives

    lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 d.

Hence, after merely swapping the degree-`d` coordinate into position `1`
while fixing coordinate `0`, the weights have the standard one-zero form

    (0, d, a, d-a),    0 < a < d.

Weighted homogeneity and the Monge--Ampere equation are invariant under this
coordinate permutation, and the marked collision `0 ~ -e0` is fixed because
the permutation fixes coordinate `0`.  The already-green one-zero affine
recovery theorem then gives an immediate contradiction.

Therefore every surviving honest first-contact terminal collision has a
*second* zero-weight coordinate.  No JC2 input occurs here.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Integral weighted degree is covariant under a permutation of variables. -/
theorem integralWeightedDegree_mapDomain_perm
    (lambda : Fin 4 → ℤ)
    (rho : Equiv.Perm (Fin 4))
    (m : Fin 4 →₀ ℕ) :
    integralWeightedDegree
        (fun j => lambda (rho.symm j))
        (Finsupp.mapDomain rho m) =
      integralWeightedDegree lambda m := by
  rw [integralWeightedDegree_eq_finsuppWeight,
    integralWeightedDegree_eq_finsuppWeight]
  change
    (Finsupp.linearCombination ℕ
        (fun j => lambda (rho.symm j)))
        (Finsupp.mapDomain rho m) =
      (Finsupp.linearCombination ℕ lambda) m
  rw [Finsupp.linearCombination_mapDomain]
  simp [Function.comp_def]

/-- Weighted homogeneity transports through a coordinate permutation, with
the weight relabelled by the inverse permutation. -/
theorem integralWeightedHomogeneous_rename_perm
    {lambda : Fin 4 → ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hhom : IsIntegralWeightedHomogeneous lambda d F)
    (rho : Equiv.Perm (Fin 4)) :
    IsIntegralWeightedHomogeneous
      (fun j => lambda (rho.symm j))
      d
      (MvPolynomial.rename rho F) := by
  intro m hm
  rcases
      MvPolynomial.coeff_rename_ne_zero rho F m hm with
    ⟨u, huMap, hu⟩
  have hdeg := hhom u hu
  rw [← huMap]
  calc
    integralWeightedDegree
        (fun j => lambda (rho.symm j))
        (Finsupp.mapDomain rho u) =
      integralWeightedDegree lambda u :=
        integralWeightedDegree_mapDomain_perm lambda rho u
    _ = d := hdeg

/-- A nonnegative terminal conformal weight whose only zero is coordinate
`0` is, after a coordinate permutation fixing `0`, exactly the standard
one-zero pattern `(0,d,a,d-a)`. -/
theorem uniqueZeroTerminalWeight_standardizes
    {lambda : Fin 4 → ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg : IsNonnegativeIntegralWeight lambda)
    (hzero : lambda (0 : Fin 4) = 0)
    (hunique :
      ∀ i : Fin 4, lambda i = 0 → i = 0) :
    ∃ (rho : Equiv.Perm (Fin 4)) (a : ℤ),
      rho (0 : Fin 4) = 0 ∧
      0 < a ∧
      a < d ∧
      (∀ i : Fin 4,
        lambda (rho.symm i) =
          standardOneZeroTerminalWeight d a i) := by
  have hd : 0 < d :=
    nonnegative_nonScalar_terminal_degree_pos hface hnonneg
  rcases
      nonScalarTerminalConformalFace_has_complementWeightPermutation
        hface with
    ⟨pi, hpi⟩

  have hjd : lambda (pi 0) = d := by
    have h := hpi 0
    linarith
  have hjne : pi 0 ≠ 0 := by
    intro hj
    rw [hj, hzero] at hjd
    linarith

  have hsum :
      (∑ i : Fin 4, (lambda (pi i) + lambda i)) =
        ∑ _i : Fin 4, d := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpi i
  have hperm :
      (∑ i : Fin 4, lambda (pi i)) =
        ∑ i : Fin 4, lambda i := by
    simpa using (Equiv.sum_comp pi lambda)
  rw [Finset.sum_add_distrib, hperm] at hsum
  have hbalance :
      2 * (∑ i : Fin 4, lambda i) = 4 * d := by
    simpa [two_mul, Fin.sum_univ_four] using hsum
  have htotal :
      (∑ i : Fin 4, lambda i) = 2 * d := by
    linarith
  have htotal4 :
      lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
    simpa [Fin.sum_univ_four] using htotal

  have hpos_of_ne_zero :
      ∀ i : Fin 4, i ≠ 0 → 0 < lambda i := by
    intro i hi
    have hle := hnonneg i
    have hne : lambda i ≠ 0 := by
      intro hz
      exact hi (hunique i hz)
    omega

  have hjcases :
      pi 0 = (0 : Fin 4) ∨
      pi 0 = (1 : Fin 4) ∨
      pi 0 = (2 : Fin 4) ∨
      pi 0 = (3 : Fin 4) := by
    omega
  rcases hjcases with hj0 | hj1 | hj2 | hj3
  · exact (hjne hj0).elim
  · have h1d : lambda 1 = d := by
      simpa [hj1] using hjd
    have h2pos : 0 < lambda 2 :=
      hpos_of_ne_zero 2 (by decide)
    have h3pos : 0 < lambda 3 :=
      hpos_of_ne_zero 3 (by decide)
    have h23 : lambda 2 + lambda 3 = d := by
      linarith [htotal4, hzero, h1d]
    refine
      ⟨Equiv.refl (Fin 4), lambda 2, rfl,
        h2pos, ?_, ?_⟩
    · linarith
    · intro i
      fin_cases i
      · simpa [standardOneZeroTerminalWeight] using hzero
      · simpa [standardOneZeroTerminalWeight] using h1d
      · simp [standardOneZeroTerminalWeight]
      · simp [standardOneZeroTerminalWeight]
        linarith
  · have h2d : lambda 2 = d := by
      simpa [hj2] using hjd
    have h1pos : 0 < lambda 1 :=
      hpos_of_ne_zero 1 (by decide)
    have h3pos : 0 < lambda 3 :=
      hpos_of_ne_zero 3 (by decide)
    have h13 : lambda 1 + lambda 3 = d := by
      linarith [htotal4, hzero, h2d]
    let rho : Equiv.Perm (Fin 4) :=
      Equiv.swap (1 : Fin 4) 2
    have hrho0 : rho (0 : Fin 4) = 0 := by
      decide
    have hrhoSymm0 : rho.symm (0 : Fin 4) = 0 := by
      decide
    have hrhoSymm1 : rho.symm (1 : Fin 4) = 2 := by
      decide
    have hrhoSymm2 : rho.symm (2 : Fin 4) = 1 := by
      decide
    have hrhoSymm3 : rho.symm (3 : Fin 4) = 3 := by
      decide
    refine
      ⟨rho, lambda 1, hrho0, h1pos, ?_, ?_⟩
    · linarith
    · intro i
      have hicases :
          i = (0 : Fin 4) ∨
          i = (1 : Fin 4) ∨
          i = (2 : Fin 4) ∨
          i = (3 : Fin 4) := by
        omega
      rcases hicases with hi0 | hi1 | hi2 | hi3
      · subst i
        rw [hrhoSymm0]
        simpa [standardOneZeroTerminalWeight] using hzero
      · subst i
        rw [hrhoSymm1]
        simpa [standardOneZeroTerminalWeight] using h2d
      · subst i
        rw [hrhoSymm2]
        simp [standardOneZeroTerminalWeight]
      · subst i
        rw [hrhoSymm3]
        simp only [standardOneZeroTerminalWeight_three]
        linarith
  · have h3d : lambda 3 = d := by
      simpa [hj3] using hjd
    have h1pos : 0 < lambda 1 :=
      hpos_of_ne_zero 1 (by decide)
    have h2pos : 0 < lambda 2 :=
      hpos_of_ne_zero 2 (by decide)
    have h12 : lambda 1 + lambda 2 = d := by
      linarith [htotal4, hzero, h3d]
    let rho : Equiv.Perm (Fin 4) :=
      Equiv.swap (1 : Fin 4) 3
    have hrho0 : rho (0 : Fin 4) = 0 := by
      decide
    have hrhoSymm0 : rho.symm (0 : Fin 4) = 0 := by
      decide
    have hrhoSymm1 : rho.symm (1 : Fin 4) = 3 := by
      decide
    have hrhoSymm2 : rho.symm (2 : Fin 4) = 2 := by
      decide
    have hrhoSymm3 : rho.symm (3 : Fin 4) = 1 := by
      decide
    refine
      ⟨rho, lambda 2, hrho0, h2pos, ?_, ?_⟩
    · linarith
    · intro i
      have hicases :
          i = (0 : Fin 4) ∨
          i = (1 : Fin 4) ∨
          i = (2 : Fin 4) ∨
          i = (3 : Fin 4) := by
        omega
      rcases hicases with hi0 | hi1 | hi2 | hi3
      · subst i
        rw [hrhoSymm0]
        simpa [standardOneZeroTerminalWeight] using hzero
      · subst i
        rw [hrhoSymm1]
        simpa [standardOneZeroTerminalWeight] using h3d
      · subst i
        rw [hrhoSymm2]
        simp [standardOneZeroTerminalWeight]
      · subst i
        rw [hrhoSymm3]
        simp only [standardOneZeroTerminalWeight_three]
        linarith

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- **Unique-zero terminal elimination, without JC2.**

If coordinate `0` were the only zero terminal weight, the terminal weight
could be standardised by a permutation fixing `0`.  The marked collision is
therefore still literally `0 ~ -e0` after renaming, and the green standard
one-zero affine-recovery theorem gives a contradiction. -/
theorem impossible_of_noSecondMarkedZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (hno : ¬ C.HasSecondMarkedTerminalZero) :
    False := by
  let lambda : Fin 4 → ℤ :=
    fun i => (C.weight i : ℤ)
  let d : ℤ := (C.degree : ℤ)

  have hunique :
      ∀ i : Fin 4, lambda i = 0 → i = 0 := by
    intro i hi
    by_contra hine
    apply hno
    refine ⟨i, hine, ?_⟩
    dsimp [lambda] at hi
    exact_mod_cast hi

  rcases
      uniqueZeroTerminalWeight_standardizes
        C.residualNonScalarJump.1
        C.nonnegative
        C.integralWeight_zero
        hunique with
    ⟨rho, a, hfix, ha, had, hweight⟩

  have hweightFun :
      (fun i : Fin 4 => lambda (rho.symm i)) =
        standardOneZeroTerminalWeight d a := by
    funext i
    exact hweight i

  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a)
        d
        (MvPolynomial.rename rho T.fibre) := by
    have h :=
      integralWeightedHomogeneous_rename_perm
        C.homogeneous rho
    dsimp [lambda, d] at hweightFun ⊢
    rw [hweightFun] at h
    exact h

  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho T.fibre) :=
    isPolynomialMongeAmpere_rename_perm rho T.mongeAmpere

  have hcoll :=
    (C.exactMarkedAxisCollision_of_noSecondZero hno).rename_perm rho
  have hcollMarked :
      HasExactGradientCollision
        (MvPolynomial.rename rho T.fibre)
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K)) := by
    rw [terminalPermutePoint_zeroPoint] at hcoll
    rw [terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero
      rho hfix] at hcoll
    exact hcoll

  exact
    standardOneZero_negativeLongitudinalAxis_collision_impossible
      ha had hhomRenamed hMARenamed hcollMarked

/-- **Second-zero forcing theorem.**
Every honest surviving first-contact terminal collision has a second
zero-weight coordinate.  Thus the unique-zero boundary has been completely
eliminated without JC2. -/
theorem hasSecondMarkedTerminalZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    C.HasSecondMarkedTerminalZero := by
  by_contra hno
  exact C.impossible_of_noSecondMarkedZero hno

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
