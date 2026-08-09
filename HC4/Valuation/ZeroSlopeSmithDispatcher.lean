import HC4.Valuation.BinarySmithOrderExtraction
import Mathlib.Tactic

/-!
# Zero-slope Smith dispatcher from the genuine polynomial family

Phases 93.62--93.64 close the two Smith branches separately:

* symmetric-minimal special fibre -> canonical local Smith repair/rigid packet;
* non-minimal special fibre -> denominator-cleared strict Smith restart.

This file removes the remaining artificial inputs between a genuine
polynomial Rees family and those two branches.

For a family

    P : K[tau][x0,x1,x2,x3]

with moving sections `a,b`, assume their reductions are the canonical
pointed pair

    a(0) = 0,
    b(0) = e_0.

Then:

1. exact family-gradient collision descends automatically to the exact
   special-fibre collision `0 ~ e_0`;
2. the three transverse coordinates of both moving sections have zero
   constant coefficient and hence are divisible by `tau`;
3. therefore the non-minimal branch has exactly the section-divisibility
   hypotheses required by the green Phase 93.63 theorem;
4. the minimal branch needs only homogeneity, degree at least two, and
   nonempty projected support in order to invoke Phase 93.62.

The final theorem is an honest one-step zero-slope dispatcher.

Important scale boundary:
the strict branch is the denominator-cleared step

    10*Delta -> 10*Delta - 4.

This file deliberately does not claim that repeatedly re-ramifying by ten
is a global well-founded process.  The global assembly must either choose a
single common ramification before iteration or return to a pole-depth
minimal representative.  Keeping that boundary explicit prevents the
one-step Smith theorem from being misused as a completed global proof.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Canonical Fin-4 chart facts -/

/-- The standard four coordinates exhaust `Fin 4`. -/
theorem finFour_standard_isFourCoordinateChart :
    IsFourCoordinateChart
      (0 : Fin 4) 1 2 3 := by
  intro i
  fin_cases i <;> simp

theorem finFour_zero_ne_one :
    (0 : Fin 4) ≠ 1 := by decide

theorem finFour_zero_ne_two :
    (0 : Fin 4) ≠ 2 := by decide

theorem finFour_zero_ne_three :
    (0 : Fin 4) ≠ 3 := by decide

theorem finFour_one_ne_two :
    (1 : Fin 4) ≠ 2 := by decide

theorem finFour_one_ne_three :
    (1 : Fin 4) ≠ 3 := by decide

theorem finFour_two_ne_three :
    (2 : Fin 4) ≠ 3 := by decide

/-! ## Canonical special-fibre Smith objects -/

/-- The balanced subface used by the symmetric-minimal special-fibre
branch, with old minimum and base both zero. -/
noncomputable def canonicalSpecialFiberSmithSubface
    (F : MvPolynomial (Fin 4) K) :
    Finset SmithSupportExponent :=
  smithSymmetricBalancedSubface
    (smithProjectedSupport
      (1 : Fin 4) 2 3 F)
    0
    (fun _ => (0 : ℤ))

/-- The canonical Smith packet polynomial extracted from that subface. -/
noncomputable def canonicalSpecialFiberSmithPolynomial
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  smithSubfacePolynomial
    (1 : Fin 4) 2 3
    (canonicalSpecialFiberSmithSubface F)
    F

/-! ## Special-point normalisation implies section divisibility -/

/-- If a moving section reduces to the origin, every transverse coordinate
is divisible by the parameter. -/
theorem smithTransverseParameterFactor_of_specialPoint_zero
    (a : Fin 4 → Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K))) :
    HasSmithTransverseParameterFactor a := by
  constructor
  · rw [Polynomial.X_dvd_iff]
    have h := congrFun ha (1 : Fin 4)
    simpa [polynomialSectionSpecialPoint] using h
  · constructor
    · rw [Polynomial.X_dvd_iff]
      have h := congrFun ha (2 : Fin 4)
      simpa [polynomialSectionSpecialPoint] using h
    · rw [Polynomial.X_dvd_iff]
      have h := congrFun ha (3 : Fin 4)
      simpa [polynomialSectionSpecialPoint] using h

/-- If a moving section reduces to the canonical `x0`-axis point, its three
transverse coordinates are likewise divisible by the parameter. -/
theorem smithTransverseParameterFactor_of_specialPoint_axisZero
    (b : Fin 4 → Polynomial K)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasSmithTransverseParameterFactor b := by
  constructor
  · rw [Polynomial.X_dvd_iff]
    have h := congrFun hb (1 : Fin 4)
    simpa [polynomialSectionSpecialPoint,
      coordinateAxisPoint] using h
  · constructor
    · rw [Polynomial.X_dvd_iff]
      have h := congrFun hb (2 : Fin 4)
      simpa [polynomialSectionSpecialPoint,
        coordinateAxisPoint] using h
    · rw [Polynomial.X_dvd_iff]
      have h := congrFun hb (3 : Fin 4)
      simpa [polynomialSectionSpecialPoint,
        coordinateAxisPoint] using h

/-! ## Family collision -> canonical special-fibre collision -/

/-- Exact family collision at sections reducing to `0` and `e0` gives
exactly the collision consumed by the canonical Smith first-wall theorem. -/
theorem polynomialFamilyCollision_specialFiber_zero_axisZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber P)
      (fun _ => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have hs :=
    polynomialFamilyExactGradientCollision_specialFiber
      P a b hcoll
  simpa [ha, hb] using hs

/-! ## Symmetric-minimal local branch -/

/-- With old minimum/base equal to zero, the minimum inequality is
automatic. -/
theorem canonicalSpecialFiberSmith_minimum
    (F : MvPolynomial (Fin 4) K) :
    ∀ e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 F,
      (0 : ℤ) ≤ (fun _ => (0 : ℤ)) e := by
  intro e he
  simp

/-- Nonempty projected support gives attainment of the zero minimum. -/
theorem canonicalSpecialFiberSmith_attainment
    (F : MvPolynomial (Fin 4) K)
    (hne :
      (smithProjectedSupport
        (1 : Fin 4) 2 3 F).Nonempty) :
    ∃ e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 F,
      (fun _ => (0 : ℤ)) e = 0 := by
  rcases hne with ⟨e, he⟩
  exact ⟨e, he, rfl⟩

/-- **The symmetric-minimal special fibre enters the existing local Smith
classifier with no additional valuation data.** -/
theorem symmetricMinimalSpecialFiber_hasRepairOrTerminal
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D : ℕ}
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hprojected :
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P)).Nonempty)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    (complexity : ℕ) :
    HasRepairOrTerminal
      (HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D
        (canonicalSpecialFiberSmithPolynomial
          (polynomialFamilySpecialFiber P)))
      (rankOneRepairState complexity) := by
  have hspecial :=
    polynomialFamilyCollision_specialFiber_zero_axisZero
      P a b hcoll ha hb
  have hmin :=
    canonicalSpecialFiberSmith_minimum
      (polynomialFamilySpecialFiber P)
  have hattain :=
    canonicalSpecialFiberSmith_attainment
      (polynomialFamilySpecialFiber P)
      hprojected
  have hout :=
    smithFirstWall_hasRepairOrTerminal_symmetricMinimal
      (K := K)
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      hhom hD hspecial
      0
      (fun _ => (0 : ℤ))
      hminimal
      hmin
      hattain
      complexity
  simpa [canonicalSpecialFiberSmithSubface,
    canonicalSpecialFiberSmithPolynomial] using hout

/-! ## One-step strict Smith restart package -/

/-- The numerical part of the denominator-cleared strict Smith branch. -/
def HasFixedTenSmithDefectRestart
    (Delta : ℕ)
    (s : GlobalRestartState) : Prop :=
  ∃ t : GlobalRestartState,
    t.defect = 10 * Delta - 4 ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t

/-- A non-minimal special fibre supplies the fixed-ten numerical restart.
The required transverse section divisibility is derived automatically from
the canonical special points. -/
theorem nonminimalSpecialFiber_hasFixedTenSmithDefectRestart
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hnotMinimal :
      ¬ IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    (s : GlobalRestartState)
    (hs : s.defect = 10 * Delta)
    (newRepair : RepairState) :
    HasFixedTenSmithDefectRestart Delta s := by
  have haaxis :=
    smithTransverseParameterFactor_of_specialPoint_zero
      a ha
  have hbaxis :=
    smithTransverseParameterFactor_of_specialPoint_axisZero
      b hb
  let t : GlobalRestartState :=
    { defect := 10 * Delta - 4
      repair := newRepair }
  have hout :=
    specialFiber_notSymmetricMinimal_exactCollision_and_strictRestart
      (K := K)
      (s := s)
      P hnotMinimal hdef
      a b haaxis hbaxis hcoll
      hs newRepair
  refine ⟨t, rfl, ?_, ?_⟩
  · simpa [t] using hout.2.1
  · simpa [t] using hout.2.2

/-! ## Complete one-step zero-slope Smith dispatcher -/

/-- The actual one-step alternatives supplied by the zero-slope Smith
analysis.

The left branch is the denominator-cleared strict defect restart.
The right branch is the already-green local Smith terminal/repair outcome.
-/
def HasZeroSlopeSmithOneStepOutcome
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (D Delta complexity : ℕ)
    (s : GlobalRestartState) : Prop :=
  HasFixedTenSmithDefectRestart Delta s ∨
    HasRepairOrTerminal
      (HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D
        (canonicalSpecialFiberSmithPolynomial
          (polynomialFamilySpecialFiber P)))
      (rankOneRepairState complexity)

/-- **Zero-slope Smith dispatcher from a genuine Rees family.**

No pole-minimality hypothesis, coefficient-order function, or section
divisibility package is assumed.

The actual special fibre is split by the finite symmetric Smith dichotomy:

* minimal -> canonical local repair/rigid packet;
* non-minimal -> fixed-denominator strict defect restart.
-/
theorem zeroSlopeSmith_oneStepDispatcher
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D Delta : ℕ}
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hprojected :
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P)).Nonempty)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (s : GlobalRestartState)
    (hs : s.defect = 10 * Delta)
    (complexity : ℕ)
    (newRepair : RepairState) :
    HasZeroSlopeSmithOneStepOutcome
      P D Delta complexity s := by
  by_cases hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ))
  · right
    exact
      symmetricMinimalSpecialFiber_hasRepairOrTerminal
        P a b hhom hD hprojected
        hcoll ha hb hminimal complexity
  · left
    exact
      nonminimalSpecialFiber_hasFixedTenSmithDefectRestart
        P a b hdef hcoll ha hb
        hminimal s hs newRepair

end

end HC4.Valuation
