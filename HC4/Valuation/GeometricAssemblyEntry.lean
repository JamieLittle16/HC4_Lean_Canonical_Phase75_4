import HC4.Valuation.CoupledSmithWallClosure
import HC4.Valuation.IntegralKernelSlopeExtraction
import Mathlib.Tactic

/-!
# Geometric entry for the final JC2 => HC4 assembly

The numerical global restart state from Phase 93.48 records only

    (determinant defect, local repair state).

That is sufficient for the abstract well-founded argument, but not for
iterating the actual valuation geometry: a genuine restart must also carry

* the polynomial family;
* the moving marked section;
* ordinary homogeneity;
* the exact Hessian defect identity;
* the exact family-gradient collision; and
* the canonical pointed special-fibre normalisation.

This file adds precisely that geometric layer.

There are two main results.

## Positive kernel slope

For the actual global pointed normalisation the first section is identically
zero and the second reduces to `e0`.

If the blown-up kernel coordinate is transverse (`kernel != 0`), then a
positive integral kernel blow-up preserves that canonical special pair
exactly.  Since the blow-up introduces no new source monomials, ordinary
homogeneity is preserved as well.

Thus the complete positive maximal-slope branch is now genuinely re-entrant
at the level of the geometric datum, not merely at the numerical defect
level.

## Zero-slope Smith branch

The global exact-collision normalisation has first section identically zero.
Consequently it has no section walls at all.  Specialising the closed
Phase-93.71 Smith dispatcher to this case leaves only

* the canonical local repair/terminal branch; or
* a separated wall of the *right* marked section.

No left-section branch survives.

Moreover the aligned arithmetic is quantised more strongly than the
Phase-93.70 `X`-factor statement:

* every separated right section wall gives a common parameter factor
  `X^10`;
* if the wall coordinate is `y` or `z`, the common factor improves to
  `X^20`.

Hence the physical Hessian defect after the first extraction is exactly

    20*Delta - 40 = 20*(Delta - 2)

in every separated right-section case, and

    20*Delta - 80 = 20*(Delta - 4)

for a `y/z` wall.

This exposes the genuine remaining orchestration issue cleanly:
the marked right special point has moved off `e0`, so the extracted family
cannot yet be fed back into the canonical Smith dispatcher without a
pointed chart-continuation theorem.

No numerical restart is silently re-ramified here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Canonical global pointed datum -/

/-- The identically-zero first moving section used by the global
exact-collision normalisation. -/
def zeroPolynomialSection :
    Fin 4 → Polynomial K :=
  fun _ => 0

@[simp] theorem zeroPolynomialSection_apply
    (i : Fin 4) :
    zeroPolynomialSection (K := K) i = 0 := rfl

/-- The zero section reduces to the zero point. -/
@[simp] theorem polynomialSectionSpecialPoint_zeroPolynomialSection :
    polynomialSectionSpecialPoint
      (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) := by
  funext i
  simp [zeroPolynomialSection,
    polynomialSectionSpecialPoint]

/-- Geometric restart state for the canonical pointed family.

Unlike `GlobalRestartState`, this structure carries the actual family and
marked section required by the next valuation step. -/
structure CanonicalGeometricRestartState
    (D : ℕ) where
  defect : ℕ
  repair : RepairState
  family : MvPolynomial (Fin 4) (Polynomial K)
  movingSection : Fin 4 → Polynomial K
  homogeneous :
    family.IsHomogeneous D
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) family defect
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family
      (zeroPolynomialSection (K := K))
      movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Forget the geometry and recover the Phase-93.48 numerical state. -/
def CanonicalGeometricRestartState.toGlobal
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D) :
    GlobalRestartState :=
  { defect := s.defect
    repair := s.repair }

@[simp] theorem CanonicalGeometricRestartState.toGlobal_defect
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D) :
    s.toGlobal.defect = s.defect := rfl

@[simp] theorem CanonicalGeometricRestartState.toGlobal_repair
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D) :
    s.toGlobal.repair = s.repair := rfl

/-! ## Positive kernel blow-up preserves the geometric datum -/

/-- An integral kernel blow-up introduces no new source monomials and
therefore preserves ordinary source homogeneity. -/
theorem integralKernelBlowupFamily_isHomogeneous
    {D slope : ℕ}
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    (integralKernelBlowupFamily
      kernel slope P hdiv).IsHomogeneous D := by
  intro d hdQ
  have hdQsupport :
      d ∈
        (integralKernelBlowupFamily
          kernel slope P hdiv).support :=
    MvPolynomial.mem_support_iff.mpr hdQ
  have hdPsupport :
      d ∈ P.support :=
    support_integralKernelBlowupFamily_subset
      kernel slope P hdiv hdQsupport
  exact hP (MvPolynomial.mem_support_iff.mp hdPsupport)

/-- Blowing up the identically-zero section leaves it identically zero. -/
theorem kernelBlowupSection_zeroPolynomialSection
    (kernel : Fin 4)
    (slope : ℕ) :
    kernelBlowupSection
        kernel slope
        (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  simp [kernelBlowupSection,
    zeroPolynomialSection]

/-- A positive blow-up in a transverse coordinate preserves the canonical
right special point `e0`. -/
theorem polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (hkernel : kernel ≠ (0 : Fin 4))
    (b : Fin 4 → Polynomial K)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope b) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  by_cases hi : i = kernel
  · subst i
    rw [
      polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hslope b]
    simp [coordinateAxisPoint, hkernel]
  · rw [
      polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel slope b hi]
    have hbi := congrFun hb i
    exact hbi

/-- The canonical axis point is nonzero. -/
theorem coordinateAxisPoint_zero_ne_zeroPoint :
    coordinateAxisPoint (K := K) (0 : Fin 4) ≠
      (fun _ => (0 : K)) := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simp [coordinateAxisPoint] at h0

/-- Hence the canonical zero/e0 special pair remains distinct after every
positive transverse kernel blow-up. -/
theorem canonicalSpecialPointsDistinct_after_positive_transverseKernelBlowup
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (hkernel : kernel ≠ (0 : Fin 4))
    (b : Fin 4 → Polynomial K)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection
          kernel slope
          (zeroPolynomialSection (K := K))) ≠
      polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope b) := by
  rw [
    kernelBlowupSection_zeroPolynomialSection,
    polynomialSectionSpecialPoint_zeroPolynomialSection,
    polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
      kernel hslope hkernel b hb]
  intro h
  exact
    coordinateAxisPoint_zero_ne_zeroPoint
      (K := K) h.symm

/-- **Geometric positive maximal-slope restart.**

The positive branch now returns a complete canonical geometric successor,
not merely a numerical defect inequality. -/
theorem canonicalGeometricRestart_positiveMaximalKernelSlope
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel s.family)
    (hslope :
      0 <
        maximalIntegralKernelSlope
          kernel s.family hactive)
    (newRepair : RepairState) :
    let q :=
      maximalIntegralKernelSlope
        kernel s.family hactive
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      t.defect = s.defect - 2 * q ∧
      t.family =
        integralKernelBlowupFamily
          kernel q s.family
          (maximalIntegralKernelSlope_divisibility
            kernel s.family hactive) ∧
      t.movingSection =
        kernelBlowupSection kernel q s.movingSection ∧
      GlobalRestartProgress s.toGlobal t.toGlobal := by
  dsimp
  let q :=
    maximalIntegralKernelSlope
      kernel s.family hactive
  let hdiv :=
    maximalIntegralKernelSlope_divisibility
      kernel s.family hactive
  let P' :=
    integralKernelBlowupFamily
      kernel q s.family hdiv
  let b' :=
    kernelBlowupSection kernel q s.movingSection
  have hdef' :
      HasPolynomialFamilyHessianDefect
        (K := K) P'
        (s.defect - 2 * q) := by
    dsimp [P', q, hdiv]
    exact
      integralKernelBlowup_hasHessianDefect_sub
        kernel q s.defect s.family hdiv
        s.hessianDefect
  have hhom' :
      P'.IsHomogeneous D := by
    dsimp [P', q, hdiv]
    exact
      integralKernelBlowupFamily_isHomogeneous
        kernel s.family s.homogeneous hdiv
  have hcollRaw :
      HasPolynomialFamilyExactGradientCollision
        P'
        (kernelBlowupSection
          kernel q
          (zeroPolynomialSection (K := K)))
        b' := by
    dsimp [P', b', q, hdiv]
    exact
      polynomialFamilyExactGradientCollision_integralKernelBlowup
        kernel q s.family hdiv
        (zeroPolynomialSection (K := K))
        s.movingSection
        s.exactCollision
  have hcoll' :
      HasPolynomialFamilyExactGradientCollision
        P'
        (zeroPolynomialSection (K := K))
        b' := by
    rw [kernelBlowupSection_zeroPolynomialSection] at hcollRaw
    exact hcollRaw
  have hb' :
      polynomialSectionSpecialPoint b' =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [b', q]
    exact
      polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
        kernel hslope hkernel s.movingSection
        s.sectionSpecial
  let t : CanonicalGeometricRestartState (K := K) D :=
    { defect := s.defect - 2 * q
      repair := newRepair
      family := P'
      movingSection := b'
      homogeneous := hhom'
      hessianDefect := hdef'
      exactCollision := hcoll'
      sectionSpecial := hb' }
  have hdrop :
      HasPositiveKernelDefectDrop
        q s.toGlobal t.toGlobal := by
    apply
      integralKernelBlowup_positiveKernelDefectDrop
        kernel hslope s.family hdiv
        s.hessianDefect
    · rfl
    · rfl
  refine ⟨t, rfl, rfl, rfl, ?_⟩
  exact
    globalRestartProgress_of_positiveKernelDefectDrop
      hdrop

/-! ## The identically-zero section has no Smith section walls -/

/-- There are no transverse section walls for the identically-zero moving
section. -/
theorem alignedSmithSectionWalls_zeroPolynomialSection :
    alignedSmithSectionWalls
        (zeroPolynomialSection (K := K)) =
      ∅ := by
  classical
  ext N
  simp [alignedSmithSectionWalls,
    nonzeroSmithTransverseCoordinates,
    zeroPolynomialSection]

/-- In particular no aligned step belongs to the zero section's wall set. -/
theorem not_mem_alignedSmithSectionWalls_zeroPolynomialSection
    (N : ℕ) :
    N ∉
      alignedSmithSectionWalls
        (zeroPolynomialSection (K := K)) := by
  rw [alignedSmithSectionWalls_zeroPolynomialSection]
  simp

/-! ## Zero-section Smith dispatcher retaining the geometric wall witness -/

/-- The only genuine section-wall residual in the global pointed
normalisation: the first wall belongs to the right marked section but not
to the coefficient-wall set. -/
def HasSeparatedRightSmithSectionWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) : Prop :=
  ∃ hwall : HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b,
    ¬ HasPrimitiveZeroSmithSource P ∧
    alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall ∉
      alignedSmithCoefficientWalls P ∧
    alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall ∈
      alignedSmithSectionWalls b

/-- **Geometric zero-section Smith dispatcher.**

Unlike the numerical Phase-93.71 wrapper, this theorem retains the actual
right-section wall certificate when the local branch is not yet reached.
This is the form required by a sound global assembly. -/
theorem alignedSmith_zeroSection_geometricDispatcher
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity ∨
      HasSeparatedRightSmithSectionWall P b := by
  classical
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  by_cases hprimitive :
      HasPrimitiveZeroSmithSource P
  · left
    have hhom :=
      polynomialFamilySpecialFiber_isHomogeneous
        P hP
    have hminimal :=
      primitiveZeroSmithSource_specialFiber_symmetricMinimal
        P hprimitive
    exact
      canonicalSymmetricMinimal_hasRepairOrTerminal
        P
        (zeroPolynomialSection (K := K))
        b hhom hD hcoll
        ha hb hminimal complexity
  · by_cases hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b
    · let N :=
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall
      by_cases hcoeff :
          N ∈ alignedSmithCoefficientWalls P
      · by_cases hB :
          N ∈ alignedSmithSectionWalls b
        · have hcoupled :
            HasCoupledAlignedSmithWall
              P (zeroPolynomialSection (K := K)) b := by
            refine ⟨hwall, ?_, ?_⟩
            · simpa [N] using hcoeff
            · exact Or.inr (by simpa [N] using hB)
          exact
            False.elim
              (coupledAlignedSmithWall_impossible_of_noPrimitive
                P hP
                (zeroPolynomialSection (K := K))
                b hD hcoll
                ha hb hprimitive hcoupled)
        · left
          have hnotA :
              N ∉ alignedSmithSectionWalls
                (zeroPolynomialSection (K := K)) :=
            not_mem_alignedSmithSectionWalls_zeroPolynomialSection
              (K := K) N
          exact
            pureCoefficientWall_hasRepairOrTerminal
              P hP
              (zeroPolynomialSection (K := K))
              b hwall
              (by simpa [N] using hcoeff)
              (by simpa [N] using hnotA)
              (by simpa [N] using hB)
              hD hcoll ha hb complexity
      · right
        have hcases :=
          alignedSmithGenuineFirstWall_cases
            P (zeroPolynomialSection (K := K)) b hwall
        have hB :
            N ∈ alignedSmithSectionWalls b := by
          rcases hcases with hc | hA | hB
          · exact
              False.elim
                (hcoeff (by simpa [N] using hc))
          · have hnotA :
                N ∉ alignedSmithSectionWalls
                  (zeroPolynomialSection (K := K)) :=
              not_mem_alignedSmithSectionWalls_zeroPolynomialSection
                (K := K) N
            exact
              False.elim
                (hnotA (by simpa [N] using hA))
          · simpa [N] using hB
        exact
          ⟨hwall, hprimitive,
            by simpa [N] using hcoeff,
            by simpa [N] using hB⟩
    · left
      exact
        noWallPrimitiveSmithFamily_hasRepairOrTerminal
          P hP
          (zeroPolynomialSection (K := K))
          b Delta hdef hwall
          hD hcoll ha hb complexity

/-! ## Quantisation of a separated right-section wall -/

/-- Every actual aligned section wall occurs at a multiple of five. -/
theorem five_dvd_alignedSmithSectionWallStep
    (i : Fin 4)
    (c : Polynomial K) :
    5 ∣ alignedSmithSectionWallStep i c := by
  unfold alignedSmithSectionWallStep
  by_cases hi3 : i = 3
  · rw [if_pos hi3]
    exact dvd_mul_right 5 _
  · rw [if_neg hi3]
    refine ⟨2 * sectionCoordinateParameterOrder c, ?_⟩
    ring

/-- A `y/z` aligned section wall occurs at a multiple of ten. -/
theorem ten_dvd_alignedSmithSectionWallStep_of_ne_three
    (i : Fin 4)
    (c : Polynomial K)
    (hi3 : i ≠ 3) :
    10 ∣ alignedSmithSectionWallStep i c := by
  unfold alignedSmithSectionWallStep
  rw [if_neg hi3]
  exact dvd_mul_right 10 _

/-- Positive aligned residual coefficient order at a section wall is at
least ten, because the symmetric Smith derivative is even and every section
wall step is a multiple of five. -/
theorem separatedSectionWall_coefficient_margin_ten
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    4 * N + 10 ≤
      N * smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder P d := by
  dsimp
  let N :=
    alignedSmithGenuineFirstWall
      P (zeroPolynomialSection (K := K)) b hwall
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  have hNpos :
      0 < N :=
    alignedSmithSectionWall_step_pos
      b
      (specialPoint_axis_transverse_constantCoeff
        b hb)
      hsection
  have hbase :
      4 * N + 1 ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d := by
    exact
      separatedSectionWall_coefficient_margin_one
        P
        (zeroPolynomialSection (K := K))
        b hwall hnotCoeff hnoPrimitive
        hNpos hd
  rcases
      mem_alignedSmithSectionWalls_exists_coordinate
        b hsection with
    ⟨i, hi0, hine, hstep⟩
  rcases
      five_dvd_alignedSmithSectionWallStep
        (K := K) i (b i) with
    ⟨k, hk⟩
  have hNk : N = 5 * k := by
    calc
      N = alignedSmithSectionWallStep i (b i) :=
        hstep.symm
      _ = 5 * k := hk
  rcases
      smithSeparatorDelta_one_one_even
        (smithAxisProjection d) with
    ⟨z, hz⟩
  have hrel :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  have hres :
      (N : ℤ) *
            (smithConformalRawExponent 2 2 d : ℤ) +
          (alignedSmithRamificationIndex : ℤ) *
            (smithFamilyCoefficientOrder P d : ℤ) -
          4 * (N : ℤ) =
        10 *
          (2 * (smithFamilyCoefficientOrder P d : ℤ) +
            (k : ℤ) * z) := by
    rw [hNk]
    rw [hz] at hrel
    norm_num [alignedSmithRamificationIndex]
    nlinarith
  have hbaseIntRaw :
      (4 * N + 1 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) := by
    exact_mod_cast hbase
  have hbaseInt :
      (1 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    omega
  have htenInt :
      (10 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    rw [hres] at hbaseInt ⊢
    omega
  exact_mod_cast
    (show
      (4 * N + 10 : ℕ) ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d by
      omega)

/-- Therefore every separated right-section wall carries a common factor
`X^10`, not merely `X`. -/
theorem separatedRightSectionWall_commonParameterFactor_ten
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let hwall := Classical.choose hsep
    HasCommonParameterFactor 10
      (alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall) := by
  dsimp
  let hwall := Classical.choose hsep
  have hdata := Classical.choose_spec hsep
  have hnoPrimitive := hdata.1
  have hnotCoeff := hdata.2.1
  have hsection := hdata.2.2
  let N :=
    alignedSmithGenuineFirstWall
      P (zeroPolynomialSection (K := K)) b hwall
  have hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)) := by
    intro d hd
    dsimp [N]
    exact
      alignedSmithGenuineFirstWall_coefficient_nonnegative
        P (zeroPolynomialSection (K := K)) b
        hwall hd
  have hmargin :
      ∀ d ∈ P.support,
        4 * N + 10 ≤
          N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex *
              smithFamilyCoefficientOrder P d := by
    intro d hd
    dsimp [N]
    exact
      separatedSectionWall_coefficient_margin_ten
        P b hwall hnotCoeff hnoPrimitive
        hsection hb hd
  have hout :=
    alignedSmith_commonFactor_of_margin
      (K := K)
      P N 10 hlegal hmargin
  simpa [alignedSmithGenuineFirstWallFamily, N] using hout

/-- The scale-ten extraction lowers the once-ramified physical defect from
`20*Delta` to exactly `20*(Delta-2)`. -/
theorem separatedRightSectionWall_hasHessianDefect_twenty_mul_sub_two
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let hwall := Classical.choose hsep
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let hcommon :=
      separatedRightSectionWall_commonParameterFactor_ten
        P b hsep hb
    HasPolynomialFamilyHessianDefect
      (K := K)
      (commonParameterFactorFamily 10 Q hcommon)
      (alignedSmithRamificationIndex * (Delta - 2)) := by
  dsimp
  let hwall := Classical.choose hsep
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let hcommon :=
    separatedRightSectionWall_commonParameterFactor_ten
      P b hsep hb
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWall_preservesHessianDefect
        P (zeroPolynomialSection (K := K)) b
        hwall Delta hdef
  have hbudget :
      4 * 10 ≤
        alignedSmithRamificationIndex * Delta :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) 10 Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQdef
  have hDelta : 2 ≤ Delta := by
    norm_num [alignedSmithRamificationIndex] at hbudget
    omega
  have hsub :
      alignedSmithRamificationIndex * Delta - 4 * 10 =
        alignedSmithRamificationIndex * (Delta - 2) := by
    norm_num [alignedSmithRamificationIndex]
    omega
  have hout :=
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (K := K)
      10 Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQdef
  rw [hsub] at hout
  exact hout

/-- The scale-ten extraction preserves the exact family collision. -/
theorem separatedRightSectionWall_preservesExactCollision_after_factor_ten
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let hwall := Classical.choose hsep
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let a' :=
      alignedSmithGenuineFirstWallSectionLeft
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let b' :=
      alignedSmithGenuineFirstWallSectionRight
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let hcommon :=
      separatedRightSectionWall_commonParameterFactor_ten
        P b hsep hb
    HasPolynomialFamilyExactGradientCollision
      (commonParameterFactorFamily 10 Q hcommon)
      a' b' := by
  dsimp
  let hwall := Classical.choose hsep
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let hcommon :=
    separatedRightSectionWall_commonParameterFactor_ten
      P b hsep hb
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q a' b' := by
    dsimp [Q, a', b']
    exact
      alignedSmithGenuineFirstWall_preservesExactCollision
        P (zeroPolynomialSection (K := K)) b
        hwall hcoll
  exact
    polynomialFamilyExactGradientCollision_commonParameterFactor
      10 Q hcommon a' b' hQcoll

/-- The scale-ten extraction also preserves ordinary source homogeneity. -/
theorem separatedRightSectionWall_isHomogeneous_after_factor_ten
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let hwall := Classical.choose hsep
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let hcommon :=
      separatedRightSectionWall_commonParameterFactor_ten
        P b hsep hb
    (commonParameterFactorFamily 10 Q hcommon).IsHomogeneous D := by
  dsimp
  let hwall := Classical.choose hsep
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let hcommon :=
    separatedRightSectionWall_commonParameterFactor_ten
      P b hsep hb
  have hQhom :
      Q.IsHomogeneous D := by
    dsimp [Q]
    let Pram :=
      parameterRamificationFamily
        (K := K)
        alignedSmithRamificationIndex P
    have hPram :
        Pram.IsHomogeneous D := by
      dsimp [Pram]
      exact hP.map _
    exact
      integralSmithConformalFamily_isHomogeneous
        Pram hPram
        (alignedSmithGenuineFirstWall_integralCoefficients
          P (zeroPolynomialSection (K := K)) b hwall)
  exact
    commonParameterFactorFamily_isHomogeneous
      Q hQhom hcommon

/-! ## y/z walls carry the stronger factor X^20 -/

/-- At a non-w transverse section wall the first step is a multiple of ten,
so the same parity argument upgrades residual order from ten to twenty. -/
theorem separatedYZSectionWall_coefficient_margin_twenty
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hi3 : i ≠ 3)
    (hine : b i ≠ 0)
    (hstep :
      alignedSmithSectionWallStep i (b i) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    4 * N + 20 ≤
      N * smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder P d := by
  dsimp
  let N :=
    alignedSmithGenuineFirstWall
      P (zeroPolynomialSection (K := K)) b hwall
  have hsection :
      N ∈ alignedSmithSectionWalls b := by
    dsimp [N]
    rw [← hstep]
    exact
      alignedSmithSectionWallStep_mem
        b hi0 hine
  have hNpos :
      0 < N :=
    alignedSmithSectionWall_step_pos
      b
      (specialPoint_axis_transverse_constantCoeff
        b hb)
      hsection
  have hbase :
      4 * N + 1 ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d := by
    exact
      separatedSectionWall_coefficient_margin_one
        P
        (zeroPolynomialSection (K := K))
        b hwall hnotCoeff hnoPrimitive
        hNpos hd
  rcases
      ten_dvd_alignedSmithSectionWallStep_of_ne_three
        (K := K) i (b i) hi3 with
    ⟨k, hk⟩
  have hNk : N = 10 * k := by
    calc
      N = alignedSmithSectionWallStep i (b i) :=
        hstep.symm
      _ = 10 * k := hk
  rcases
      smithSeparatorDelta_one_one_even
        (smithAxisProjection d) with
    ⟨z, hz⟩
  have hrel :=
    smithSeparatorDelta_projection_eq_raw_sub_four d
  have hres :
      (N : ℤ) *
            (smithConformalRawExponent 2 2 d : ℤ) +
          (alignedSmithRamificationIndex : ℤ) *
            (smithFamilyCoefficientOrder P d : ℤ) -
          4 * (N : ℤ) =
        20 *
          ((smithFamilyCoefficientOrder P d : ℤ) +
            (k : ℤ) * z) := by
    rw [hNk]
    rw [hz] at hrel
    norm_num [alignedSmithRamificationIndex]
    nlinarith
  have hbaseIntRaw :
      (4 * N + 1 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) := by
    exact_mod_cast hbase
  have hbaseInt :
      (1 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    omega
  have htwentyInt :
      (20 : ℤ) ≤
        (N : ℤ) *
              (smithConformalRawExponent 2 2 d : ℤ) +
            (alignedSmithRamificationIndex : ℤ) *
              (smithFamilyCoefficientOrder P d : ℤ) -
            4 * (N : ℤ) := by
    rw [hres] at hbaseInt ⊢
    omega
  exact_mod_cast
    (show
      (4 * N + 20 : ℕ) ≤
        N * smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder P d by
      omega)

/-- If the separated right wall is actually a y/z wall, the common factor
is `X^20`. -/
theorem separatedYZSectionWall_commonParameterFactor_twenty
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hi3 : i ≠ 3)
    (hine : b i ≠ 0)
    (hstep :
      alignedSmithSectionWallStep i (b i) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasCommonParameterFactor 20
      (alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall) := by
  let N :=
    alignedSmithGenuineFirstWall
      P (zeroPolynomialSection (K := K)) b hwall
  have hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)) := by
    intro d hd
    dsimp [N]
    exact
      alignedSmithGenuineFirstWall_coefficient_nonnegative
        P (zeroPolynomialSection (K := K)) b
        hwall hd
  have hmargin :
      ∀ d ∈ P.support,
        4 * N + 20 ≤
          N * smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex *
              smithFamilyCoefficientOrder P d := by
    intro d hd
    dsimp [N]
    exact
      separatedYZSectionWall_coefficient_margin_twenty
        P b hwall hnotCoeff hnoPrimitive
        hi0 hi3 hine hstep hb hd
  have hout :=
    alignedSmith_commonFactor_of_margin
      (K := K)
      P N 20 hlegal hmargin
  simpa [alignedSmithGenuineFirstWallFamily, N] using hout

/-- Correspondingly, a separated y/z wall lowers the once-ramified
physical defect to exactly `20*(Delta-4)`. -/
theorem separatedYZSectionWall_hasHessianDefect_twenty_mul_sub_four
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    {i : Fin 4}
    (hi0 : i ≠ 0)
    (hi3 : i ≠ 3)
    (hine : b i ≠ 0)
    (hstep :
      alignedSmithSectionWallStep i (b i) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let Q :=
      alignedSmithGenuineFirstWallFamily
        (K := K) P
        (zeroPolynomialSection (K := K))
        b hwall
    let hcommon :=
      separatedYZSectionWall_commonParameterFactor_twenty
        P b hwall hnotCoeff hnoPrimitive
        hi0 hi3 hine hstep hb
    HasPolynomialFamilyHessianDefect
      (K := K)
      (commonParameterFactorFamily 20 Q hcommon)
      (alignedSmithRamificationIndex * (Delta - 4)) := by
  dsimp
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let hcommon :=
    separatedYZSectionWall_commonParameterFactor_twenty
      P b hwall hnotCoeff hnoPrimitive
      hi0 hi3 hine hstep hb
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWall_preservesHessianDefect
        P (zeroPolynomialSection (K := K)) b
        hwall Delta hdef
  have hbudget :
      4 * 20 ≤
        alignedSmithRamificationIndex * Delta :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) 20 Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQdef
  have hDelta : 4 ≤ Delta := by
    norm_num [alignedSmithRamificationIndex] at hbudget
    omega
  have hsub :
      alignedSmithRamificationIndex * Delta - 4 * 20 =
        alignedSmithRamificationIndex * (Delta - 4) := by
    norm_num [alignedSmithRamificationIndex]
    omega
  have hout :=
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (K := K)
      20 Q hcommon
      (alignedSmithRamificationIndex * Delta)
      hQdef
  rw [hsub] at hout
  exact hout

/-! ## Assembly boundary -/

/-- The exact missing geometric continuation interface exposed by the final
assembly audit.

The preceding theorems prove all algebraic data carried by a separated
right-section wall.  What remains is to choose a new pointed chart for its
moved nonzero special point and return a canonical geometric restart state
without introducing a fresh uncontrolled ramification.

Keeping this as a named proposition prevents the final well-founded theorem
from silently assuming the required chart continuation. -/
def HasCanonicalContinuationFromSeparatedRightWall
    (D : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) : Prop :=
  ∀ hsep : HasSeparatedRightSmithSectionWall P b,
    ∃ Delta' : ℕ,
      ∃ repair' : RepairState,
        ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
          ∃ b' : Fin 4 → Polynomial K,
            P'.IsHomogeneous D ∧
            HasPolynomialFamilyHessianDefect
              (K := K) P' Delta' ∧
            HasPolynomialFamilyExactGradientCollision
              P'
              (zeroPolynomialSection (K := K))
              b' ∧
            polynomialSectionSpecialPoint b' =
              coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Audit theorem: after the green positive-kernel transport and the closed
zero-slope Smith analysis, the only geometric datum not yet supplied by the
current Lean tree is the pointed continuation of a separated right-section
wall.

This theorem deliberately does not assert that the continuation exists; it
identifies its exact type so the final proof cannot hide it in the numerical
restart state. -/
theorem geometricAssembly_zeroSlope_reduced_to_rightSectionContinuation
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity ∨
      HasSeparatedRightSmithSectionWall P b := by
  exact
    alignedSmith_zeroSection_geometricDispatcher
      P hP b hdef hD hcoll hb complexity

end

end HC4.Valuation
