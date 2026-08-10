import HC4.Valuation.RigidClosingRecenteredSource
import HC4.Valuation.ExactKernelDefectDrop
import HC4.Valuation.GeometricAssemblyEntry
import HC4.Valuation.AlignedSmithWallArithmetic
import Mathlib.Tactic

/-!
# First global kernel stage at a rigid determinant closing

The evaluated zero-Schur clock supplies a positive first common parameter
order `e`.  What it does *not* supply automatically is coefficientwise
integrality of the corresponding source blow-up on the whole recentered
polynomial family.

This file makes that distinction exact.

For the canonically recentered rigid-closing family `Q`, use source
coordinate `3`, which is transverse in both rigid charts.  The first common
Schur order gives a positive candidate slope `e` with

    2*e <= N,

where `N = 20*defect` is the exact Hessian determinant order.

Then finite support gives an exhaustive alternative:

* every coefficient of `Q` is divisible by the power required for the
  coordinate-3 integral kernel blow-up; or
* there is an actual supported source monomial whose coefficient fails that
  divisibility.

In the integral branch the already-green concrete kernel-blow-up machinery
constructs an honest polynomial family, preserves the moving exact gradient
collision and the canonical special points `0,e0`, and changes the Hessian
order exactly from `N` to `N-2*e`.

In the non-integral branch we strengthen the witness to the strict numerical
inequality

    ord_X(coeff_d Q) < e * d(3).

That is the finite-support obstruction needed by the next Newton/valuation
refinement step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Coordinate `3` is the chart-independent residual kernel direction used
for the first global source blow-up. -/
def rigidClosingCommonKernel : Fin 4 := 3

@[simp] theorem rigidClosingCommonKernel_ne_zero :
    rigidClosingCommonKernel ≠ (0 : Fin 4) := by
  decide

/-- Elementary finite-support dichotomy for one proposed integral kernel
blow-up.  This deliberately exposes a concrete offending monomial when
coefficientwise integrality fails. -/
theorem integralKernelDivisibility_or_supportOffender
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasIntegralKernelCoefficientDivisibility kernel slope P ∨
      ∃ d ∈ P.support,
        ¬ kernelCoefficientTauPower (K := K) kernel slope d ∣
          MvPolynomial.coeff d P := by
  classical
  by_cases hdiv :
      HasIntegralKernelCoefficientDivisibility kernel slope P
  · exact Or.inl hdiv
  · right
    unfold HasIntegralKernelCoefficientDivisibility at hdiv
    push_neg at hdiv
    exact hdiv

/-- Admissible integral kernel slopes are downward closed. -/
theorem integralKernelCoefficientDivisibility_mono
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {q r : ℕ}
    (hqr : q ≤ r)
    (hr : HasIntegralKernelCoefficientDivisibility kernel r P) :
    HasIntegralKernelCoefficientDivisibility kernel q P := by
  intro d hd
  have hexp : q * d kernel ≤ r * d kernel :=
    Nat.mul_le_mul_right (d kernel) hqr
  have hpow :
      (Polynomial.X ^ (q * d kernel) : Polynomial K) ∣
        Polynomial.X ^ (r * d kernel) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (q * d kernel) (r * d kernel) hexp
  unfold kernelCoefficientTauPower
  exact dvd_trans hpow (hr d hd)


/-- Proof-independent exact parameter order of a source coefficient.  Outside
the source support the coefficient is zero and we assign order `0`; on the
actual support this agrees with `smithFamilyCoefficientParameterOrder`. -/
noncomputable def sourceCoefficientParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ := by
  classical
  exact
    if h : MvPolynomial.coeff d P = 0 then
      0
    else
      polynomialParameterOrder (MvPolynomial.coeff d P) h

/-- A failed coefficient divisibility condition is equivalently a strict
shortfall of the exact `X`-adic order of that supported coefficient. -/
theorem supportOffender_parameterOrder_lt_required
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support)
    (hfail :
      ¬ kernelCoefficientTauPower (K := K) kernel slope d ∣
        MvPolynomial.coeff d P) :
    sourceCoefficientParameterOrder P d < slope * d kernel := by
  have hne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  unfold sourceCoefficientParameterOrder
  rw [dif_neg hne]
  by_contra hnot
  have hreq :
      slope * d kernel ≤
        polynomialParameterOrder (MvPolynomial.coeff d P) hne := by
    omega
  have hpow :
      (Polynomial.X ^ (slope * d kernel) : Polynomial K) ∣
        Polynomial.X ^
          (polynomialParameterOrder (MvPolynomial.coeff d P) hne) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (slope * d kernel)
      (polynomialParameterOrder (MvPolynomial.coeff d P) hne)
      hreq
  have hcoeff :
      Polynomial.X ^
          (polynomialParameterOrder (MvPolynomial.coeff d P) hne) ∣
        MvPolynomial.coeff d P :=
    polynomialParameterOrder_dvd (MvPolynomial.coeff d P) hne
  apply hfail
  unfold kernelCoefficientTauPower
  exact dvd_trans hpow hcoeff

/-- The first common zero-Schur order attached to a rigid closing is positive
and consumes at most the available Hessian defect.  The theorem is stated
existentially because `RigidClosingCertificate` is a proposition and should
not be used as computational data. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingCertificate.exists_firstKernelOrder
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (hclose : f.RigidClosingCertificate) :
    ∃ e : ℕ,
      0 < e ∧
      2 * e ≤ alignedSmithRamificationIndex * f.defect := by
  cases hclose with
  | left hD hrigid hpivot hclosing =>
      let B := f.rigidLeftZeroSchurData hrigid hpivot hD
      refine ⟨B.toClock.firstOrder, B.toClock.firstOrder_pos, ?_⟩
      have hle := B.toClock.twice_firstOrder_le_defect
      have hdef :
          B.toClock.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      rw [hdef] at hle
      exact hle
  | right hD hrigid hpivot hclosing =>
      let B := f.rigidRightZeroSchurData hrigid hpivot hD
      refine ⟨B.toClock.firstOrder, B.toClock.firstOrder_pos, ?_⟩
      have hle := B.toClock.twice_firstOrder_le_defect
      have hdef :
          B.toClock.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      rw [hdef] at hle
      exact hle

namespace CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData

variable [CharZero K]
variable {D complexity : ℕ}
variable {f : CanonicalSmithDepartureFrontier (K := K) D complexity}

/-- In the integral first-stage branch, the exact determinant order drops by
`2*e`; this is a theorem of the concrete kernel blow-up, not an assumption. -/
theorem firstKernelBlowup_hessianDefect
    (S : f.RigidClosingRecenteredSourceData)
    (e : ℕ)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel e S.family) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (integralKernelBlowupFamily
        rigidClosingCommonKernel e S.family hdiv)
      (alignedSmithRamificationIndex * f.defect - 2 * e) := by
  exact
    integralKernelBlowup_hasHessianDefect_sub
      rigidClosingCommonKernel e
      (alignedSmithRamificationIndex * f.defect)
      S.family hdiv S.hessianDefect

/-- The exact moving gradient collision survives the first integral stage. -/
theorem firstKernelBlowup_exactCollision
    (S : f.RigidClosingRecenteredSourceData)
    (e : ℕ)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel e S.family) :
    HasPolynomialFamilyExactGradientCollision
      (integralKernelBlowupFamily
        rigidClosingCommonKernel e S.family hdiv)
      (kernelBlowupSection
        rigidClosingCommonKernel e
        (zeroPolynomialSection (K := K)))
      (kernelBlowupSection
        rigidClosingCommonKernel e S.rightSection) := by
  exact
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      rigidClosingCommonKernel e S.family hdiv
      (zeroPolynomialSection (K := K)) S.rightSection
      S.exactCollision

/-- Positive first-stage blow-up leaves the canonical right reduction `e0`
unchanged because coordinate `3` is transverse to the marked axis. -/
theorem firstKernelBlowup_rightSpecial
    (S : f.RigidClosingRecenteredSourceData)
    {e : ℕ}
    (he : 0 < e) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection
          rigidClosingCommonKernel e S.rightSection) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact
    polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
      rigidClosingCommonKernel he
      rigidClosingCommonKernel_ne_zero
      S.rightSection S.rightSpecial

/-- Consequently the first-stage transformed moving sections still have
canonically distinct specialisations. -/
theorem firstKernelBlowup_specialPoints_ne
    (S : f.RigidClosingRecenteredSourceData)
    {e : ℕ}
    (he : 0 < e) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection
          rigidClosingCommonKernel e
          (zeroPolynomialSection (K := K))) ≠
      polynomialSectionSpecialPoint
        (kernelBlowupSection
          rigidClosingCommonKernel e S.rightSection) := by
  exact
    canonicalSpecialPointsDistinct_after_positive_transverseKernelBlowup
      rigidClosingCommonKernel he
      rigidClosingCommonKernel_ne_zero
      S.rightSection S.rightSpecial

/-- Successful first global kernel stage for one retained closing
four-block. -/
def HasIntegralRigidClosingFirstKernelStage
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K) : Prop :=
  let e := B.toClock.firstOrder
  ∃ hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel e S.family,
    HasPolynomialFamilyHessianDefect
        (K := K)
        (integralKernelBlowupFamily
          rigidClosingCommonKernel e S.family hdiv)
        B.toClock.residualDefect ∧
    HasPolynomialFamilyExactGradientCollision
        (integralKernelBlowupFamily
          rigidClosingCommonKernel e S.family hdiv)
        (kernelBlowupSection
          rigidClosingCommonKernel e
          (zeroPolynomialSection (K := K)))
        (kernelBlowupSection
          rigidClosingCommonKernel e S.rightSection) ∧
    polynomialSectionSpecialPoint
        (kernelBlowupSection
          rigidClosingCommonKernel e S.rightSection) =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Explicit obstruction to the first global kernel stage. -/
def HasRigidClosingFirstKernelOffender
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K) : Prop :=
  let e := B.toClock.firstOrder
  ∃ d ∈ S.family.support,
    sourceCoefficientParameterOrder S.family d <
      e * d rigidClosingCommonKernel

/-- An explicit first-stage offender proves that coordinate `3` is
actually active in the recentered source family. -/
theorem firstKernelOffender_active
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hoff : HasRigidClosingFirstKernelOffender S B) :
    IsActiveKernelCoordinate rigidClosingCommonKernel S.family := by
  unfold HasRigidClosingFirstKernelOffender at hoff
  dsimp only at hoff
  rcases hoff with ⟨d, hd, hlt⟩
  refine ⟨d, hd, ?_⟩
  by_contra hzero
  have hd0 : d rigidClosingCommonKernel = 0 := Nat.eq_zero_of_not_pos hzero
  rw [hd0] at hlt
  simp at hlt

/-- The candidate closing slope itself is not globally integral whenever an
offending source monomial exists. -/
theorem firstKernelOffender_not_candidateDivisibility
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hoff : HasRigidClosingFirstKernelOffender S B) :
    ¬ HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel B.toClock.firstOrder S.family := by
  intro hdiv
  unfold HasRigidClosingFirstKernelOffender at hoff
  dsimp only at hoff
  rcases hoff with ⟨d, hd, hlt⟩
  have hne : MvPolynomial.coeff d S.family ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdvd := hdiv d hd
  have hle :
      B.toClock.firstOrder * d rigidClosingCommonKernel ≤
        polynomialParameterOrder (MvPolynomial.coeff d S.family) hne := by
    exact
      polynomial_X_pow_dvd_le_parameterOrder
        (MvPolynomial.coeff d S.family) hne
        (B.toClock.firstOrder * d rigidClosingCommonKernel)
        (by simpa [kernelCoefficientTauPower] using hdvd)
  unfold sourceCoefficientParameterOrder at hlt
  rw [dif_neg hne] at hlt
  omega

/-- Therefore the maximal admissible integral coordinate-3 slope lies
strictly below the Schur candidate `e`. -/
theorem firstKernelOffender_maximalSlope_lt_firstOrder
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hoff : HasRigidClosingFirstKernelOffender S B) :
    maximalIntegralKernelSlope
        rigidClosingCommonKernel S.family
        (S.firstKernelOffender_active B hoff) <
      B.toClock.firstOrder := by
  let hactive := S.firstKernelOffender_active B hoff
  let q := maximalIntegralKernelSlope
    rigidClosingCommonKernel S.family hactive
  have hqdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel q S.family :=
    maximalIntegralKernelSlope_divisibility
      rigidClosingCommonKernel S.family hactive
  by_contra hnot
  have heq : B.toClock.firstOrder ≤ q := by omega
  have hediv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel B.toClock.firstOrder S.family :=
    integralKernelCoefficientDivisibility_mono
      rigidClosingCommonKernel S.family heq hqdiv
  exact S.firstKernelOffender_not_candidateDivisibility B hoff hediv

/-- Zero maximal slope is the only offender subcase not already handled by
the existing positive-slope restart machine. -/
def HasRigidClosingZeroCommonKernelSlopeObstruction
    (S : f.RigidClosingRecenteredSourceData) : Prop :=
  ∃ hactive : IsActiveKernelCoordinate rigidClosingCommonKernel S.family,
    maximalIntegralKernelSlope
        rigidClosingCommonKernel S.family hactive = 0 ∧
    ¬ ∃ q : ℕ,
      0 < q ∧
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel q S.family

/-- A **concrete** strict kernel restart from the recentered closing
source.  The witness retains the actual integral blow-up family and the two
transformed moving sections through a `PolynomialFamilyKernelRestartCertificate`;
it is therefore much stronger than merely asserting the existence of a
numerically smaller restart state. -/
def HasRigidClosingStrictKernelRestart
    (S : f.RigidClosingRecenteredSourceData) : Prop :=
  ∃ q : ℕ,
    ∃ hdiv :
        HasIntegralKernelCoefficientDivisibility
          rigidClosingCommonKernel q S.family,
      0 < q ∧
      let s0 : GlobalRestartState :=
        { defect := alignedSmithRamificationIndex * f.defect
          repair := rankOneRepairState complexity }
      let t : GlobalRestartState :=
        { defect := alignedSmithRamificationIndex * f.defect - 2 * q
          repair := rankOneRepairState complexity }
      PolynomialFamilyKernelRestartCertificate
        s0 t q
        (integralKernelBlowupFamily
          rigidClosingCommonKernel q S.family hdiv)
        (kernelBlowupSection
          rigidClosingCommonKernel q
          (zeroPolynomialSection (K := K)))
        (kernelBlowupSection
          rigidClosingCommonKernel q S.rightSection)

/-- **Phase 75.19 restart collapse.**

Any successful first global kernel stage is already a genuine strict restart.
The first zero-Schur order is positive, the integral blow-up preserves the
exact moving collision and the canonical distinct specialisations, and the
exact Hessian defect drops by `2 * firstOrder`.  Therefore there is no need
to retain separate zero-residual and positive-residual integral branches in
the rigid-closing endgame. -/
theorem integralFirstKernelStage_to_strictRestart
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hint : HasIntegralRigidClosingFirstKernelStage S B) :
    HasRigidClosingStrictKernelRestart S := by
  unfold HasIntegralRigidClosingFirstKernelStage at hint
  dsimp only at hint
  rcases hint with ⟨hdiv, _hdef, _hcoll, _hspecial⟩
  unfold HasRigidClosingStrictKernelRestart
  refine ⟨B.toClock.firstOrder, hdiv, B.toClock.firstOrder_pos, ?_⟩
  let s0 : GlobalRestartState :=
    { defect := alignedSmithRamificationIndex * f.defect
      repair := rankOneRepairState complexity }
  let t : GlobalRestartState :=
    { defect := alignedSmithRamificationIndex * f.defect -
          2 * B.toClock.firstOrder
      repair := rankOneRepairState complexity }
  have hspecial :
      polynomialSectionSpecialPoint
          (kernelBlowupSection
            rigidClosingCommonKernel B.toClock.firstOrder
            (zeroPolynomialSection (K := K))) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection
            rigidClosingCommonKernel B.toClock.firstOrder S.rightSection) := by
    exact S.firstKernelBlowup_specialPoints_ne B.toClock.firstOrder_pos
  have hdrop :
      HasPositiveKernelDefectDrop B.toClock.firstOrder s0 t := by
    exact
      integralKernelBlowup_positiveKernelDefectDrop
        rigidClosingCommonKernel B.toClock.firstOrder_pos
        S.family hdiv S.hessianDefect rfl rfl
  exact
    integralKernelBlowup_toPolynomialFamilyKernelRestartCertificate
      rigidClosingCommonKernel B.toClock.firstOrder S.family hdiv
      (zeroPolynomialSection (K := K)) S.rightSection
      S.exactCollision hspecial hdrop

/-- Every explicit first-stage offender either has no positive integral
coordinate-3 slope at all, or the already-green maximal-slope machinery
produces an immediate strict global restart. -/
theorem firstKernelOffender_zeroSlope_or_strictRestart
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hoff : HasRigidClosingFirstKernelOffender S B) :
    HasRigidClosingZeroCommonKernelSlopeObstruction S ∨
      HasRigidClosingStrictKernelRestart S := by
  let hactive := S.firstKernelOffender_active B hoff
  rcases maximalIntegralKernelSlope_zero_or_positive
      rigidClosingCommonKernel S.family hactive with hzero | hpos
  · left
    exact ⟨hactive, hzero.1, hzero.2⟩
  · right
    unfold HasRigidClosingStrictKernelRestart
    let q := maximalIntegralKernelSlope
      rigidClosingCommonKernel S.family hactive
    let hdiv :
        HasIntegralKernelCoefficientDivisibility
          rigidClosingCommonKernel q S.family :=
      maximalIntegralKernelSlope_divisibility
        rigidClosingCommonKernel S.family hactive
    refine ⟨q, hdiv, hpos.1, ?_⟩
    let s0 : GlobalRestartState :=
      { defect := alignedSmithRamificationIndex * f.defect
        repair := rankOneRepairState complexity }
    let t : GlobalRestartState :=
      { defect := alignedSmithRamificationIndex * f.defect - 2 * q
        repair := rankOneRepairState complexity }
    have hspecial :
        polynomialSectionSpecialPoint
            (kernelBlowupSection
              rigidClosingCommonKernel q
              (zeroPolynomialSection (K := K))) ≠
          polynomialSectionSpecialPoint
            (kernelBlowupSection
              rigidClosingCommonKernel q S.rightSection) := by
      exact S.firstKernelBlowup_specialPoints_ne hpos.1
    have hdrop : HasPositiveKernelDefectDrop q s0 t := by
      exact
        integralKernelBlowup_positiveKernelDefectDrop
          rigidClosingCommonKernel hpos.1 S.family hdiv
          S.hessianDefect rfl rfl
    exact
      integralKernelBlowup_toPolynomialFamilyKernelRestartCertificate
        rigidClosingCommonKernel q S.family hdiv
        (zeroPolynomialSection (K := K)) S.rightSection
        S.exactCollision hspecial hdrop

/-- Block-level first-stage dichotomy.  The transformed Hessian order is
identified with the *same* residual defect stored by the zero-Schur clock. -/
theorem firstClosingKernelStage_forBlock
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hBdef :
      B.defect = alignedSmithRamificationIndex * f.defect) :
    let e := B.toClock.firstOrder
    0 < e ∧
    2 * e ≤ B.defect ∧
    (HasIntegralRigidClosingFirstKernelStage S B ∨
      HasRigidClosingFirstKernelOffender S B) := by
  classical
  dsimp only
  refine ⟨B.toClock.firstOrder_pos,
    B.toClock.twice_firstOrder_le_defect, ?_⟩
  rcases integralKernelDivisibility_or_supportOffender
      (K := K) rigidClosingCommonKernel B.toClock.firstOrder S.family with
    hdiv | hoff
  · left
    unfold HasIntegralRigidClosingFirstKernelStage
    dsimp only
    refine ⟨hdiv, ?_,
      S.firstKernelBlowup_exactCollision B.toClock.firstOrder hdiv,
      S.firstKernelBlowup_rightSpecial B.toClock.firstOrder_pos⟩
    have hdef :=
      S.firstKernelBlowup_hessianDefect B.toClock.firstOrder hdiv
    have hres :
        alignedSmithRamificationIndex * f.defect -
            2 * B.toClock.firstOrder =
          B.toClock.residualDefect := by
      unfold ExactZeroSchurClock.residualDefect
      change
        alignedSmithRamificationIndex * f.defect -
            2 * B.toClock.firstOrder =
          B.defect - 2 * B.toClock.firstOrder
      rw [hBdef]
    rw [hres] at hdef
    exact hdef
  · right
    unfold HasRigidClosingFirstKernelOffender
    dsimp only
    rcases hoff with ⟨d, hd, hfail⟩
    refine ⟨d, hd, ?_⟩
    exact supportOffender_parameterOrder_lt_required
      rigidClosingCommonKernel B.toClock.firstOrder S.family d hd hfail

/-- Closing-aware three-way split for an explicitly supplied zero-Schur
four-block.  This version is deliberately independent of
`S.original.closing`; it is the entry point used after the Schur clock has
been rebuilt on the recentered family itself. -/
theorem firstClosingKernelStage_terminal_or_residual_or_offender_forBlock
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hBdef :
      B.defect = alignedSmithRamificationIndex * f.defect)
    (hclosing : ExactZeroSchurClosingOutcome B) :
    (B.toClock.residualDefect = 0 ∧
        HasIntegralRigidClosingFirstKernelStage S B) ∨
      (0 < B.toClock.residualDefect ∧
        HasIntegralRigidClosingFirstKernelStage S B) ∨
      HasRigidClosingFirstKernelOffender S B := by
  have hstage := S.firstClosingKernelStage_forBlock B hBdef
  dsimp only at hstage
  rcases hstage.2.2 with hintegral | hoffender
  · unfold ExactZeroSchurClosingOutcome at hclosing
    rcases hclosing with hdirect | hsecond
    · exact Or.inl ⟨hdirect.1, hintegral⟩
    · rcases hsecond with ⟨_R, hres, _hRdef, _hRclose, _hRnonzero⟩
      exact Or.inr (Or.inl ⟨hres, hintegral⟩)
  · exact Or.inr (Or.inr hoffender)

/-- **Phase 75.17 first-stage global dichotomy with closing provenance.**

The output retains the exact zero-Schur four-block `B` that came from the
rigid left/right chart and its actual closing proof.  Thus no clock data is
lost when we pass from the evaluated Schur analysis back to the global
polynomial family.

For `e = B.toClock.firstOrder`, either:

* the whole recentered family admits the honest coordinate-3 integral
  kernel blow-up, whose exact Hessian order is
  `B.toClock.residualDefect` and whose moving collision still specialises to
  `0 ~ e0`; or
* a concrete supported monomial has exact parameter order strictly below
  the required lattice order `e*d(3)`.
-/
theorem firstClosingKernelStage_integral_or_offender
    (S : f.RigidClosingRecenteredSourceData) :
    ∃ B : ExactZeroSchurFourBlockData K,
      ExactZeroSchurClosingOutcome B ∧
      B.defect = alignedSmithRamificationIndex * f.defect ∧
      0 < B.toClock.firstOrder ∧
      2 * B.toClock.firstOrder ≤ B.defect ∧
      (HasIntegralRigidClosingFirstKernelStage S B ∨
        HasRigidClosingFirstKernelOffender S B) := by
  cases S.original.closing with
  | left hD hrigid hpivot hclosing =>
      let B := f.rigidLeftZeroSchurData hrigid hpivot hD
      have hBdef :
          B.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      have hstage := S.firstClosingKernelStage_forBlock B hBdef
      dsimp only at hstage
      exact ⟨B, hclosing, hBdef, hstage.1, hstage.2.1, hstage.2.2⟩
  | right hD hrigid hpivot hclosing =>
      let B := f.rigidRightZeroSchurData hrigid hpivot hD
      have hBdef :
          B.defect = alignedSmithRamificationIndex * f.defect := by
        rfl
      have hstage := S.firstClosingKernelStage_forBlock B hBdef
      dsimp only at hstage
      exact ⟨B, hclosing, hBdef, hstage.1, hstage.2.1, hstage.2.2⟩

/-- **Three-way first-stage closure split.**

On the integral branch, the closing proof itself decides whether the first
kernel blow-up has already exhausted the determinant clock or leaves a
strictly positive residual clock.  The only third possibility is an explicit
source coefficient whose parameter order is too small for the candidate
blow-up. -/
theorem firstClosingKernelStage_terminal_or_residual_or_offender
    (S : f.RigidClosingRecenteredSourceData) :
    ∃ B : ExactZeroSchurFourBlockData K,
      B.defect = alignedSmithRamificationIndex * f.defect ∧
      ((B.toClock.residualDefect = 0 ∧
          HasIntegralRigidClosingFirstKernelStage S B) ∨
       (0 < B.toClock.residualDefect ∧
          HasIntegralRigidClosingFirstKernelStage S B) ∨
       HasRigidClosingFirstKernelOffender S B) := by
  rcases S.firstClosingKernelStage_integral_or_offender with
    ⟨B, hclosing, hBdef, he, hle, hintegral | hoffender⟩
  · refine ⟨B, hBdef, ?_⟩
    unfold ExactZeroSchurClosingOutcome at hclosing
    rcases hclosing with hdirect | hsecond
    · exact Or.inl ⟨hdirect.1, hintegral⟩
    · rcases hsecond with ⟨_R, hres, _hRdef, _hRclose, _hRnonzero⟩
      exact Or.inr (Or.inl ⟨hres, hintegral⟩)
  · exact ⟨B, hBdef, Or.inr (Or.inr hoffender)⟩

/-- An integral first stage with zero residual clock is already an honest
defect-zero polynomial-family collision.  This is the source object from
which the terminal associated-graded endpoint will be read in the direct
closing branch. -/
theorem integralFirstKernelStage_zeroResidual_data
    (S : f.RigidClosingRecenteredSourceData)
    (B : ExactZeroSchurFourBlockData K)
    (hzero : B.toClock.residualDefect = 0)
    (hint : HasIntegralRigidClosingFirstKernelStage S B) :
    ∃ hdiv :
        HasIntegralKernelCoefficientDivisibility
          rigidClosingCommonKernel B.toClock.firstOrder S.family,
      HasPolynomialFamilyHessianDefect
          (K := K)
          (integralKernelBlowupFamily
            rigidClosingCommonKernel B.toClock.firstOrder S.family hdiv)
          0 ∧
      HasPolynomialFamilyExactGradientCollision
          (integralKernelBlowupFamily
            rigidClosingCommonKernel B.toClock.firstOrder S.family hdiv)
          (kernelBlowupSection
            rigidClosingCommonKernel B.toClock.firstOrder
            (zeroPolynomialSection (K := K)))
          (kernelBlowupSection
            rigidClosingCommonKernel B.toClock.firstOrder S.rightSection) ∧
      polynomialSectionSpecialPoint
          (kernelBlowupSection
            rigidClosingCommonKernel B.toClock.firstOrder S.rightSection) =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
  unfold HasIntegralRigidClosingFirstKernelStage at hint
  dsimp only at hint
  rcases hint with ⟨hdiv, hdef, hcoll, hspecial⟩
  refine ⟨hdiv, ?_, hcoll, hspecial⟩
  rw [hzero] at hdef
  exact hdef

/-- If the first common order exhausts the determinant clock, the integral
branch already produces a defect-zero family with the same exact moving
collision and canonical special points. -/
theorem firstKernelBlowup_terminalDefect_of_exactClosure
    (S : f.RigidClosingRecenteredSourceData)
    (e : ℕ)
    (heq : alignedSmithRamificationIndex * f.defect = 2 * e)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel e S.family) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (integralKernelBlowupFamily
        rigidClosingCommonKernel e S.family hdiv)
      0 := by
  have h := S.firstKernelBlowup_hessianDefect e hdiv
  simpa [heq] using h

end CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData

end

end HC4.Valuation
