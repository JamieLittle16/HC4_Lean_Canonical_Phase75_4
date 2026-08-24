import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurHomogeneousLinearPower
import Mathlib.Tactic

/-!
# Stage 4B24: unified `x₀^e L^m` normal form of the first spatial key

Stage 4B23 closes the only genuine rank-one transverse classification gap.
Outside the already-certified rank-two repair branch, the maximal homogeneous
first-key profile is now either

* transverse degree one, or
* an explicit scalar multiple of a power of one transverse linear form.

The degree-one branch is already of the same shape: simply take the linear
form to be the degree-one profile itself and the scalar to be `1`.

This file folds those branches together and restores the longitudinal factor
proved in Stages 4B4/4B11.  Thus the complete maximal homogeneous first-key
slice has, under `finSuccEquiv`, the exact form

    Polynomial.monomial e (C a * L^m),

which is precisely the coefficient-ring form of

    a * x₀^e * L^m.

No positivity of `e` is asserted here.  That point is intentionally retained
for the next Schur/RS2 adapter, because the already-green Stage 4B2 rigidity
uses `e > 0` and the `e = 0` boundary must be discharged rather than assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Exact source-monomial form of the canonical maximal homogeneous slice.

This is the B11 longitudinal factorisation rewritten using the B12/B14
`sourceExponent` and `transverseSourceProfile` names. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.slice_finSuccEquiv_eq_sourceMonomial
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice =
      Polynomial.monomial D.sourceExponent D.transverseSourceProfile := by
  simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent,
    FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile] using
    D.slice_finSuccEquiv_eq_monomial

/-- Unified non-repair normal form for the complete maximal homogeneous
first-key slice.

The equality `slice_eq` is the literal `finSuccEquiv` representation of
`a * x₀^e * L^m`; no support-level approximation remains. -/
structure FirstKeyXeLmNormalFormData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) where
  coefficient : K
  linearForm : MvPolynomial (Fin 3) K
  transverse_eq :
    D.transverseSourceProfile =
      MvPolynomial.C coefficient * linearForm ^ D.transverseDegree
  slice_eq :
    MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice =
      Polynomial.monomial D.sourceExponent
        (MvPolynomial.C coefficient * linearForm ^ D.transverseDegree)

/-- The degree-one branch is already a linear-power branch: use the source
profile itself as the linear form. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.xeLmNormalForm_of_degree_one
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (hm : D.transverseDegree = 1) :
    Nonempty (C.FirstKeyXeLmNormalFormData D) := by
  refine ⟨{
    coefficient := 1
    linearForm := D.transverseSourceProfile
    transverse_eq := ?_
    slice_eq := ?_
  }⟩
  · simp [hm]
  · rw [D.slice_finSuccEquiv_eq_sourceMonomial]
    simp [hm]

/-- The B23 classified residual already has the unified `x₀^e L^m` source
shape; this theorem merely restores the longitudinal monomial factor. -/
theorem FirstKeyRankOneLinearPowerResidualData.toXeLmNormalFormData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyRankOneLinearPowerResidualData D F) :
    Nonempty (C.FirstKeyXeLmNormalFormData D) := by
  refine ⟨{
    coefficient := R.linearPower.coefficient
    linearForm := gradientRatioLinearForm R.linearPower.ratio
    transverse_eq := R.linearPower.eq_power
    slice_eq := ?_
  }⟩
  rw [D.slice_finSuccEquiv_eq_sourceMonomial]
  exact congrArg (Polynomial.monomial D.sourceExponent) R.linearPower.eq_power

/-- **Stage 4B24 unified first-key frontier.**

Outside the already-existing rank-two repair progress, *every* surviving
maximal homogeneous first spatial key is exactly `a * x₀^e * L^m` in the
coefficient-ring representation.  The former degree-one branch has been
absorbed into the same normal form.
-/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.rankTwoRepair_or_xeLmNormalForm
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyXeLmNormalFormData D) := by
  rcases D.degreeOne_or_rankTwoRepair_or_linearPowerResidual F complexity with
    hm | hrest
  · exact Or.inr (D.xeLmNormalForm_of_degree_one hm)
  · rcases hrest with hrepair | hlinear
    · exact Or.inl hrepair
    · rcases hlinear with ⟨R⟩
      exact Or.inr R.toXeLmNormalFormData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
