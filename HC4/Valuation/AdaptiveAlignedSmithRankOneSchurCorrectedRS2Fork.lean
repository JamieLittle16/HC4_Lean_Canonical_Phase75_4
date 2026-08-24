import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurKernelProvenanceAssembly
import Mathlib.Tactic

/-!
# Stage 4B31: the corrected RS2 fork

The first-key/source analysis is now total and B30 retains one and the same
Stage-3 Schur kernel through the whole descent.  Before identifying the final
Schur coefficient, it is important to record the *correct* second-order
algebra.

For the active first key

    a * x₀^e * L^m

the denominator-free second-order source is the quadratic form

    m(m-1) u^2 - 2 e m u v + e(e-1) v^2,

with `u = x₀ rhoX` and `v = L rhoL`.  This is the cleared adjugate quadratic
of the two-dimensional Euler Hessian core.  On the degree-zero Euler line

    u + v = 0

B25 says that it can vanish only when the projective motion itself vanishes.

The actual Schur/partial-Legendre calculation has a correction term.  Thus the
right final fork is not to assume the quadratic above is immediately zero.
Instead, if

    clearedRS2Source = correction,

then every genuinely nonconstant projective motion forces

    correction != 0.

Consequently the final geometric provenance theorem has exactly two jobs:

* identify the correction with the already-known mixed/rank-two repair source;
* in the null-correction branch, invoke the theorem below and obtain the B29
  null-RS2 contradiction.

This file is deliberately independent of the parameter first-actual-layer
order.  In particular it makes no identification between the spatial
first-key degree and any parameter clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The denominator-free adjugate quadratic attached to the Euler Hessian
core of `x^e L^m`.

Writing the Euler Hessian core as

    [[e(e-1), em],
     [em,     m(m-1)]],

this is the quadratic form of its formal `2 x 2` adjugate on `(u,v)`. -/
def xeLmClearedAdjugateQuadratic
    (e m : ℕ) (u v : K) : K :=
  (m : K) * ((m : K) - 1) * u ^ 2 -
    2 * (e : K) * (m : K) * u * v +
    (e : K) * ((e : K) - 1) * v ^ 2

/-- Source-coordinate version of the same cleared adjugate quadratic. -/
def xeLmClearedRS2Source
    (e m : ℕ) (x ell rhoX rhoL : K) : K :=
  xeLmClearedAdjugateQuadratic e m (x * rhoX) (ell * rhoL)

@[simp]
theorem xeLmClearedRS2Source_eq
    (e m : ℕ) (x ell rhoX rhoL : K) :
    xeLmClearedRS2Source e m x ell rhoX rhoL =
      (m : K) * ((m : K) - 1) * (x * rhoX) ^ 2 -
        2 * (e : K) * (m : K) * (x * rhoX) * (ell * rhoL) +
        (e : K) * ((e : K) - 1) * (ell * rhoL) ^ 2 := by
  rfl

/-- On the Euler line the cleared adjugate quadratic collapses to the single
coefficient `(e+m)(e+m-1)` times `u^2`.

This is the intrinsic scalar calculation behind B25, stated independently so
the corrected Schur identity can use it without unfolding the projective
coordinates. -/
theorem xeLmClearedAdjugateQuadratic_eq_eulerCoefficient_mul_sq
    (e m : ℕ) (u v : K)
    (hEuler : u + v = 0) :
    xeLmClearedAdjugateQuadratic e m u v =
      (((e : K) + (m : K)) *
        ((e : K) + (m : K) - 1)) * u ^ 2 := by
  have hv : v = -u := by
    linear_combination hEuler
  rw [hv]
  unfold xeLmClearedAdjugateQuadratic
  ring

/-- The determinant of the Euler Hessian core.  This identity is useful when
the final cleared-Schur calculation is written as a `2 x 2` adjugate identity:
the only scalar factor introduced by the active monomial is explicit. -/
theorem xeLmEulerHessianCoreDet
    (e m : ℕ) :
    (e : K) * ((e : K) - 1) *
          ((m : K) * ((m : K) - 1)) -
        ((e : K) * (m : K)) ^ 2 =
      -(e : K) * (m : K) *
        ((e : K) + (m : K) - 1) := by
  ring

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- An RS2-ready key admits no nontrivial Euler motion for which the cleared
second-order source vanishes.

This is the contrapositive form needed by the corrected Schur calculation:
for a genuinely moving projective direction, the second-order source is
*forced nonzero* unless an external correction cancels it. -/
theorem FirstKeyXeLmRS2ReadyData.clearedRS2Source_ne_zero_of_euler_motion
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (x ell rhoX rhoL : K)
    (hx : x ≠ 0)
    (hell : ell ≠ 0)
    (hEuler : x * rhoX + ell * rhoL = 0)
    (hmotion : rhoX ≠ 0 ∨ rhoL ≠ 0) :
    xeLmClearedRS2Source
        D.sourceExponent D.transverseDegree x ell rhoX rhoL ≠ 0 := by
  intro hzero
  have hpair :=
    xeLm_rs2ProjectiveDerivatives_eq_zero_of_totalDegree_two_le
      D.sourceExponent D.transverseDegree N.totalDegree_two_le
      x ell rhoX rhoL hx hell hEuler (by simpa using hzero)
  rcases hmotion with hrhoX | hrhoL
  · exact hrhoX hpair.1
  · exact hrhoL hpair.2

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- The first-order part of the final projective provenance theorem, separated
from the second-order Schur identity.

It consists of an active point away from `x₀ L = 0`, a genuinely nonzero pair
of projective-motion scalars, and the degree-zero Euler relation.  No RS2
identity is assumed here. -/
structure ActiveProjectiveEulerMotionWitness
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) where
  activePoint : E.ActiveProjectiveWedgePointData N i j k
  rhoX : K
  rhoL : K
  motion_ne_zero : rhoX ≠ 0 ∨ rhoL ≠ 0
  euler :
    activePoint.point 0 * rhoX +
      MvPolynomial.eval (fun r : Fin 3 => activePoint.point r.succ)
        N.normalForm.linearForm * rhoL = 0

/-- Every genuine active Euler motion has nonzero cleared RS2 source. -/
theorem ActiveProjectiveEulerMotionWitness.clearedRS2Source_ne_zero
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    {N : C.FirstKeyXeLmRS2ReadyData D}
    {E : DenominatorClearedSpecialSchurKernelData C}
    {i j k : Fin 4}
    (W : E.ActiveProjectiveEulerMotionWitness N i j k) :
    xeLmClearedRS2Source
        D.sourceExponent D.transverseDegree
        (W.activePoint.point 0)
        (MvPolynomial.eval
          (fun r : Fin 3 => W.activePoint.point r.succ)
          N.normalForm.linearForm)
        W.rhoX W.rhoL ≠ 0 := by
  exact
    N.clearedRS2Source_ne_zero_of_euler_motion
      (W.activePoint.point 0)
      (MvPolynomial.eval
        (fun r : Fin 3 => W.activePoint.point r.succ)
        N.normalForm.linearForm)
      W.rhoX W.rhoL
      W.activePoint.longitudinal_ne_zero
      W.activePoint.linearForm_ne_zero
      W.euler W.motion_ne_zero

/-- Correct second-order projective packet.

The cleared RS2 source is allowed to equal a correction scalar.  The next
geometric bridge must identify that correction with its honest Schur/mixed
source; this structure does **not** assume it vanishes. -/
structure ActiveProjectiveCorrectedRS2Witness
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) where
  motion : E.ActiveProjectiveEulerMotionWitness N i j k
  correction : K
  source_eq_correction :
    xeLmClearedRS2Source
        D.sourceExponent D.transverseDegree
        (motion.activePoint.point 0)
        (MvPolynomial.eval
          (fun r : Fin 3 => motion.activePoint.point r.succ)
          N.normalForm.linearForm)
        motion.rhoX motion.rhoL = correction

/-- **Corrected-RS2 fork.**

For a genuinely nonconstant projective motion the correction in the exact
second-order Schur identity cannot vanish.  Thus any final proof of
`source = correction` has only the intended alternatives:

* nonzero correction, which must be routed to certified mixed/rank-two repair;
* or no nonconstant projective motion at all.
-/
theorem ActiveProjectiveCorrectedRS2Witness.correction_ne_zero
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    {N : C.FirstKeyXeLmRS2ReadyData D}
    {E : DenominatorClearedSpecialSchurKernelData C}
    {i j k : Fin 4}
    (W : E.ActiveProjectiveCorrectedRS2Witness N i j k) :
    W.correction ≠ 0 := by
  rw [← W.source_eq_correction]
  exact W.motion.clearedRS2Source_ne_zero

/-- In particular a null correction immediately reconstructs the B29 null-RS2
witness and is impossible.  This adapter is convenient when the cleared Schur
calculation naturally returns the correction as a named scalar. -/
theorem ActiveProjectiveCorrectedRS2Witness.elim_of_correction_eq_zero
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    {N : C.FirstKeyXeLmRS2ReadyData D}
    {E : DenominatorClearedSpecialSchurKernelData C}
    {i j k : Fin 4}
    (W : E.ActiveProjectiveCorrectedRS2Witness N i j k)
    (hzero : W.correction = 0) : False := by
  exact W.correction_ne_zero hzero

/-- First-order provenance interface, now stated separately from RS2.

This is the next graded-projective extraction target: a nonzero polynomial
wedge must produce an active nonzero Euler motion for the *same* Stage-3
kernel retained by B30. -/
def HasEulerProjectiveWedgeProvenance
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C) : Prop :=
  ∀ i j k : Fin 4,
    E.projectiveWedge i j k ≠ 0 →
      Nonempty (E.ActiveProjectiveEulerMotionWitness N i j k)

/-- Corrected second-order provenance interface.  Unlike the provisional B29
interface, this is faithful to the actual Schur calculation: it retains the
correction instead of silently setting it to zero. -/
def HasCorrectedRS2ProjectiveWedgeProvenance
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C) : Prop :=
  ∀ i j k : Fin 4,
    E.projectiveWedge i j k ≠ 0 →
      Nonempty (E.ActiveProjectiveCorrectedRS2Witness N i j k)

/-- A corrected provenance theorem whose correction is known to vanish is
exactly strong enough to recover B29's old null-RS2 provenance interface. -/
theorem hasRS2ProjectiveWedgeProvenance_of_corrected_of_correction_zero
    {T : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData T}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (hprov : E.HasCorrectedRS2ProjectiveWedgeProvenance N)
    (hcorrection :
      ∀ i j k : Fin 4,
        ∀ hwedge : E.projectiveWedge i j k ≠ 0,
          ∀ W : E.ActiveProjectiveCorrectedRS2Witness N i j k,
            W.correction = 0) :
    E.HasRS2ProjectiveWedgeProvenance N := by
  intro i j k hwedge
  rcases hprov i j k hwedge with ⟨W⟩
  refine ⟨{
    activePoint := W.motion.activePoint
    rhoX := W.motion.rhoX
    rhoL := W.motion.rhoL
    motion_ne_zero := W.motion.motion_ne_zero
    euler := W.motion.euler
    rs2 := ?_
  }⟩
  have hzero := hcorrection i j k hwedge W
  have hsource :
      xeLmClearedRS2Source
          D.sourceExponent D.transverseDegree
          (W.motion.activePoint.point 0)
          (MvPolynomial.eval
            (fun r : Fin 3 => W.motion.activePoint.point r.succ)
            N.normalForm.linearForm)
          W.motion.rhoX W.motion.rhoL = 0 := by
    calc
      xeLmClearedRS2Source
          D.sourceExponent D.transverseDegree
          (W.motion.activePoint.point 0)
          (MvPolynomial.eval
            (fun r : Fin 3 => W.motion.activePoint.point r.succ)
            N.normalForm.linearForm)
          W.motion.rhoX W.motion.rhoL = W.correction :=
        W.source_eq_correction
      _ = 0 := hzero
  simpa [xeLmClearedRS2Source, xeLmClearedAdjugateQuadratic] using hsource

end DenominatorClearedSpecialSchurKernelData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
