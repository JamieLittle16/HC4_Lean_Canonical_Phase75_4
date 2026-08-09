import HC4.Valuation.LinearCovariance
import HC4.Newton.GlobalRestartClassification
import HC4.Newton.RestartClassification
import Mathlib.Tactic

/-!
# Kernel blow-up certificate

This file is the interface between the safe algebra layer and the concrete
DVR/kernel-blow-up construction.

A concrete kernel blow-up must establish four pieces of information:

1. the transformed polynomial has the exact normalised gradient covariance;
2. the marked transformed points remain distinct;
3. the source polynomial has the marked exact collision at their images;
4. the determinant defect changes by the certified positive kernel-slope
   rule `Delta' = Delta - 2*q`.

Nothing else is assumed.

From those four facts Lean derives simultaneously:

* distinctness of the new marked points;
* preservation of the exact gradient collision;
* strict determinant-defect decrease;
* `GlobalRestartProgress`.

Thus the later concrete valuation file does not have to re-prove any
restart or collision logic.  Its sole job is to construct this certificate
from the actual polynomial-family/kernel rescaling.

The final theorem in this file also shows that if the target polynomial is
already one of the certified terminal endpoints, JC2 gives an immediate
contradiction.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Exact restart data that a concrete positive-slope kernel blow-up must
produce.

The source collision is expressed at the images `D*p` and `D*r`, so the
linear covariance theorem transports it exactly to the transformed
polynomial `P` at `p,r`.

The global source/target states are deliberately independent of the
polynomial data except through the positive defect-drop certificate.  This
matches the lexicographic restart architecture: a defect drop may reset the
local repair state. -/
structure KernelBlowupCertificate
    (s t : HC4.Newton.GlobalRestartState)
    (slope : ℕ)
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (F P : MvPolynomial (Fin 4) K)
    (p r : Fin 4 -> K) : Prop where
  gradientCovariance :
    HasNormalizedGradientCovariance mu D F P
  transformedPointsDistinct :
    D.mulVec p ≠ D.mulVec r
  sourceCollision :
    HC4.Newton.HasExactGradientCollision
      F (D.mulVec p) (D.mulVec r)
  positiveDefectDrop :
    HC4.Newton.HasPositiveKernelDefectDrop
      slope s t

/-- The concrete certificate automatically transports the marked collision
to the transformed polynomial and preserves distinctness. -/
theorem KernelBlowupCertificate.distinct_collision
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    p ≠ r ∧
      HC4.Newton.HasExactGradientCollision
        P p r := by
  exact
    distinctExactGradientCollision_of_normalizedGradientCovariance
      mu D F P p r
      h.gradientCovariance
      h.transformedPointsDistinct
      h.sourceCollision

/-- The concrete certificate automatically gives strict global restart
progress. -/
theorem KernelBlowupCertificate.globalProgress
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    HC4.Newton.GlobalRestartProgress s t := by
  exact
    HC4.Newton.globalRestartProgress_of_positiveKernelDefectDrop
      h.positiveDefectDrop

/-- The determinant defect of the target is strictly smaller. -/
theorem KernelBlowupCertificate.defect_lt
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    t.defect < s.defect := by
  exact
    HC4.Newton.positiveKernelDefectDrop_defect_lt
      h.positiveDefectDrop

/-- The positive kernel slope is genuinely positive. -/
theorem KernelBlowupCertificate.slope_pos
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    0 < slope := by
  exact h.positiveDefectDrop.1

/-- The target defect is exactly the arithmetic update
`source defect - 2*slope`. -/
theorem KernelBlowupCertificate.defect_eq
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    t.defect = s.defect - 2 * slope := by
  exact h.positiveDefectDrop.2.2

/-- **Complete positive kernel-blow-up consequence package.**

This is the theorem intended for the global DVR restart dispatcher.  Once
the concrete valuation construction has produced a
`KernelBlowupCertificate`, all logical consequences of the blow-up are
available in one call. -/
theorem kernelBlowup_preservesCollision_and_strictlyRestarts
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (h : KernelBlowupCertificate
      s t slope mu D F P p r) :
    p ≠ r ∧
      HC4.Newton.HasExactGradientCollision P p r ∧
      t.defect < s.defect ∧
      HC4.Newton.GlobalRestartProgress s t := by
  have hcoll := h.distinct_collision
  exact
    ⟨hcoll.1, hcoll.2,
      h.defect_lt, h.globalProgress⟩

/-! ## Conformal Hessian determinant component

The concrete polynomial transformation will also need to instantiate the
matrix chain rule proved in Phase 93.49.  We package the exact determinant
consequence here so the valuation file only has to identify its Hessian
with the normalised congruence.
-/

/-- A matrix-level conformal kernel transform preserves Hessian determinant
one exactly. -/
theorem conformalKernelTransform_preserves_det_one
    (mu : K)
    (D H : Matrix (Fin 4) (Fin 4) K)
    (hmu : mu ≠ 0)
    (hconformal : D.det ^ 2 = mu ^ 4)
    (hdet : H.det = 1) :
    (normalizedHessianCongruence mu D H).det = 1 := by
  exact
    normalizedHessianCongruence_det_one
      mu D H hmu hconformal hdet

/-! ## Terminal target contradiction -/

/-- **A positive kernel blow-up cannot land in a certified terminal
counterexample under JC2.**

If the concrete blow-up certificate reaches a polynomial `P` that is one
of the three already-formalised terminal endpoint families, the transported
distinct exact collision contradicts terminal gradient injectivity.

This is the exact terminal branch needed by the eventual global
`JC2ImpliesHC4` restart dispatcher. -/
theorem kernelBlowup_terminalTarget_impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {s t : HC4.Newton.GlobalRestartState}
    {slope : ℕ}
    {mu : K}
    {D : Matrix (Fin 4) (Fin 4) K}
    {F P : MvPolynomial (Fin 4) K}
    {p r : Fin 4 -> K}
    (hblow :
      KernelBlowupCertificate
        s t slope mu D F P p r)
    (hterminal :
      HC4.Newton.CertifiedTerminalEndpoint P) :
    False := by
  have hcoll := hblow.distinct_collision
  exact
    HC4.Newton.certifiedTerminalEndpoint_collision_impossible_of_JC2
      hJC2 hterminal hcoll.1 hcoll.2

end

end HC4.Valuation
