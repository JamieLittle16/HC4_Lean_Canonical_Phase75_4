import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import HC4.Valuation.KernelBlowupCertificate
import Mathlib.Tactic

/-!
# Polynomial-family kernel restart

`PolynomialFamilyCollisionSpecialFiber` already proves that an exact
gradient collision carried by a polynomial family over `K[τ]` survives on
the special fibre `τ = 0`.

`GlobalRestartClassification` already proves that a positive kernel-slope
defect drop is a strict global restart.

This file joins those two green mechanisms.

A concrete Rees/kernel family therefore only has to provide:

* an exact family gradient collision between its two moving sections;
* distinct reductions of those sections on the special fibre;
* the positive determinant-defect update.

From these data Lean obtains, in one theorem:

* distinct marked points on the special fibre;
* an exact gradient collision on the special fibre;
* strict defect decrease;
* `GlobalRestartProgress`.

A pointed normalised form is also supplied for the common situation where
the first moving section reduces to the origin and the second reduces to a
specified nonzero point.

Finally, if the special fibre is already one of the certified terminal
endpoint families, JC2 gives an immediate contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {σ K : Type*} [Field K]

/-- Concrete special-fibre restart data for a polynomial-parameter family.

Unlike `KernelBlowupCertificate`, this interface does not ask for a
matrix-level covariance formula.  It uses the already-proved family
collision directly and then specialises to `τ = 0`.  This is the natural
interface for Rees families and kernel-blow-up families represented in
`MvPolynomial σ (Polynomial K)`. -/
structure PolynomialFamilyKernelRestartCertificate
    (s t : GlobalRestartState)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K) : Prop where
  familyCollision :
    HasPolynomialFamilyExactGradientCollision P a b
  specialPointsDistinct :
    polynomialSectionSpecialPoint a ≠
      polynomialSectionSpecialPoint b
  positiveDefectDrop :
    HasPositiveKernelDefectDrop slope s t

/-- The family certificate gives the distinct exact collision on the
special fibre. -/
theorem PolynomialFamilyKernelRestartCertificate.distinct_collision
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    (h :
      PolynomialFamilyKernelRestartCertificate
        s t slope P a b) :
    polynomialSectionSpecialPoint a ≠
        polynomialSectionSpecialPoint b ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber P)
        (polynomialSectionSpecialPoint a)
        (polynomialSectionSpecialPoint b) := by
  exact
    ⟨h.specialPointsDistinct,
      polynomialFamilyExactGradientCollision_specialFiber
        P a b h.familyCollision⟩

/-- The family certificate gives strict determinant-defect descent. -/
theorem PolynomialFamilyKernelRestartCertificate.defect_lt
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    (h :
      PolynomialFamilyKernelRestartCertificate
        s t slope P a b) :
    t.defect < s.defect := by
  exact
    positiveKernelDefectDrop_defect_lt
      h.positiveDefectDrop

/-- The family certificate gives a genuine global restart step. -/
theorem PolynomialFamilyKernelRestartCertificate.globalProgress
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    (h :
      PolynomialFamilyKernelRestartCertificate
        s t slope P a b) :
    GlobalRestartProgress s t := by
  exact
    globalRestartProgress_of_positiveKernelDefectDrop
      h.positiveDefectDrop

/-- **Complete polynomial-family restart package.**

Exact family collision plus distinct special points plus positive defect
drop is enough to obtain every logical consequence needed by the global
restart dispatcher. -/
theorem polynomialFamilyKernelRestart_preservesCollision_and_strictlyRestarts
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    (h :
      PolynomialFamilyKernelRestartCertificate
        s t slope P a b) :
    polynomialSectionSpecialPoint a ≠
        polynomialSectionSpecialPoint b ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber P)
        (polynomialSectionSpecialPoint a)
        (polynomialSectionSpecialPoint b) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  have hcoll := h.distinct_collision
  exact
    ⟨hcoll.1, hcoll.2,
      h.defect_lt, h.globalProgress⟩

/-! ## Pointed normalised family interface -/

/-- Pointed family restart data when the reductions of the marked moving
sections have already been identified with the origin and a specified
nonzero point.

This is the normal form expected after collision normalisation in the DVR
restart. -/
structure PointedPolynomialFamilyKernelRestartCertificate
    (s t : GlobalRestartState)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K)
    (r : σ → K) : Prop where
  familyCollision :
    HasPolynomialFamilyExactGradientCollision P a b
  firstSpecialPoint :
    polynomialSectionSpecialPoint a =
      fun _ => (0 : K)
  secondSpecialPoint :
    polynomialSectionSpecialPoint b = r
  secondPointNonzero :
    r ≠ fun _ => (0 : K)
  positiveDefectDrop :
    HasPositiveKernelDefectDrop slope s t

/-- The pointed certificate automatically implies distinct reductions. -/
theorem PointedPolynomialFamilyKernelRestartCertificate.specialPointsDistinct
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    {r : σ → K}
    (h :
      PointedPolynomialFamilyKernelRestartCertificate
        s t slope P a b r) :
    polynomialSectionSpecialPoint a ≠
      polynomialSectionSpecialPoint b := by
  rw [h.firstSpecialPoint, h.secondSpecialPoint]
  intro hz
  exact h.secondPointNonzero hz.symm

/-- Forget the pointed normalisation and obtain the generic family restart
certificate. -/
theorem PointedPolynomialFamilyKernelRestartCertificate.toKernelRestartCertificate
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    {r : σ → K}
    (h :
      PointedPolynomialFamilyKernelRestartCertificate
        s t slope P a b r) :
    PolynomialFamilyKernelRestartCertificate
      s t slope P a b := by
  exact
    { familyCollision := h.familyCollision
      specialPointsDistinct := h.specialPointsDistinct
      positiveDefectDrop := h.positiveDefectDrop }

/-- **Pointed special-fibre collision and strict restart.**

The special fibre has a distinct exact collision from the origin to `r`,
and the global determinant defect strictly decreases. -/
theorem pointedPolynomialFamilyKernelRestart_zeroCollision_and_strictlyRestarts
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial σ (Polynomial K)}
    {a b : σ → Polynomial K}
    {r : σ → K}
    (h :
      PointedPolynomialFamilyKernelRestartCertificate
        s t slope P a b r) :
    r ≠ (fun _ => (0 : K)) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber P)
        (fun _ => (0 : K))
        r ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  have hgeneric :=
    polynomialFamilyKernelRestart_preservesCollision_and_strictlyRestarts
      h.toKernelRestartCertificate
  rw [h.firstSpecialPoint, h.secondSpecialPoint] at hgeneric
  exact
    ⟨h.secondPointNonzero,
      hgeneric.2.1,
      hgeneric.2.2.1,
      hgeneric.2.2.2⟩

/-! ## Terminal special fibre -/

section Terminal

variable [CharZero K]

/-- **A pointed polynomial-family kernel restart cannot terminate in a
certified endpoint under JC2.**

The family collision specialises to a distinct exact collision on the
terminal special fibre, contradicting the unified endpoint injectivity
theorem from Phase 93.47. -/
theorem pointedPolynomialFamilyKernelRestart_terminalSpecialFiber_impossible_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {s t : GlobalRestartState}
    {slope : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {a b : Fin 4 → Polynomial K}
    {r : Fin 4 → K}
    (h :
      PointedPolynomialFamilyKernelRestartCertificate
        s t slope P a b r)
    (hterminal :
      CertifiedTerminalEndpoint
        (polynomialFamilySpecialFiber P)) :
    False := by
  have hrestart :=
    pointedPolynomialFamilyKernelRestart_zeroCollision_and_strictlyRestarts
      h
  exact
    certifiedTerminalEndpoint_collision_impossible_of_JC2
      hJC2 hterminal
      (by
        intro hr
        exact h.secondPointNonzero hr.symm)
      hrestart.2.1

end Terminal

end

end HC4.Valuation
