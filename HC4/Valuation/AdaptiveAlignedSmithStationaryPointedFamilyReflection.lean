import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockAssemblyFrontier
import HC4.Valuation.AdaptiveAlignedSmithMixedDegreePointedReflection
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Family-level pointed reflection of the stationary aligned-Smith blocker

The static mixed-degree reflection theorem deliberately stopped before
claiming any covariance for the actual polynomial family.  This file closes
that gap.

Let

    P : K[τ][X₀,...,X₃]

carry the exact moving collision `0 ~ b(τ)`, with `b(0)=e₀`.  Translate by
`b` and then negate every source coordinate.  The resulting family is

    P♯(X) = P(b(τ) - X).

This is the genuine family-level pointed reflection.  It has four decisive
properties:

* the same pure Hessian determinant clock;
* the same nonlinear source-degree cap;
* the same *ordered* moving collision `0 ~ b(τ)`;
* special fibre `P₀(e₀-X)`, which is still mixed in ordinary source degree.

The last point is important.  The full reflection differs from the earlier
static `x₀ ↦ 1-x₀` reflection only by signs in the transverse variables, and
linear sign substitutions preserve every ordinary homogeneous degree.

No Rees exposure, terminal classification, or JC2 hypothesis is used.  The
purpose of this module is to ensure that any subsequent degree-adaptive
purification is performed on an honest collision-carrying HC4 family rather
than on an isolated special-fibre polynomial.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

/-! ## Simultaneous source negation -/

variable {R : Type u} [CommRing R]

/-- Simultaneous linear sign change in all four source coordinates. -/
noncomputable def allSourceSignHom :
    MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin 4 => -MvPolynomial.X i)

@[simp]
theorem allSourceSignHom_C (c : R) :
    allSourceSignHom (R := R) (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [allSourceSignHom]

@[simp]
theorem allSourceSignHom_X (i : Fin 4) :
    allSourceSignHom (R := R) (MvPolynomial.X i) = -MvPolynomial.X i := by
  simp [allSourceSignHom]

/-- Simultaneous source negation is an involution. -/
theorem allSourceSignHom_involutive
    (F : MvPolynomial (Fin 4) R) :
    allSourceSignHom (R := R) (allSourceSignHom (R := R) F) = F := by
  let φ : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) R :=
    (allSourceSignHom (R := R)).comp (allSourceSignHom (R := R))
  have hφ : φ = RingHom.id (MvPolynomial (Fin 4) R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ, allSourceSignHom]
    · intro i
      simp [φ, allSourceSignHom]
  change φ F = F
  rw [hφ]
  rfl

/-- Linear sign substitution preserves every ordinary homogeneous degree. -/
theorem allSourceSignHom_isHomogeneous
    {F : MvPolynomial (Fin 4) R}
    {D : ℕ}
    (hF : F.IsHomogeneous D) :
    (allSourceSignHom (R := R) F).IsHomogeneous D := by
  have h :=
    hF.eval₂
      MvPolynomial.C
      (fun i : Fin 4 => -MvPolynomial.X i)
      (by
        intro r
        exact MvPolynomial.isHomogeneous_C (Fin 4) r)
      (by
        intro i
        exact (MvPolynomial.isHomogeneous_X R i).neg)
  simpa [allSourceSignHom] using h

/-- Evaluation of a sign-pulled polynomial at the negated point is the old
evaluation. -/
theorem eval_allSourceSignHom_neg
    (a : Fin 4 → R)
    (F : MvPolynomial (Fin 4) R) :
    MvPolynomial.eval (fun i => -a i)
        (allSourceSignHom (R := R) F) =
      MvPolynomial.eval a F := by
  change
    MvPolynomial.eval (fun i => -a i)
        (MvPolynomial.eval₂ MvPolynomial.C
          (fun i : Fin 4 => -MvPolynomial.X i) F) =
      MvPolynomial.eval a F
  rw [← MvPolynomial.eval_assoc
    (fun i : Fin 4 => -MvPolynomial.X i)
    (fun i => -a i) F]
  apply congrArg (fun x => MvPolynomial.eval x F)
  funext i
  simp

/-- One source derivative of the simultaneous sign pullback contributes one
minus sign. -/
theorem pderiv_allSourceSignHom
    (i : Fin 4)
    (F : MvPolynomial (Fin 4) R) :
    MvPolynomial.pderiv i (allSourceSignHom (R := R) F) =
      - allSourceSignHom (R := R) (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
    ring
  · intro p n hp
    simp only [map_mul, allSourceSignHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hni : n = i
    · subst n
      simp
      ring
    · simp [hni]

/-- Two source derivatives cancel the two sign factors. -/
theorem hessian_allSourceSignHom_entry
    (F : MvPolynomial (Fin 4) R)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (allSourceSignHom (R := R) F) i j =
      allSourceSignHom (R := R) (HC4.Polynomial.hessian F i j) := by
  simp [HC4.Polynomial.hessian_apply, pderiv_allSourceSignHom]

/-- Matrix form of Hessian covariance under simultaneous sign change. -/
theorem hessian_allSourceSignHom
    (F : MvPolynomial (Fin 4) R) :
    HC4.Polynomial.hessian (allSourceSignHom (R := R) F) =
      (allSourceSignHom (R := R)).mapMatrix (HC4.Polynomial.hessian F) := by
  apply Matrix.ext
  intro i j
  exact hessian_allSourceSignHom_entry F i j

/-- Hessian determinant is exactly functorial under simultaneous sign change. -/
theorem hessianDeterminant_allSourceSignHom
    (F : MvPolynomial (Fin 4) R) :
    HC4.Polynomial.hessianDeterminant (allSourceSignHom (R := R) F) =
      allSourceSignHom (R := R) (HC4.Polynomial.hessianDeterminant F) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_allSourceSignHom]
  exact
    (RingHom.map_det
      (allSourceSignHom (R := R))
      (HC4.Polynomial.hessian F)).symm

/-! ## Polynomial-family covariance -/

variable {K : Type*} [Field K]

/-- Coordinatewise negation of a polynomial moving section. -/
def polynomialSectionNegation
    (a : Fin 4 → Polynomial K) : Fin 4 → Polynomial K :=
  fun i => -a i

@[simp]
theorem polynomialSectionNegation_zero :
    polynomialSectionNegation (K := K) (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  simp [polynomialSectionNegation, zeroPolynomialSection]

@[simp]
theorem polynomialSectionNegation_neg
    (a : Fin 4 → Polynomial K) :
    polynomialSectionNegation (K := K) (fun i => -a i) = a := by
  funext i
  simp [polynomialSectionNegation]

/-- Simultaneous source negation preserves a pure polynomial-family Hessian
clock. -/
theorem allSourceSignHom_preservesHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K) (allSourceSignHom (R := Polynomial K) P) Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_allSourceSignHom]
  rw [hdef]
  simp

/-- Exact family-gradient collisions are transported by simultaneous source
negation. -/
theorem polynomialFamilyExactGradientCollision_allSourceSign
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (allSourceSignHom (R := Polynomial K) P)
      (polynomialSectionNegation (K := K) a)
      (polynomialSectionNegation (K := K) b) := by
  intro i
  calc
    MvPolynomial.eval (polynomialSectionNegation (K := K) a)
        (MvPolynomial.pderiv i (allSourceSignHom (R := Polynomial K) P)) =
      - MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
        rw [pderiv_allSourceSignHom]
        simp only [map_neg]
        exact congrArg Neg.neg (by
          simpa [polynomialSectionNegation] using
            (eval_allSourceSignHom_neg
              (R := Polynomial K) a (MvPolynomial.pderiv i P)))
    _ = - MvPolynomial.eval b (MvPolynomial.pderiv i P) :=
      congrArg Neg.neg (hcoll i)
    _ = MvPolynomial.eval (polynomialSectionNegation (K := K) b)
        (MvPolynomial.pderiv i (allSourceSignHom (R := Polynomial K) P)) := by
        rw [pderiv_allSourceSignHom]
        simp only [map_neg]
        exact (congrArg Neg.neg (by
          simpa [polynomialSectionNegation] using
            (eval_allSourceSignHom_neg
              (R := Polynomial K) b (MvPolynomial.pderiv i P)))).symm

/-- Simultaneous source negation preserves every nonlinear degree ceiling. -/
theorem nonlinearDegreeBound_allSourceSignHom
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (allSourceSignHom (R := Polynomial K) P) := by
  apply nonlinearDegreeBound_map_of_monomial_homogeneous
    (allSourceSignHom (R := Polynomial K)) P m hP
  intro n c
  have hhom :
      (MvPolynomial.monomial n c).IsHomogeneous n.degree :=
    MvPolynomial.isHomogeneous_monomial c rfl
  exact allSourceSignHom_isHomogeneous hhom

/-- Passing to the parameter special fibre commutes with simultaneous source
negation. -/
theorem polynomialFamilySpecialFiber_allSourceSignHom
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber
        (allSourceSignHom (R := Polynomial K) P) =
      allSourceSignHom (R := K) (polynomialFamilySpecialFiber P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [polynomialFamilySpecialFiber]
  · intro p q hp hq
    simpa [polynomialFamilySpecialFiber] using
      congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    have hvar :
        polynomialFamilySpecialFiber
            (allSourceSignHom (R := Polynomial K) (MvPolynomial.X i)) =
          allSourceSignHom (R := K)
            (polynomialFamilySpecialFiber (MvPolynomial.X i)) := by
      simp [polynomialFamilySpecialFiber]
    have hmul := congrArg₂ (fun x y => x * y) hp hvar
    simpa [polynomialFamilySpecialFiber, map_mul] using hmul

/-! ## The honest pointed reflection family -/

/-- Family-level pointed reflection about the actual moving marked section:

`P♯(X) = P(b(τ) - X)`.

It is implemented as translation by `b`, followed by simultaneous source
negation. -/
noncomputable def polynomialFamilyPointedReflection
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  allSourceSignHom (R := Polynomial K)
    (polynomialFamilyTranslationHom (K := K) b P)

/-- The full static pointed reflection `F(X) ↦ F(e₀-X)`.  This is the special
fibre of `polynomialFamilyPointedReflection` when `b(0)=e₀`. -/
noncomputable def fullPointedLongitudinalReflectionHom
    (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  allSourceSignHom (R := K)
    (longitudinalRightRecenterHom (K := K) F)

/-- The family-level pointed reflection preserves the exact Hessian clock. -/
theorem polynomialFamilyPointedReflection_preservesHessianDefect
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K) (polynomialFamilyPointedReflection (K := K) b P) Delta := by
  unfold polynomialFamilyPointedReflection
  exact allSourceSignHom_preservesHessianDefect
    (polynomialFamilyTranslationHom (K := K) b P)
    (polynomialFamilyTranslationHom_preservesHessianDefect b P hdef)

/-- The family-level pointed reflection preserves every nonlinear source-degree
ceiling. -/
theorem nonlinearDegreeBound_polynomialFamilyPointedReflection
    (m : ℕ)
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (polynomialFamilyPointedReflection (K := K) b P) := by
  unfold polynomialFamilyPointedReflection
  exact nonlinearDegreeBound_allSourceSignHom m
    (polynomialFamilyTranslationHom (K := K) b P)
    (nonlinearDegreeBound_polynomialFamilyTranslationHom m b P hP)

/-- If `P` carries the ordered collision `0 ~ b`, reflection about `b`
returns the *same ordered collision* `0 ~ b`. -/
theorem polynomialFamilyPointedReflection_exactCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision
      P (zeroPolynomialSection (K := K)) b) :
    HasPolynomialFamilyExactGradientCollision
      (polynomialFamilyPointedReflection (K := K) b P)
      (zeroPolynomialSection (K := K)) b := by
  have hswap :
      HasPolynomialFamilyExactGradientCollision
        P b (zeroPolynomialSection (K := K)) := by
    intro i
    exact (hcoll i).symm
  have hrec :=
    polynomialFamilyExactGradientCollision_recenter
      (K := K) P b (zeroPolynomialSection (K := K)) hswap
  have hsign :=
    polynomialFamilyExactGradientCollision_allSourceSign
      (K := K)
      (polynomialFamilyTranslationHom (K := K) b P)
      (zeroPolynomialSection (K := K))
      (polynomialSectionDifference b (zeroPolynomialSection (K := K)))
      hrec
  have hzero :
      polynomialSectionNegation (K := K)
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) :=
    polynomialSectionNegation_zero (K := K)
  have hsection :
      polynomialSectionNegation (K := K)
          (polynomialSectionDifference b (zeroPolynomialSection (K := K))) = b := by
    funext i
    simp [polynomialSectionNegation, polynomialSectionDifference,
      zeroPolynomialSection]
  rw [hzero, hsection] at hsign
  simpa [polynomialFamilyPointedReflection] using hsign

/-- At `τ=0`, the honest family reflection is exactly `F₀(e₀-X)`. -/
theorem polynomialFamilyPointedReflection_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hb : polynomialSectionSpecialPoint b =
      coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialFamilySpecialFiber
        (polynomialFamilyPointedReflection (K := K) b P) =
      fullPointedLongitudinalReflectionHom
        (K := K) (polynomialFamilySpecialFiber P) := by
  unfold polynomialFamilyPointedReflection
  rw [polynomialFamilySpecialFiber_allSourceSignHom]
  rw [polynomialFamilySpecialFiber_translation_eq_longitudinalRightRecenter
    (K := K) b hb P]
  rfl

/-- The full pointed reflection is mixed in ordinary degree whenever the
right-recentered polynomial is. -/
theorem fullPointedLongitudinalReflection_not_isHomogeneous
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hrec : ¬ (longitudinalRightRecenterHom (K := K) F).IsHomogeneous D) :
    ¬ (fullPointedLongitudinalReflectionHom (K := K) F).IsHomogeneous D := by
  intro hreflect
  have hback :
      (allSourceSignHom (R := K)
        (fullPointedLongitudinalReflectionHom (K := K) F)).IsHomogeneous D :=
    allSourceSignHom_isHomogeneous hreflect
  unfold fullPointedLongitudinalReflectionHom at hback
  rw [allSourceSignHom_involutive] at hback
  exact hrec hback

/-! ## Stationary-blocker package -/

/-- Honest family data supplied by pointed reflection of a canonical
stationary blocker.  This is the family-level object that the degree-adaptive
purification step may use without reconstructing covariance. -/
structure AdaptiveAlignedSmithStationaryPointedReflectionData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  family : MvPolynomial (Fin 4) (Polynomial K)
  family_eq :
    family = polynomialFamilyPointedReflection
      (K := K) stationary.blocker.aligned.endpoint.movingSection
      stationary.blocker.aligned.endpoint.family
  movingSection : Fin 4 → Polynomial K
  movingSection_eq :
    movingSection = stationary.blocker.aligned.endpoint.movingSection
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) family stationary.blocker.aligned.endpoint.defect
  nonlinearDegreeBound : NonlinearDegreeBound s.degreeCap family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (zeroPolynomialSection (K := K)) movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  specialFiber_eq :
    polynomialFamilySpecialFiber family =
      fullPointedLongitudinalReflectionHom
        (K := K) stationary.blocker.aligned.endpoint.rawSpecialFiber
  specialFiber_not_isHomogeneous :
    ∀ D : ℕ, ¬ (polynomialFamilySpecialFiber family).IsHomogeneous D

/-- Every scale-sound stationary blocker has an honest collision-preserving,
clock-preserving pointed reflection family whose special fibre remains
mixed-degree. -/
theorem AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker.pointedReflectionData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    Nonempty (AdaptiveAlignedSmithStationaryPointedReflectionData s) := by
  let E := S.blocker.aligned.endpoint
  let Psharp := polynomialFamilyPointedReflection
    (K := K) E.movingSection E.family
  have hspecial :
      polynomialFamilySpecialFiber Psharp =
        fullPointedLongitudinalReflectionHom (K := K) E.rawSpecialFiber := by
    simpa [Psharp, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
      (polynomialFamilyPointedReflection_specialFiber
        (K := K) E.family E.movingSection E.sectionSpecial)
  have hmixed :
      ∀ D : ℕ, ¬ (polynomialFamilySpecialFiber Psharp).IsHomogeneous D := by
    intro D
    rw [hspecial]
    have hrec := S.mixed.recentered_not_isHomogeneous D
    rw [S.mixed_eq] at hrec
    exact fullPointedLongitudinalReflection_not_isHomogeneous
      (K := K) E.rawSpecialFiber D (by simpa [E] using hrec)
  exact ⟨{
    stationary := S
    family := Psharp
    family_eq := rfl
    movingSection := E.movingSection
    movingSection_eq := rfl
    hessianDefect := by
      dsimp [Psharp]
      exact polynomialFamilyPointedReflection_preservesHessianDefect
        (K := K) E.movingSection E.family E.hessianDefect
    nonlinearDegreeBound := by
      dsimp [Psharp]
      exact nonlinearDegreeBound_polynomialFamilyPointedReflection
        (K := K) s.degreeCap E.movingSection E.family E.nonlinearDegreeBound
    exactCollision := by
      dsimp [Psharp]
      exact polynomialFamilyPointedReflection_exactCollision
        (K := K) E.family E.movingSection E.exactCollision
    sectionSpecial := E.sectionSpecial
    specialFiber_eq := hspecial
    specialFiber_not_isHomogeneous := hmixed
  }⟩

end

end HC4.Valuation
