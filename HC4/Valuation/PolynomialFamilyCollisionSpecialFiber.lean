import HC4.Newton.RankOnePacketExactCollision
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# Exact gradient collision passes to a polynomial-family special fibre

This is the generic coefficient/specialisation lemma required by the
pointed Rees restart programme.

Represent a finite one-parameter family by

    P : MvPolynomial σ (Polynomial K),

where the coefficient-ring polynomial variable is the Rees parameter
`τ`.  A moving marked section is simply

    a : σ → Polynomial K.

The special fibre at `τ=0` is obtained by applying the coefficient ring
homomorphism `Polynomial.constantCoeff` to every coefficient of `P`.
Likewise, the reduction of a moving section is obtained by taking the
constant coefficient of every coordinate.

The key theorem proves:

    exact gradient collision over K[τ]
        ↓ constant coefficient
    exact gradient collision of the special fibre.

The proof uses only two functorial facts from Mathlib:

* partial derivatives commute with `MvPolynomial.map`;
* ring homomorphisms commute with multivariate evaluation.

Thus this lemma applies equally to the original Laurent pole clearing,
kernel blow-ups, and later Rees/Smith refinements.

The final theorem connects this directly to the green Phase 93.18 Smith
packet rigidity result.  To finish the RS1 collision inheritance globally,
one now only has to exhibit the actual Rees family whose special fibre is
the canonical symmetric Smith restriction and identify the reductions of
its two marked sections.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {σ K : Type*} [Field K]

/-- The `τ=0` special fibre of a polynomial-parameter multivariate family. -/
noncomputable def polynomialFamilySpecialFiber
    (P : MvPolynomial σ (Polynomial K)) :
    MvPolynomial σ K :=
  MvPolynomial.map Polynomial.constantCoeff P

/-- Reduction at `τ=0` of a polynomial moving section. -/
def polynomialSectionSpecialPoint
    (a : σ → Polynomial K) :
    σ → K :=
  fun i => Polynomial.constantCoeff (a i)

/-- Exact equality of all source-gradient components for two moving
sections of a polynomial-parameter family.  The Rees parameter is a
coefficient parameter, not a source variable, so only the `σ`-gradient is
used. -/
def HasPolynomialFamilyExactGradientCollision
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K) : Prop :=
  ∀ i : σ,
    MvPolynomial.eval a (MvPolynomial.pderiv i P) =
      MvPolynomial.eval b (MvPolynomial.pderiv i P)

/-- A constant source point regarded as a polynomial moving section. -/
def polynomialConstantSection
    (p : σ → K) :
    σ → Polynomial K :=
  fun i => Polynomial.C (p i)

@[simp] theorem polynomialSectionSpecialPoint_constantSection
    (p : σ → K) :
    polynomialSectionSpecialPoint
        (polynomialConstantSection p) = p := by
  funext i
  simp [polynomialSectionSpecialPoint, polynomialConstantSection]

/-- Evaluated source-gradient components commute with passage to the
`τ=0` special fibre. -/
theorem polynomialFamilySpecialFiber_gradientComponent
    (P : MvPolynomial σ (Polynomial K))
    (a : σ → Polynomial K)
    (i : σ) :
    mvGradientComponentAt
        (polynomialSectionSpecialPoint a)
        (polynomialFamilySpecialFiber P)
        i =
      Polynomial.constantCoeff
        (MvPolynomial.eval a
          (MvPolynomial.pderiv i P)) := by
  unfold mvGradientComponentAt
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.pderiv_map]
  rw [MvPolynomial.eval_map]
  exact
    (MvPolynomial.eval₂_comp
      Polynomial.constantCoeff
      a
      (MvPolynomial.pderiv i P)).symm

/-- **Exact collision inheritance under specialisation.**
An exact gradient collision between moving polynomial sections descends to
an exact gradient collision between their reductions on the special
fibre. -/
theorem polynomialFamilyExactGradientCollision_specialFiber
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P a b) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber P)
      (polynomialSectionSpecialPoint a)
      (polynomialSectionSpecialPoint b) := by
  intro i
  rw [polynomialFamilySpecialFiber_gradientComponent
        P a i]
  rw [polynomialFamilySpecialFiber_gradientComponent
        P b i]
  exact
    congrArg Polynomial.constantCoeff
      (hcoll i)

/-- If both moving sections have zero family-gradient, their reductions
have zero special-fibre gradient. -/
theorem polynomialFamilyGradientZero_specialFiber
    (P : MvPolynomial σ (Polynomial K))
    (a : σ → Polynomial K)
    (hzero :
      ∀ i : σ,
        MvPolynomial.eval a
          (MvPolynomial.pderiv i P) = 0) :
    ∀ i : σ,
      mvGradientComponentAt
        (polynomialSectionSpecialPoint a)
        (polynomialFamilySpecialFiber P)
        i = 0 := by
  intro i
  rw [polynomialFamilySpecialFiber_gradientComponent
        P a i]
  rw [hzero i]
  simp

/-- A convenient exact-collision form when the first marked section is
identically zero. -/
theorem polynomialFamilyZeroCollision_specialFiber
    (P : MvPolynomial σ (Polynomial K))
    (b : σ → Polynomial K)
    (hzero :
      ∀ i : σ,
        MvPolynomial.eval
          (fun _ => (0 : Polynomial K))
          (MvPolynomial.pderiv i P) =
        MvPolynomial.eval b
          (MvPolynomial.pderiv i P)) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber P)
      (fun _ => (0 : K))
      (polynomialSectionSpecialPoint b) := by
  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (fun _ => (0 : Polynomial K))
        b :=
    hzero
  have hs :=
    polynomialFamilyExactGradientCollision_specialFiber
      P
      (fun _ => (0 : Polynomial K))
      b hcoll
  simpa [polynomialSectionSpecialPoint] using hs

/-- **RS1 special-fibre adapter.**
If the canonical symmetric Smith restriction is realised as the special
fibre of a polynomial Rees family carrying an exact marked collision, and
the two marked sections reduce to the origin and a nonzero normalised
transverse point, then the packet is rigid.

All Smith/pole-minimal algebra is already discharged by Phases 93.11--93.18;
the only new hypotheses here describe the genuine Rees-family realisation
and its marked sections. -/
theorem poleMinimal_symmetricSmithRestriction_rigid_of_familySpecialFiber
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base)
    (hnoW :
      ∀ e ∈ S,
        base e = m ->
          ¬ IsWLinearSmithPattern e)
    (hreal :
      IsSmithSubfaceRealisedInPolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (P : MvPolynomial σ (Polynomial K))
    (a b : σ → Polynomial K)
    (hfamily :
      HasPolynomialFamilyExactGradientCollision P a b)
    (hspecial :
      polynomialFamilySpecialFiber P =
        smithSubfacePolynomial
          y z w
          (smithSymmetricBalancedSubface S m base)
          F)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        rankOnePacketTransversePoint x y z Y Z) :
    HasRigidRankOnePacket
      x y z D
      (smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F) := by
  have hcoll :=
    polynomialFamilyExactGradientCollision_specialFiber
      P a b hfamily
  rw [hspecial, ha, hb] at hcoll
  exact
    poleMinimal_symmetricSmithRestriction_rigid_of_exactCollision
      x y z w
      hxy hxz hxw hyz hyw hzw
      hchart hhom hD
      S m base
      hpole hmin hattain hshape hnoW hreal
      Y Z hpoint hcoll

end

end HC4.Valuation
