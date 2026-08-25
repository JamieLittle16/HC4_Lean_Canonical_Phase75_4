import HC4.Newton.FiniteSupportCrossFacetExposure
import Mathlib.Tactic

/-!
# A18.5.65d: cross-facet affine-line recognition

The exact cross-facet face from A18.5.65c inherits three affine equations:

* toric balance;
* the first-contact equation; and
* the secondary exposing-weight equation.

Choosing the secondary coordinate opposite the contact coordinate makes the
homogeneous difference system uniformly rank three.  There is therefore no
exceptional `a = b` branch to dispatch: after forming the cross-difference

    z = y_j x - x_j y,

the secondary equation kills the opposite coordinate of `z`, the contact
equation kills the sum of the two remaining coordinates, and toric balance
kills those two coordinates because their balance coefficients have opposite
signs.

The resulting theorem is stated directly on honest `MvPolynomial` support: all
support exponents of the cross-facet face lie on the affine line through the
certified facet and outside exponents.  In particular the contact coordinate
is injective on that support.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

/-- The canonical auxiliary coordinate opposite the contact coordinate. -/
def crossFacetOppositeCoordinate (j : Fin 4) : Fin 4 :=
  ⟨(j.1 + 2) % 4, Nat.mod_lt _ (by decide)⟩

/-- Pure integer kernel lemma behind the cross-facet line recognition.

The balance row is `(a,b,-b,-a)`.  The contact row has one common positive
scale plus an arbitrary bump in coordinate `j`.  The secondary row is supported
on `j` and the opposite coordinate.  Two solutions are therefore proportional
with proportionality measured by their `j` coordinates. -/
theorem crossFacetOpposite_rankOne_kernel
    {a b contactScale secondaryScale : ℕ}
    {contactBump secondaryBump : ℤ}
    {j : Fin 4}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (hsecondaryScale : 0 < secondaryScale)
    (x y : Fin 4 → ℤ)
    (hxBal :
      (a : ℤ) * x 0 + (b : ℤ) * x 1 =
        (b : ℤ) * x 2 + (a : ℤ) * x 3)
    (hyBal :
      (a : ℤ) * y 0 + (b : ℤ) * y 1 =
        (b : ℤ) * y 2 + (a : ℤ) * y 3)
    (hxContact :
      (contactScale : ℤ) * (x 0 + x 1 + x 2 + x 3) +
        contactBump * x j = 0)
    (hyContact :
      (contactScale : ℤ) * (y 0 + y 1 + y 2 + y 3) +
        contactBump * y j = 0)
    (hxSecondary :
      (secondaryScale : ℤ) * x (crossFacetOppositeCoordinate j) +
        secondaryBump * x j = 0)
    (hySecondary :
      (secondaryScale : ℤ) * y (crossFacetOppositeCoordinate j) +
        secondaryBump * y j = 0) :
    ∀ k : Fin 4, y j * x k = x j * y k := by
  let z : Fin 4 → ℤ := fun k => y j * x k - x j * y k

  have hzj : z j = 0 := by
    dsimp [z]
    ring

  have hzBal :
      (a : ℤ) * z 0 + (b : ℤ) * z 1 =
        (b : ℤ) * z 2 + (a : ℤ) * z 3 := by
    calc
      (a : ℤ) * z 0 + (b : ℤ) * z 1 =
          y j * ((a : ℤ) * x 0 + (b : ℤ) * x 1) -
            x j * ((a : ℤ) * y 0 + (b : ℤ) * y 1) := by
              dsimp [z]
              ring
      _ = y j * ((b : ℤ) * x 2 + (a : ℤ) * x 3) -
            x j * ((b : ℤ) * y 2 + (a : ℤ) * y 3) := by
              rw [hxBal, hyBal]
      _ = (b : ℤ) * z 2 + (a : ℤ) * z 3 := by
              dsimp [z]
              ring

  have hzContact :
      (contactScale : ℤ) * (z 0 + z 1 + z 2 + z 3) +
        contactBump * z j = 0 := by
    calc
      (contactScale : ℤ) * (z 0 + z 1 + z 2 + z 3) +
          contactBump * z j =
        y j *
            ((contactScale : ℤ) * (x 0 + x 1 + x 2 + x 3) +
              contactBump * x j) -
          x j *
            ((contactScale : ℤ) * (y 0 + y 1 + y 2 + y 3) +
              contactBump * y j) := by
                dsimp [z]
                ring
      _ = 0 := by rw [hxContact, hyContact]; ring

  have hzSecondary :
      (secondaryScale : ℤ) * z (crossFacetOppositeCoordinate j) +
        secondaryBump * z j = 0 := by
    calc
      (secondaryScale : ℤ) * z (crossFacetOppositeCoordinate j) +
          secondaryBump * z j =
        y j *
            ((secondaryScale : ℤ) * x (crossFacetOppositeCoordinate j) +
              secondaryBump * x j) -
          x j *
            ((secondaryScale : ℤ) * y (crossFacetOppositeCoordinate j) +
              secondaryBump * y j) := by
                dsimp [z]
                ring
      _ = 0 := by rw [hxSecondary, hySecondary]; ring

  have hcontactScaleZ : (0 : ℤ) < (contactScale : ℤ) := by
    exact_mod_cast hcontactScale
  have hsecondaryScaleZ : (0 : ℤ) < (secondaryScale : ℤ) := by
    exact_mod_cast hsecondaryScale
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hab_ne : (a : ℤ) + (b : ℤ) ≠ 0 := by
    nlinarith

  have hzi : z (crossFacetOppositeCoordinate j) = 0 := by
    have hmul :
        (secondaryScale : ℤ) * z (crossFacetOppositeCoordinate j) = 0 := by
      rw [hzj] at hzSecondary
      simpa using hzSecondary
    rcases mul_eq_zero.mp hmul with hscale | hz
    · exact (ne_of_gt hsecondaryScaleZ hscale).elim
    · exact hz

  have hzsum : z 0 + z 1 + z 2 + z 3 = 0 := by
    have hmul :
        (contactScale : ℤ) * (z 0 + z 1 + z 2 + z 3) = 0 := by
      rw [hzj] at hzContact
      simpa using hzContact
    rcases mul_eq_zero.mp hmul with hscale | hsum
    · exact (ne_of_gt hcontactScaleZ hscale).elim
    · exact hsum

  have hzall : ∀ k : Fin 4, z k = 0 := by
    fin_cases j
    · have hz0 : z 0 = 0 := hzj
      have hz2 : z 2 = 0 := by
        simpa [crossFacetOppositeCoordinate] using hzi
      have hprod : ((a : ℤ) + (b : ℤ)) * z 1 = 0 := by
        nlinarith [hzBal, hzsum]
      have hz1 : z 1 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hab_ne
      have hz3 : z 3 = 0 := by nlinarith [hzsum]
      intro k
      fin_cases k <;> assumption
    · have hz1 : z 1 = 0 := hzj
      have hz3 : z 3 = 0 := by
        simpa [crossFacetOppositeCoordinate] using hzi
      have hprod : ((a : ℤ) + (b : ℤ)) * z 0 = 0 := by
        nlinarith [hzBal, hzsum]
      have hz0 : z 0 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hab_ne
      have hz2 : z 2 = 0 := by nlinarith [hzsum]
      intro k
      fin_cases k <;> assumption
    · have hz2 : z 2 = 0 := hzj
      have hz0 : z 0 = 0 := by
        simpa [crossFacetOppositeCoordinate] using hzi
      have hprod : ((a : ℤ) + (b : ℤ)) * z 1 = 0 := by
        nlinarith [hzBal, hzsum]
      have hz1 : z 1 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hab_ne
      have hz3 : z 3 = 0 := by nlinarith [hzsum]
      intro k
      fin_cases k <;> assumption
    · have hz3 : z 3 = 0 := hzj
      have hz1 : z 1 = 0 := by
        simpa [crossFacetOppositeCoordinate] using hzi
      have hprod : ((a : ℤ) + (b : ℤ)) * z 0 = 0 := by
        nlinarith [hzBal, hzsum]
      have hz0 : z 0 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hab_ne
      have hz2 : z 2 = 0 := by nlinarith [hzsum]
      intro k
      fin_cases k <;> assumption

  intro k
  exact sub_eq_zero.mp (by simpa [z] using hzall k)

variable {K : Type*} [Field K] [CharZero K]

/-- Every supported exponent of an exact cross-facet face has the selected
secondary weight. -/
theorem CrossFacetInitialData.face_weight_eq
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    Finsupp.weight (crossFacetWeight i j D.scale D.bump) d = D.level := by
  have hhom := initialForm_isWeightedHomogeneous
    (crossFacetWeight i j D.scale D.bump) D.level F
  rw [D.face_eq] at hd
  exact hhom (MvPolynomial.mem_support_iff.mp hd)

/-- **Cross-facet affine-line recognition.**

If the carrier is torus-balanced and lies on one exact first-contact level,
then the canonical opposite-coordinate cross-facet face is genuinely
one-dimensional.  Every supported exponent is cross-proportional to the
certified facet-to-outside direction. -/
theorem CrossFacetInitialData.support_crossFacet_affine_proportional
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {j : Fin 4}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F (crossFacetOppositeCoordinate j) j)
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight j contactScale contactBump d = contactLevel) :
    ∀ d ∈ D.face.support, ∀ k : Fin 4,
      (((D.outsideExponent j : ℕ) : ℤ) -
          ((D.facetExponent j : ℕ) : ℤ)) *
          (((d k : ℕ) : ℤ) - ((D.facetExponent k : ℕ) : ℤ)) =
        (((d j : ℕ) : ℤ) - ((D.facetExponent j : ℕ) : ℤ)) *
          (((D.outsideExponent k : ℕ) : ℤ) -
            ((D.facetExponent k : ℕ) : ℤ)) := by
  intro d hd

  let v := D.facetExponent
  let o := D.outsideExponent
  let x : Fin 4 → ℤ := fun k => (d k : ℤ) - (v k : ℤ)
  let y : Fin 4 → ℤ := fun k => (o k : ℤ) - (v k : ℤ)

  have hdF : d ∈ F.support := D.support_subset hd

  have hdBal := hBal d hdF
  have hvBal := hBal v D.facet_mem
  have hoBal := hBal o D.outside_mem
  unfold IsBalancedExponent at hdBal hvBal hoBal

  have hdBalZ :
      (a : ℤ) * (d 0 : ℤ) + (b : ℤ) * (d 1 : ℤ) =
        (b : ℤ) * (d 2 : ℤ) + (a : ℤ) * (d 3 : ℤ) := by
    exact_mod_cast hdBal
  have hvBalZ :
      (a : ℤ) * (v 0 : ℤ) + (b : ℤ) * (v 1 : ℤ) =
        (b : ℤ) * (v 2 : ℤ) + (a : ℤ) * (v 3 : ℤ) := by
    exact_mod_cast hvBal
  have hoBalZ :
      (a : ℤ) * (o 0 : ℤ) + (b : ℤ) * (o 1 : ℤ) =
        (b : ℤ) * (o 2 : ℤ) + (a : ℤ) * (o 3 : ℤ) := by
    exact_mod_cast hoBal

  have hxBal :
      (a : ℤ) * x 0 + (b : ℤ) * x 1 =
        (b : ℤ) * x 2 + (a : ℤ) * x 3 := by
    dsimp [x, v]
    nlinarith [hdBalZ, hvBalZ]
  have hyBal :
      (a : ℤ) * y 0 + (b : ℤ) * y 1 =
        (b : ℤ) * y 2 + (a : ℤ) * y 3 := by
    dsimp [y, o, v]
    nlinarith [hoBalZ, hvBalZ]

  have hdContact := hcontact d hdF
  have hvContact := hcontact v D.facet_mem
  have hoContact := hcontact o D.outside_mem
  unfold scaledContactExponentWeight ordinaryDegree4 at
    hdContact hvContact hoContact
  push_cast at hdContact hvContact hoContact

  have hxContact :
      (contactScale : ℤ) * (x 0 + x 1 + x 2 + x 3) +
        (contactBump : ℤ) * x j = 0 := by
    dsimp [x, v]
    nlinarith [hdContact, hvContact]
  have hyContact :
      (contactScale : ℤ) * (y 0 + y 1 + y 2 + y 3) +
        (contactBump : ℤ) * y j = 0 := by
    dsimp [y, o, v]
    nlinarith [hoContact, hvContact]

  have hdSecondary := D.face_weight_eq hd
  have hvSecondary := D.face_weight_eq D.facet_mem_face
  have hoSecondary := D.face_weight_eq D.outside_mem_face
  rw [weight_crossFacetWeight] at hdSecondary hvSecondary hoSecondary

  have hxSecondary :
      (D.scale : ℤ) * x (crossFacetOppositeCoordinate j) +
        D.bump * x j = 0 := by
    dsimp [x, v]
    nlinarith [hdSecondary, hvSecondary]
  have hySecondary :
      (D.scale : ℤ) * y (crossFacetOppositeCoordinate j) +
        D.bump * y j = 0 := by
    dsimp [y, o, v]
    nlinarith [hoSecondary, hvSecondary]

  have hkernel := crossFacetOpposite_rankOne_kernel
    (a := a) (b := b)
    (contactScale := contactScale) (secondaryScale := D.scale)
    (contactBump := (contactBump : ℤ)) (secondaryBump := D.bump)
    (j := j)
    ha hb hcontactScale D.scale_pos x y
    hxBal hyBal hxContact hyContact hxSecondary hySecondary

  intro k
  simpa [x, y, v, o] using hkernel k

/-- The contact coordinate is injective on the recognised cross-facet support.
This is the exact finite-support fact needed to index the edge by a univariate
coefficient polynomial in the next adapter. -/
theorem CrossFacetInitialData.support_eq_of_contactCoordinate_eq
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {j : Fin 4}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F (crossFacetOppositeCoordinate j) j)
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight j contactScale contactBump d = contactLevel)
    {p q : Fin 4 →₀ ℕ}
    (hp : p ∈ D.face.support) (hq : q ∈ D.face.support)
    (hpqj : p j = q j) :
    p = q := by
  ext k
  have hpLine := D.support_crossFacet_affine_proportional
    ha hb hcontactScale hBal hcontact p hp k
  have hqLine := D.support_crossFacet_affine_proportional
    ha hb hcontactScale hBal hcontact q hq k
  have hdenPos :
      (0 : ℤ) <
        ((D.outsideExponent j : ℕ) : ℤ) -
          ((D.facetExponent j : ℕ) : ℤ) := by
    rw [D.facet_coordinate_zero]
    exact_mod_cast D.outside_coordinate_pos
  have hpqjZ : (p j : ℤ) = (q j : ℤ) := by exact_mod_cast hpqj
  have hmul :
      (((D.outsideExponent j : ℕ) : ℤ) -
          ((D.facetExponent j : ℕ) : ℤ)) *
        (((p k : ℕ) : ℤ) - ((q k : ℕ) : ℤ)) = 0 := by
    nlinarith [hpLine, hqLine]
  rcases mul_eq_zero.mp hmul with hden | hk
  · exact (ne_of_gt hdenPos hden).elim
  · exact_mod_cast (show (p k : ℤ) = (q k : ℤ) by linarith)

end

end HC4.Newton
