import HC4.Newton.FiniteSupportExposedVertex
import HC4.Newton.FiniteSupportCrossFacetExposure
import HC4.Newton.InteriorVertex
import Mathlib.Tactic

/-!
# A19.68: expose a singular boundary vertex with a prescribed positive coordinate

The balance-free zero-Hessian endgame often starts with a singular nonlinear
carrier which is known to contain actual support on both sides of one
coordinate facet.  The generic exposed-vertex theorem chooses an arbitrary
vertex and can therefore fall back onto the original facet.

For a finite support we can force the exposed vertex to stay outside that
facet.  First maximize the chosen coordinate `j`.  Since some supported
exponent has positive `j`-coordinate, this attained maximum is positive.
Then maximize coordinates `0,1,2,3` successively inside that exact face.
The final face is a singleton monomial, still with positive `j`-coordinate.
Hessian singularity passes through every exact maximal initial form, and the
interior-vertex theorem therefore puts the final exponent on a coordinate
boundary.

No torus balance or convex-polytope library is used.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Prescribed-positive exposed boundary vertex.**

A Hessian-singular polynomial whose complete support is nonlinear and which
contains a monomial with positive coordinate `j` contains an actual nonlinear
boundary exponent with that same coordinate positive. -/
theorem exists_nonlinear_boundary_exponent_with_coordinate_pos
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d)
    (hout : (positiveCoordinateSupport j F).Nonempty) :
    ∃ d ∈ F.support,
      3 ≤ ordinaryDegree4 d ∧
      0 < d j ∧
      MvExponentOnBoundary d := by
  classical
  rcases hout with ⟨q, hqPos⟩
  have hq := mem_positiveCoordinateSupport.mp hqPos
  have hFne : F ≠ 0 :=
    MvPolynomial.support_nonempty.mp ⟨q, hq.1⟩

  let Dj := coordinateMaxInitialData F hFne j
  have hjLevelPos : 0 < Dj.level := by
    exact lt_of_lt_of_le hq.2 (Dj.maximal q hq.1)
  have hjZero : hessianDeterminant Dj.face = 0 :=
    Dj.hessian_zero hzero

  let D0 := coordinateMaxInitialData Dj.face Dj.face_ne_zero (0 : Fin 4)
  have h0Zero : hessianDeterminant D0.face = 0 :=
    D0.hessian_zero hjZero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1Zero : hessianDeterminant D1.face = 0 :=
    D1.hessian_zero h0Zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2Zero : hessianDeterminant D2.face = 0 :=
    D2.hessian_zero h1Zero
  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  let d := D3.witness
  let c := MvPolynomial.coeff d D3.face

  have hd2 : d ∈ D2.face.support := D3.witness_mem
  have hd1 : d ∈ D1.face.support := D2.support_subset hd2
  have hd0 : d ∈ D0.face.support := D1.support_subset hd1
  have hdj : d ∈ Dj.face.support := D0.support_subset hd0
  have hdF : d ∈ F.support := Dj.support_subset hdj

  have hdjEq : d j = Dj.level := Dj.coordinate_eq d hdj
  have hdjPos : 0 < d j := by
    rw [hdjEq]
    exact hjLevelPos
  have hdDeg : 3 ≤ ordinaryDegree4 d := hnonlinear d hdF

  have hc : c ≠ 0 := by
    dsimp [c]
    have hcoeff :
        MvPolynomial.coeff d D3.face =
          MvPolynomial.coeff d D2.face := by
      rw [D3.face_eq, coeff_initialForm, weight_coordinateMaxWeight]
      have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simp [hd3]
    rw [hcoeff]
    exact MvPolynomial.mem_support_iff.mp D3.witness_mem

  have hunique : ∀ r ∈ D3.face.support, r = d := by
    intro r hr
    have hr2 : r ∈ D2.face.support := D3.support_subset hr
    have hr1 : r ∈ D1.face.support := D2.support_subset hr2
    have hr0 : r ∈ D0.face.support := D1.support_subset hr1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using
        (D0.coordinate_eq r hr0).trans (D0.coordinate_eq d hd0).symm
    · simpa using
        (D1.coordinate_eq r hr1).trans (D1.coordinate_eq d hd1).symm
    · simpa using
        (D2.coordinate_eq r hr2).trans (D2.coordinate_eq d hd2).symm
    · have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simpa using (D3.coordinate_eq r hr).trans hd3.symm

  have hmono : D3.face = MvPolynomial.monomial d c := by
    apply MvPolynomial.ext
    intro r
    by_cases hrd : r = d
    · subst r
      simp [c]
    · have hr0 : MvPolynomial.coeff r D3.face = 0 := by
        by_contra hne
        have hrs : r ∈ D3.face.support := MvPolynomial.mem_support_iff.mpr hne
        exact hrd (hunique r hrs)
      have hdr : d ≠ r := by
        intro hdr
        exact hrd hdr.symm
      rw [hr0]
      simp [hdr]

  have hinit :
      initialForm (coordinateMaxWeight (3 : Fin 4)) (D3.level : ℤ) D2.face =
        MvPolynomial.monomial d c := by
    rw [← D3.face_eq]
    exact hmono

  have hboundary : MvExponentOnBoundary d :=
    exposed_monomial_on_boundary_of_zero_hessian
      D3.weight_bound h2Zero hinit hc hdDeg

  exact ⟨d, hdF, hdDeg, hdjPos, hboundary⟩

end

end HC4.Newton
