import HC4.Newton.FiniteSupportExposedVertex
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# A18.5.92: balance-free singular nonlinear boundary vertex

The terminal first-contact carrier is genuinely Hessian-singular, but an
unrestricted HC4 proof cannot assume a torus grading merely to enter the
boundary-stratum machinery.

Finite support already gives a grading-free substitute.  Successively maximize
all four source coordinates.  Hessian singularity passes through every maximal
initial form, and after the fourth maximum the exposed face is a single
monomial.  The monomial Hessian formula then says that a nonlinear singular
monomial cannot involve all four variables in characteristic zero.  Hence the
exposed exponent lies on an actual coordinate boundary.

No balanced-support, torus, or JC2 hypothesis occurs in this file.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A balance-free exposed vertex carried by a singular nonlinear polynomial.
The carrier is a genuine iterated maximal initial form of the source, and its
last coordinate-max face is literally the displayed monomial. -/
structure ExposedSingularNonlinearBoundaryVertexData
    (F : MvPolynomial (Fin 4) K) where
  carrier : MvPolynomial (Fin 4) K
  weight : Fin 4 → ℤ
  level : ℤ
  exponent : Fin 4 →₀ ℕ
  coeff : K
  carrier_hessian_zero : hessianDeterminant carrier = 0
  weight_bound : IsWeightLE weight level carrier
  exposed : initialForm weight level carrier = MvPolynomial.monomial exponent coeff
  coeff_ne_zero : coeff ≠ 0
  exponent_mem_source : exponent ∈ F.support
  exponent_nonlinear : 3 ≤ ordinaryDegree4 exponent
  exponent_boundary : MvExponentOnBoundary exponent

/-- **Finite singular support exposes a genuine nonlinear boundary vertex.**

This is the grading-free counterpart of
`exists_exposed_nonlinear_balanced_monomial`.  The proof uses only finite
coordinate maxima and the characteristic-zero monomial Hessian obstruction. -/
noncomputable def exposedSingularNonlinearBoundaryVertex
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    ExposedSingularNonlinearBoundaryVertexData F := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : hessianDeterminant D0.face = 0 := D0.hessian_zero hzero

  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : hessianDeterminant D1.face = 0 := D1.hessian_zero h0zero

  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : hessianDeterminant D2.face = 0 := D2.hessian_zero h1zero

  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)
  have h3zero : hessianDeterminant D3.face = 0 := D3.hessian_zero h2zero

  let d := D3.witness
  let c := MvPolynomial.coeff d D3.face

  have hd2 : d ∈ D2.face.support := D3.witness_mem
  have hd1 : d ∈ D1.face.support := D2.support_subset hd2
  have hd0 : d ∈ D0.face.support := D1.support_subset hd1
  have hdF : d ∈ F.support := D0.support_subset hd0

  have hc : c ≠ 0 := by
    dsimp [c]
    have hcoeff :
        MvPolynomial.coeff d D3.face = MvPolynomial.coeff d D2.face := by
      rw [D3.face_eq, coeff_initialForm, weight_coordinateMaxWeight]
      have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simp [hd3]
    rw [hcoeff]
    exact MvPolynomial.mem_support_iff.mp D3.witness_mem

  have hunique : ∀ q ∈ D3.face.support, q = d := by
    intro q hq
    have hq2 : q ∈ D2.face.support := D3.support_subset hq
    have hq1 : q ∈ D1.face.support := D2.support_subset hq2
    have hq0 : q ∈ D0.face.support := D1.support_subset hq1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using
        (D0.coordinate_eq q hq0).trans (D0.coordinate_eq d hd0).symm
    · simpa using
        (D1.coordinate_eq q hq1).trans (D1.coordinate_eq d hd1).symm
    · simpa using
        (D2.coordinate_eq q hq2).trans (D2.coordinate_eq d hd2).symm
    · have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simpa using (D3.coordinate_eq q hq).trans hd3.symm

  have hmono : D3.face = MvPolynomial.monomial d c := by
    apply MvPolynomial.ext
    intro q
    by_cases hqd : q = d
    · subst q
      simp [c]
    · have hq0 : MvPolynomial.coeff q D3.face = 0 := by
        by_contra hne
        have hqs : q ∈ D3.face.support := MvPolynomial.mem_support_iff.mpr hne
        exact hqd (hunique q hqs)
      have hdq : d ≠ q := by
        intro hdq
        exact hqd hdq.symm
      rw [hq0]
      simp [hdq]

  have hd3 : 3 ≤ ordinaryDegree4 d := hnonlinear d hdF

  have hboundary : MvExponentOnBoundary d := by
    by_contra hinterior
    have hpos : ∀ i : Fin 4, 0 < d i :=
      coordinate_pos_of_not_mvExponentOnBoundary hinterior
    have hmonomial_ne :
        hessianDeterminant (MvPolynomial.monomial d c) ≠ 0 :=
      hessianDeterminant_monomial_ne_zero hc hpos hd3
    apply hmonomial_ne
    rw [← hmono]
    exact h3zero

  exact {
    carrier := D2.face
    weight := coordinateMaxWeight (3 : Fin 4)
    level := (D3.level : ℤ)
    exponent := d
    coeff := c
    carrier_hessian_zero := h2zero
    weight_bound := D3.weight_bound
    exposed := by
      rw [← D3.face_eq]
      exact hmono
    coeff_ne_zero := hc
    exponent_mem_source := hdF
    exponent_nonlinear := hd3
    exponent_boundary := hboundary
  }

/-- Existential form convenient for proposition-valued terminal dispatchers. -/
theorem exists_exposed_singular_nonlinear_boundary_vertex
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    Nonempty (ExposedSingularNonlinearBoundaryVertexData F) :=
  ⟨exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear⟩

end

end HC4.Newton
