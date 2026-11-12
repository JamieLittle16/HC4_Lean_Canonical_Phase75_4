import HC4.Valuation.QuadraticTransverseCapSourceAxisSchur
import Mathlib.Tactic

/-!
# Source-honest transverse-section Hessian determinants

The longitudinal-axis Hessian unit theorem is only the y=0 case.
Here we restrict the original four-variable determinant-one source
to an arbitrary *constant transverse section* y in K³, leaving the
longitudinal coordinate x as a free polynomial indeterminate.

The resulting determinant is 1 in K[x], at every transverse section,
including y=±e₁ and y=±e₂. This is the honest source-level provenance
of the four remaining Schur unit equations in the five-section
rank-two collision endpoint. No quadratic-cap hypothesis is necessary
to preserve the unit determinant; that cap is needed only to identify
the section Hessian entries with C and C'.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Evaluate the three transverse coordinates at a constant point y,
but leave source coordinate zero free as a polynomial in X. -/
noncomputable def quadraticTransverseSourceSectionRingHom
    (y : Fin 3 → K) :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  (Polynomial.mapRingHom (MvPolynomial.eval y)).comp
    (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom

/-- Actual Hessian block obtained by restricting the original
four-variable Hessian to the section (x,y). -/
noncomputable def quadraticTransverseSourceSectionFourBlock
    (F : MvPolynomial (Fin 4) K)
    (y : Fin 3 → K) : GeneralFourBlock (Polynomial K) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.hessian F).map
      (quadraticTransverseSourceSectionRingHom y))

theorem quadraticTransverseSourceSectionHessian_symmetric
    (F : MvPolynomial (Fin 4) K)
    (y : Fin 3 → K)
    (i j : Fin 4) :
    ((HC4.Polynomial.hessian F).map
      (quadraticTransverseSourceSectionRingHom y)) i j =
    ((HC4.Polynomial.hessian F).map
      (quadraticTransverseSourceSectionRingHom y)) j i := by
  change
    quadraticTransverseSourceSectionRingHom y
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i F)) =
      quadraticTransverseSourceSectionRingHom y
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F))
  congr 1
  exact (pderiv_comm_commRing i j F).symm

/-- Every constant transverse section of the same represented
determinant-one source has a unit four-block Hessian determinant
as an exact identity in the longitudinal polynomial ring. -/
theorem quadraticTransverseSourceSectionFourBlock_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (y : Fin 3 → K) :
    (quadraticTransverseSourceSectionFourBlock F y).determinantCore = 1 := by
  let phi : MvPolynomial (Fin 4) K →+* Polynomial K :=
    quadraticTransverseSourceSectionRingHom y
  let H : Matrix (Fin 4) (Fin 4) (Polynomial K) :=
    (HC4.Polynomial.hessian F).map phi
  have hsymm : ∀ i j : Fin 4, H i j = H j i := by
    intro i j
    exact quadraticTransverseSourceSectionHessian_symmetric F y i j
  have hmat :
      (quadraticTransverseSourceSectionFourBlock F y).matrix = H :=
    GeneralFourBlock.matrix_ofSymmetricMatrix H hsymm
  calc
    (quadraticTransverseSourceSectionFourBlock F y).determinantCore =
        (quadraticTransverseSourceSectionFourBlock F y).matrix.det :=
      (GeneralFourBlock.matrix_det _).symm
    _ = H.det := by rw [hmat]
    _ = phi ((HC4.Polynomial.hessian F).det) := by
      exact (phi.map_det (HC4.Polynomial.hessian F)).symm
    _ = phi (HC4.Polynomial.hessianDeterminant F) := rfl
    _ = 1 := by rw [hdet]; simp

/-- The four honest transverse sections y=±e₁, y=±e₂ already
carry determinant one. The remaining cap-two calculation identifies
each four-block with its v±C'eᵢ and fixed C normal form. -/
theorem quadraticTransverseSource_fourOppositeSections_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let e0 : Fin 3 → K := fun i => if i = 0 then 1 else 0
    let e1 : Fin 3 → K := fun i => if i = 1 then 1 else 0
    (quadraticTransverseSourceSectionFourBlock F e0).determinantCore = 1 ∧
    (quadraticTransverseSourceSectionFourBlock F (fun i => -e0 i)).determinantCore = 1 ∧
    (quadraticTransverseSourceSectionFourBlock F e1).determinantCore = 1 ∧
    (quadraticTransverseSourceSectionFourBlock F (fun i => -e1 i)).determinantCore = 1 := by
  dsimp only
  exact ⟨quadraticTransverseSourceSectionFourBlock_unit F hdet _,
    quadraticTransverseSourceSectionFourBlock_unit F hdet _,
    quadraticTransverseSourceSectionFourBlock_unit F hdet _,
    quadraticTransverseSourceSectionFourBlock_unit F hdet _⟩

/-- Three *arbitrary* opposite transverse basis pairs, including the
third pair omitted by the earlier five-section algebra, are exact unit
Hessian determinants of the SAME source. -/
theorem quadraticTransverseSource_allThreeOppositePairs_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    ∀ j : Fin 3,
      (quadraticTransverseSourceSectionFourBlock F
        (fun i : Fin 3 => if i = j then 1 else 0)).determinantCore = 1 ∧
      (quadraticTransverseSourceSectionFourBlock F
        (fun i : Fin 3 => if i = j then -1 else 0)).determinantCore = 1 := by
  intro j
  exact ⟨quadraticTransverseSourceSectionFourBlock_unit F hdet _,
    quadraticTransverseSourceSectionFourBlock_unit F hdet _⟩

/-- The zero transverse section is literally the old
longitudinal-axis ring-hom restriction. -/
theorem quadraticTransverseSourceSectionRingHom_zero :
    quadraticTransverseSourceSectionRingHom
        (fun _ : Fin 3 => (0 : K)) =
      longitudinalAxisRestrictionRingHom (K := K) := by
  rfl


end

end HC4.Valuation
