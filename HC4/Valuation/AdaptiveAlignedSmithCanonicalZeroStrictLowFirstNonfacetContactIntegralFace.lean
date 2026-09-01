import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import Mathlib.Tactic

/-!
# A19.R18: identify the integral contact Rees special fibre

The original first-contact carrier is written with the denominator-cleared
weight

    (scale, scale, scale, scale) + bump * e₀,

whereas the honest contact Rees uses the integral slope `r = bump / scale` and
weight `(r+1,1,1,1)`.  In the genuine other-facet branch `scale > 0` and the
retained contact package has `bump = scale * r`.  Hence the two exact weighted
components select precisely the same source monomials.

This file records that cancellation once and for all.  It is representation
plumbing only: no support relation is strengthened and no homogeneity of the
represented source is assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The denominator-cleared first-contact carrier and the integral contact
initial form are literally the same polynomial. -/
theorem QsOtherFacetContactQuadraticReesPackage.integralContactInitialForm_eq_face
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    HC4.Polynomial.initialForm
        (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 P.contactGap)
        (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) =
      C.face := by
  rw [C.face_eq]
  apply MvPolynomial.ext
  intro d
  rw [HC4.Polynomial.coeff_initialForm, HC4.Polynomial.coeff_initialForm]
  have hiff :
      Finsupp.weight
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 P.contactGap) d =
          (T.topFace.degree : ℤ) ↔
        Finsupp.weight
          (HC4.Newton.scaledContactWeight
            (HC4.Polynomial.facetOmittedCoordinate .qs) C.scale C.bump) d =
          ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    rw [HC4.Newton.weight_scaledContactWeight,
      HC4.Newton.weight_scaledContactWeight]
    change
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) +
            (P.contactGap : ℤ) * (d (0 : Fin 4) : ℤ) =
          (T.topFace.degree : ℤ) ↔
        (C.scale : ℤ) * HC4.Polynomial.ordinaryDegree4 d +
            (C.bump : ℤ) * (d (0 : Fin 4) : ℤ) =
          (C.scale : ℤ) * T.topFace.degree
    rw [P.bump_eq]
    push_cast
    have hs : (0 : ℤ) < C.scale := by
      exact_mod_cast C.scale_pos
    constructor <;> intro h
    · nlinarith
    · nlinarith
  by_cases h :
      Finsupp.weight
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 P.contactGap) d =
        (T.topFace.degree : ℤ)
  · rw [if_pos h, if_pos (hiff.mp h)]
  · have hs :
        Finsupp.weight
            (HC4.Newton.scaledContactWeight
              (HC4.Polynomial.facetOmittedCoordinate .qs) C.scale C.bump) d ≠
          ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
      intro hs
      exact h (hiff.mpr hs)
    rw [if_neg h, if_neg hs]

/-- Consequently the honest integral contact Rees specialises exactly to the
original first-contact carrier `C.face`. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_specialFiber_eq_face
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    polynomialFamilySpecialFiber P.contactFamily = C.face := by
  rw [P.specialFiber_eq_contact]
  exact P.integralContactInitialForm_eq_face

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
