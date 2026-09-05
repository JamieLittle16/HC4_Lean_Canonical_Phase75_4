import HC4.Valuation.AdaptiveAlignedSmithCanonicalCollisionNormalization
import HC4.Valuation.NonlinearDegreeBoundPreservation

/-!
# A18.5.87: remove the artificial degree-cap hypothesis from HC4 entry

The proposition-level collision normalizer of A18.5.86 accepts an explicit
`NonlinearDegreeBound`.  For an ordinary four-variable polynomial this is not
extra mathematical data: finite support is already bounded by
`MvPolynomial.totalDegree`.

This file packages that canonical bound and supplies the unrestricted collision
front door used by the final HC4 theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The total degree of an ordinary four-variable polynomial is automatically
a valid nonlinear source-degree ceiling. -/
theorem nonlinearDegreeBound_totalDegree
    (F : MvPolynomial (Fin 4) K) :
    NonlinearDegreeBound F.totalDegree F := by
  intro d hd _hnonlinear
  rw [← finsuppSum_eq_ordinaryDegree4]
  exact MvPolynomial.le_totalDegree hd

/-- **A18.5.87 — arbitrary exact determinant-one collision enters A18 with no
externally supplied degree cap.** -/
noncomputable def zeroDefectCollisionEntry_ofExactCollision_autoDegree
    (F : MvPolynomial (Fin 4) K)
    (p q : Fin 4 → K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
  zeroDefectCollisionEntry_ofExactCollision
    F.totalDegree F p q (nonlinearDegreeBound_totalDegree F)
      hdet hpq hcoll

end

end HC4.Valuation
