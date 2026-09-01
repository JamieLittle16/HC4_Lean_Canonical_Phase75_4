import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryEulerSchurTransport
import HC4.Valuation.ExactKernelDefectDrop
import Mathlib.Tactic

/-!
# A19.R18: injectivity of simultaneous binary transverse inflation

The binary contact normalisation applies the three unit kernel inflations in
coordinates `1`, `2`, and `3`.  Each individual inflation is already known to
be injective: it preserves every source monomial and only multiplies its
coefficient by a nonzero parameter power.

R18 needs to cancel the *combined* transverse inflation after deriving the
straightened determinant equation.  We record that fact once at the owner of
the combined ring homomorphism.  This is cancellation of an injective ring map,
not division by the active Schur pivot.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K]

/-- Simultaneous unit transverse inflation is injective. -/
theorem unitTransverseInflateRingHom_injective :
    Function.Injective (unitTransverseInflateRingHom (K := K)) := by
  intro P Q hPQ
  apply kernelInflateHom_injective (K := K) (1 : Fin 4) 1
  apply kernelInflateHom_injective (K := K) (2 : Fin 4) 1
  apply kernelInflateHom_injective (K := K) (3 : Fin 4) 1
  exact hPQ

/-- Equality after simultaneous transverse inflation may therefore be pulled
back to the honest contact family. -/
theorem unitTransverseInflateFamily_injective
    {P Q : MvPolynomial (Fin 4) (Polynomial K)}
    (h : unitTransverseInflateFamily (K := K) P =
      unitTransverseInflateFamily (K := K) Q) :
    P = Q := by
  exact unitTransverseInflateRingHom_injective (K := K) h

end

end HC4.Valuation
