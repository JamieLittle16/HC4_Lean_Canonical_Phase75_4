import HC4.Valuation.AdaptiveAlignedSmithExactFourBlockSchur
import HC4.Valuation.ActualParameterLayer
import HC4.Polynomial.HessianDeterminant
import Mathlib.Tactic

/-!
# Corrected adaptive family / four-block API probe

Temporary only.  The previous probe guessed the fully-qualified namespace of
the Schur-series extensions.  Those extensions are already known to work by
dot notation in the green adaptive four-block module, so this probe lets Lean
resolve them directly.

It also prints the universal ring-hom APIs needed to swap

    MvPolynomial (Fin 4) (Polynomial K)

into

    Polynomial (MvPolynomial (Fin 4) K)

without inventing an ad hoc coefficient conversion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

#check fun
  (H : GeneralFourBlock
    (Polynomial (MvPolynomial (Fin 4) K))) =>
  H.polynomialSchurSeries

#check fun
  (H : GeneralFourBlock
    (Polynomial (MvPolynomial (Fin 4) K))) =>
  H.polynomialSchurSeries_determinant

#check GeneralFourBlock.ofSymmetricMatrix
#check GeneralFourBlock.matrix_det

#check MvPolynomial.eval₂Hom
#check MvPolynomial.ringHom_ext
#check Polynomial.mapRingHom
#check Polynomial.C
#check Matrix.det_map

#check familyParameterLayer
#check familyParameterLayer_coeff
#check HC4.Polynomial.hessian
#check HC4.Polynomial.hessianDeterminant

end

end HC4.Valuation
