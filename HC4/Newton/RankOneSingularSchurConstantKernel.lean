import HC4.Newton.RankOneSchurSeriesAlignment
import HC4.Newton.RankOneSingularSchurContinuation
import Mathlib.Tactic

/-!
# Constant raw kernel behind a stationary aligned rank-one Schur series

Constant alignment is only an algebraic change of binary Schur basis.  If the
aligned off-diagonal and kernel entries vanish identically, the original
unaligned polynomial Schur series therefore has a nonzero binary kernel whose
coordinates are constant in the parameter.

This file records that pullback explicitly.  It is intentionally independent
of HC4 source geometry.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R] [NoZeroDivisors R]

namespace BinarySchurPolynomialSeries

/-- A nonzero binary kernel of a polynomial Schur series whose two coordinates
are constant in the parameter. -/
def HasConstantBinaryKernel (S : BinarySchurPolynomialSeries R) : Prop :=
  ∃ u v : R,
    (u ≠ 0 ∨ v ≠ 0) ∧
      S.active * Polynomial.C u + S.offDiag * Polynomial.C v = 0 ∧
      S.offDiag * Polynomial.C u + S.kernel * Polynomial.C v = 0

/-- Pull a stationary left-aligned tail back to a constant kernel of the raw
series. -/
theorem hasConstantBinaryKernel_of_alignLeft_stationary
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot)
    (hoff : (S.alignLeft hleft).offDiag = 0)
    (hker : (S.alignLeft hleft).kernel = 0) :
    S.HasConstantBinaryKernel := by
  let a := S.active.coeff 0
  let b := S.offDiag.coeff 0
  refine ⟨-b, a, Or.inr ?_, ?_, ?_⟩
  · exact hleft.1
  · change
      S.active * Polynomial.C (-b) +
          S.offDiag * Polynomial.C a = 0
    change
      -(Polynomial.C b) * S.active +
          Polynomial.C a * S.offDiag = 0 at hoff
    simpa [map_neg, mul_comm] using hoff
  · change
      S.offDiag * Polynomial.C (-b) +
          S.kernel * Polynomial.C a = 0
    change
      (Polynomial.C b) ^ 2 * S.active -
          2 * Polynomial.C a * Polynomial.C b * S.offDiag +
          (Polynomial.C a) ^ 2 * S.kernel = 0 at hker
    change
      -(Polynomial.C b) * S.active +
          Polynomial.C a * S.offDiag = 0 at hoff
    have hfactor :
        Polynomial.C a *
            (S.offDiag * Polynomial.C (-b) +
              S.kernel * Polynomial.C a) = 0 := by
      calc
        Polynomial.C a *
              (S.offDiag * Polynomial.C (-b) +
                S.kernel * Polynomial.C a) =
            ((Polynomial.C b) ^ 2 * S.active -
                2 * Polynomial.C a * Polynomial.C b * S.offDiag +
                (Polynomial.C a) ^ 2 * S.kernel) +
              Polynomial.C b *
                (-(Polynomial.C b) * S.active +
                  Polynomial.C a * S.offDiag) := by
                    simp only [map_neg]
                    ring
        _ = 0 := by rw [hker, hoff]; simp
    have hCa : Polynomial.C a ≠ 0 := by
      exact Polynomial.C_ne_zero.mpr hleft.1
    exact (mul_eq_zero.mp hfactor).resolve_left hCa

/-- Pull a stationary right-axis alignment back to the obvious first-axis
kernel of the raw series. -/
theorem hasConstantBinaryKernel_of_alignRight_stationary
    (S : BinarySchurPolynomialSeries R)
    (hright : S.RightAxisPivot)
    (hoff : (S.alignRight hright).offDiag = 0)
    (hker : (S.alignRight hright).kernel = 0) :
    S.HasConstantBinaryKernel := by
  refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩
  · change S.active * Polynomial.C (1 : R) +
      S.offDiag * Polynomial.C (0 : R) = 0
    change S.active = 0 at hker
    simpa using hker
  · change S.offDiag * Polynomial.C (1 : R) +
      S.kernel * Polynomial.C (0 : R) = 0
    change S.offDiag = 0 at hoff
    simpa using hoff

end BinarySchurPolynomialSeries

end

end HC4.Newton
