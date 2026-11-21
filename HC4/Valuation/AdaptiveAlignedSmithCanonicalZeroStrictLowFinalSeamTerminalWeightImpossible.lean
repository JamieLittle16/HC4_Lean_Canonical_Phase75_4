import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamPlanarReduction
import Mathlib.Tactic

/-!
# G16: the G13 transverse-square fibre admits no honest terminal weight

G14 already proves that every honest marked terminal weight on the G13 fibre
has a second zero-weight coordinate away from both the marked longitudinal
coordinate and the distinguished transverse square coordinate.

The conformal complement equations imply that the sum of all four terminal
weights is twice the terminal degree, and every individual weight is at most
that degree.  With two distinct zero coordinates, the remaining two
coordinates therefore both have full weight d.

But the distinguished transverse square lies on one of those remaining
coordinates and weighted homogeneity gives

    2 * lambda_ell = d.

Hence lambda_ell = d and 2 * lambda_ell = d force d = 0, contradicting the
strict positivity of the terminal degree.

Thus the whole-fibre terminal-cocharacter route is not merely unproved at the
final seam: it is impossible.  Any unrestricted closure must continue through
the source-honest associated-graded / first-break geometry rather than assume
weighted homogeneity of the complete G13 fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Any honest marked whole-fibre terminal weight on the G13 transverse-square
fibre is contradictory. -/
theorem FinalSeamMarkedTerminalWeight.impossible
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    False := by
  rcases W.exists_second_zero_away_from_square with
    ⟨z, hz0, hzell, hzw⟩

  have hdpos : 0 < W.degree :=
    nonnegative_nonScalar_terminal_degree_pos
      W.conformalFace W.nonnegative

  have htotal :
      W.lambda 0 + W.lambda 1 + W.lambda 2 + W.lambda 3 =
        2 * W.degree := by
    simpa [Fin.sum_univ_four] using
      terminalConformalFace_totalWeight_eq_two_degree W.conformalFace

  have hle0 : W.lambda (0 : Fin 4) ≤ W.degree :=
    nonnegative_terminal_weight_le_degree
      W.conformalFace W.nonnegative 0
  have hle1 : W.lambda (1 : Fin 4) ≤ W.degree :=
    nonnegative_terminal_weight_le_degree
      W.conformalFace W.nonnegative 1
  have hle2 : W.lambda (2 : Fin 4) ≤ W.degree :=
    nonnegative_terminal_weight_le_degree
      W.conformalFace W.nonnegative 2
  have hle3 : W.lambda (3 : Fin 4) ≤ W.degree :=
    nonnegative_terminal_weight_le_degree
      W.conformalFace W.nonnegative 3

  let ell : Fin 4 := S.familyPacket.ell
  have hell0 : ell ≠ 0 := by
    simpa [ell] using S.ell_ne_zero
  have hzell' : z ≠ ell := by
    simpa [ell] using hzell

  have hsquareDegree :
      W.lambda ell + W.lambda ell = W.degree := by
    have hdeg :=
      W.homogeneous
        (HC4.Newton.quadraticExponent ell ell)
        (by simpa [ell] using S.squareCoeff_ne_zero)
    simpa [HC4.Newton.quadraticExponent,
      integralWeightedDegree_eq_finsuppWeight] using hdeg

  have h0 : W.lambda (0 : Fin 4) = 0 := W.markedZero

  fin_cases z <;> fin_cases ell <;>
    simp_all <;> linarith

/-- Consequently the G15 whole-fibre marked terminal-weight extraction
interface is false for every actual final singular seam. -/
theorem not_hasFinalSeamMarkedTerminalWeightExtraction
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ¬ T.HasFinalSeamMarkedTerminalWeightExtraction := by
  intro hextract
  rcases T.finalSeamTransverseSquareData with ⟨S⟩
  rcases hextract S with ⟨W⟩
  exact W.impossible

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
