import HC4.Valuation.ParameterGapSecondJet
import Mathlib.Tactic

/-!
# Second determinant variation at an exact rank-two kernel block

Let the constant matrix have support only in coordinates `0,3`,

    A = [[a,0,0,b],
         [0,0,0,0],
         [0,0,0,0],
         [c,0,0,d]].

For an arbitrary first layer `B` and arbitrary second layer `C`, form the
universal second parameter jet

    ((A,B),(B,2C)).

Because `A` has rank at most two and vanishes on kernel coordinates `1,2`,
the doubly nilpotent determinant component is independent of `C` and of all
entries of `B` outside the kernel block.  It is exactly

    2 * det(A_{0,3}) * det(B_{1,2}).

This is the source-honest coefficient bridge needed by the finite-staircase
central branch: higher parameter layers are retained, but cannot contribute to
the first nonzero determinant variation.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- A four-by-four matrix supported on the active coordinate pair `0,3`. -/
def rankTwoZeroKernelBase
    {R : Type*} [CommRing R]
    (a b c d : R) : Matrix (Fin 4) (Fin 4) R :=
  !![a, 0, 0, b;
     0, 0, 0, 0;
     0, 0, 0, 0;
     c, 0, 0, d]

/-- Universal scalar second-variation jet `a + eps*b + eps^2*c`, represented
in nested dual numbers with the conventional factor `2*c`. -/
def rankTwoSecondVariationEntry
    {R : Type*} [CommRing R]
    (a b c : R) : DualNumber (DualNumber R) :=
  ((a, b), (b, 2 * c))

/-- Entrywise second-variation jet around the rank-two `0,3` base. -/
def rankTwoZeroKernelSecondVariation
    {R : Type*} [CommRing R]
    (a b c d : R)
    (B C : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber R)) :=
  fun i j =>
    rankTwoSecondVariationEntry
      (rankTwoZeroKernelBase a b c d i j)
      (B i j) (C i j)

/-- **Exact second determinant variation at a rank-two kernel block.**

No symmetry hypothesis is needed.  The correction layer `C` and every
first-layer entry outside the kernel coordinates disappear identically. -/
set_option maxHeartbeats 5000000 in
theorem snd_snd_det_rankTwoZeroKernelSecondVariation
    {R : Type*} [CommRing R]
    (a b c d : R)
    (B C : Matrix (Fin 4) (Fin 4) R) :
    TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (rankTwoZeroKernelSecondVariation a b c d B C).det) =
      2 * (a * d - b * c) *
        (B 1 1 * B 2 2 - B 1 2 * B 2 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [rankTwoZeroKernelSecondVariation,
    rankTwoZeroKernelBase, rankTwoSecondVariationEntry,
    Matrix.det_fin_three, Fin.succAbove, DualNumber.snd_mul]
  ring


/-- Domain-level cancellation form of the rank-two second variation.  This is
the version used when the coefficient ring is itself a multivariate
polynomial ring. -/
theorem kernelBlock_det_eq_zero_of_secondVariation_eq_zero_domain
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {a b c d : R}
    (B C : Matrix (Fin 4) (Fin 4) R)
    (htwo : (2 : R) ≠ 0)
    (hactive : a * d - b * c ≠ 0)
    (hzero :
      TrivSqZeroExt.snd
          (TrivSqZeroExt.snd
            (rankTwoZeroKernelSecondVariation a b c d B C).det) = 0) :
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  rw [snd_snd_det_rankTwoZeroKernelSecondVariation] at hzero
  have hfactor : 2 * (a * d - b * c) ≠ 0 :=
    mul_ne_zero htwo hactive
  have hprod :
      (2 * (a * d - b * c)) *
          (B 1 1 * B 2 2 - B 1 2 * B 2 1) = 0 := by
    simpa [mul_assoc] using hzero
  exact (mul_eq_zero.mp hprod).resolve_left hfactor

/-- If the complete second determinant variation vanishes and the active
constant minor is nonzero, then the first layer has singular binary kernel
block. -/
theorem kernelBlock_det_eq_zero_of_secondVariation_eq_zero
    {K : Type*} [Field K]
    {a b c d : K}
    (B C : Matrix (Fin 4) (Fin 4) K)
    (hactive : a * d - b * c ≠ 0)
    (hzero :
      TrivSqZeroExt.snd
          (TrivSqZeroExt.snd
            (rankTwoZeroKernelSecondVariation a b c d B C).det) = 0) :
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  rw [snd_snd_det_rankTwoZeroKernelSecondVariation] at hzero
  have htwo : (2 : K) ≠ 0 := by
    norm_num
  have hfactor : 2 * (a * d - b * c) ≠ 0 :=
    mul_ne_zero htwo hactive
  have hprod :
      (2 * (a * d - b * c)) *
          (B 1 1 * B 2 2 - B 1 2 * B 2 1) = 0 := by
    simpa [mul_assoc] using hzero
  exact (mul_eq_zero.mp hprod).resolve_left hfactor



/-- Domain-level polynomial-matrix gap bridge.  It differs from the field
version only in making the cancellation hypotheses explicit. -/
theorem kernelBlock_det_eq_zero_of_polynomialMatrix_gap_domain
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hgap : ∀ r s,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s,
      (M r s).coeff 0 = rankTwoZeroKernelBase a b c d r s)
    (htwo : (2 : R) ≠ 0)
    (hactive : a * d - b * c ≠ 0)
    (hdet : M.det = 0) :
    let B : Matrix (Fin 4) (Fin 4) R :=
      fun r s => (M r s).coeff j
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  let B : Matrix (Fin 4) (Fin 4) R :=
    fun r s => (M r s).coeff j
  let C : Matrix (Fin 4) (Fin 4) R :=
    fun r s => (M r s).coeff (2 * j)
  change B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0
  have hjet :
      HC4.Valuation.matrixParameterGapSecondJet hj M hgap =
        rankTwoZeroKernelSecondVariation a b c d B C := by
    apply Matrix.ext
    intro r s
    rw [HC4.Valuation.matrixParameterGapSecondJet_apply]
    simp [rankTwoZeroKernelSecondVariation, rankTwoSecondVariationEntry,
      B, C, hbase]
  have hbridge :=
    HC4.Valuation.snd_snd_det_matrixParameterGapSecondJet
      (R := R) hj M hgap
  have hzero :
      TrivSqZeroExt.snd
          (TrivSqZeroExt.snd
            (HC4.Valuation.matrixParameterGapSecondJet hj M hgap).det) = 0 := by
    rw [hbridge, hdet]
    simp
  rw [hjet] at hzero
  exact kernelBlock_det_eq_zero_of_secondVariation_eq_zero_domain
    B C htwo hactive hzero

/-- **Polynomial-family bridge for the rank-two second variation.**

Let a polynomial matrix have no positive parameter coefficient below a
positive order \`j\`.  If its constant layer is exactly a matrix supported on
the active coordinates \`0,3\`, its determinant vanishes identically, and that
active \`2 x 2\` minor is nonzero, then the \`j\`-th coefficient layer has
singular kernel block on coordinates \`1,2\`.

The arbitrary \`2*j\` coefficient layer is retained: the preceding exact
second-variation theorem proves that it cannot affect this conclusion. -/
theorem kernelBlock_det_eq_zero_of_polynomialMatrix_gap
    {K : Type*} [Field K]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hgap : ∀ r s,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : K)
    (hbase : ∀ r s,
      (M r s).coeff 0 = rankTwoZeroKernelBase a b c d r s)
    (hactive : a * d - b * c ≠ 0)
    (hdet : M.det = 0) :
    let B : Matrix (Fin 4) (Fin 4) K :=
      fun r s => (M r s).coeff j
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  let B : Matrix (Fin 4) (Fin 4) K :=
    fun r s => (M r s).coeff j
  let C : Matrix (Fin 4) (Fin 4) K :=
    fun r s => (M r s).coeff (2 * j)
  change B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0
  have hjet :
      HC4.Valuation.matrixParameterGapSecondJet hj M hgap =
        rankTwoZeroKernelSecondVariation a b c d B C := by
    apply Matrix.ext
    intro r s
    rw [HC4.Valuation.matrixParameterGapSecondJet_apply]
    simp [rankTwoZeroKernelSecondVariation, rankTwoSecondVariationEntry,
      B, C, hbase]
  have hbridge :=
    HC4.Valuation.snd_snd_det_matrixParameterGapSecondJet
      (R := K) hj M hgap
  have hzero :
      TrivSqZeroExt.snd
          (TrivSqZeroExt.snd
            (HC4.Valuation.matrixParameterGapSecondJet hj M hgap).det) = 0 := by
    rw [hbridge, hdet]
    simp
  rw [hjet] at hzero
  exact kernelBlock_det_eq_zero_of_secondVariation_eq_zero
    B C hactive hzero

end

end HC4.Polynomial
