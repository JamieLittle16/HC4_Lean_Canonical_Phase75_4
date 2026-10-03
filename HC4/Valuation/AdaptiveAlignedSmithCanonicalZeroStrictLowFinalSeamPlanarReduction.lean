
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamTerminalWeightRestriction
import HC4.Valuation.AdaptiveAlignedSmithMarkedAxisTerminal
import Mathlib.Tactic

/-!
# G15: any honest final-seam terminal weight gives a planar Keller collision

G14 shows that every honest marked terminal weight on the G13 fibre has a
second zero-weight coordinate.  In four variables the complement matching
carried by a non-scalar terminal conformal face then determines the entire
weight.

Indeed, the complement equations imply that the sum of all four weights is
`2*d`.  With two zero weights and the general bound `lambda_i <= d`, the
remaining two weights must both equal `d`.  A permutation fixing the marked
coordinate zero and moving the second zero into coordinate one therefore
standardizes the weight to

    (0, 0, d, d).

Weighted homogeneity, the Monge--Ampere identity, and the marked collision
are invariant under this coordinate permutation.  The already-green
two-zero marked-axis theorem then produces an explicit planar Keller map with
a collision at two distinct points.

Thus, after G15, the only HC4-specific missing statement is existence of the
honest terminal weight / associated-graded extraction.  No JC2 assumption is
used in this reduction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complement matching forces the total terminal weight to be twice the
terminal degree. -/
theorem terminalConformalFace_totalWeight_eq_two_degree
    {lambda : Fin 4 → ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F) :
    (∑ i : Fin 4, lambda i) = 2 * d := by
  rcases
      nonScalarTerminalConformalFace_has_complementWeightPermutation
        hface with
    ⟨pi, hpi⟩
  have hsum :
      (∑ i : Fin 4, (lambda (pi i) + lambda i)) =
        ∑ _i : Fin 4, d := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpi i
  have hperm :
      (∑ i : Fin 4, lambda (pi i)) =
        ∑ i : Fin 4, lambda i := by
    simpa using (Equiv.sum_comp pi lambda)
  rw [Finset.sum_add_distrib, hperm] at hsum
  have hbalance :
      2 * (∑ i : Fin 4, lambda i) = 4 * d := by
    simpa [two_mul, Fin.sum_univ_four] using hsum
  linarith

/-- Two zero coordinates in a nonnegative non-scalar terminal conformal face
can be standardized to coordinates zero and one by a permutation fixing the
marked coordinate zero. -/
theorem twoZeroMarkedTerminalWeight_standardizes
    {lambda : Fin 4 → ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg : IsNonnegativeIntegralWeight lambda)
    (h0 : lambda (0 : Fin 4) = 0)
    {z : Fin 4}
    (hz0 : z ≠ 0)
    (hz : lambda z = 0) :
    ∃ rho : Equiv.Perm (Fin 4),
      rho (0 : Fin 4) = 0 ∧
      (∀ i : Fin 4,
        lambda (rho.symm i) =
          standardTwoZeroTerminalWeight d i) := by
  have hd : 0 < d :=
    nonnegative_nonScalar_terminal_degree_pos hface hnonneg
  have htotal := terminalConformalFace_totalWeight_eq_two_degree hface
  have hle : ∀ i : Fin 4, lambda i ≤ d :=
    fun i => nonnegative_terminal_weight_le_degree hface hnonneg i

  fin_cases z
  · exact (hz0 rfl).elim
  · have h2d : lambda (2 : Fin 4) = d := by
      have h2le := hle (2 : Fin 4)
      have h3le := hle (3 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h2le, h3le]
    have h3d : lambda (3 : Fin 4) = d := by
      have h2le := hle (2 : Fin 4)
      have h3le := hle (3 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h2le, h3le]
    refine ⟨Equiv.refl (Fin 4), rfl, ?_⟩
    intro i
    fin_cases i
    · simpa using h0
    · simpa using hz
    · simpa using h2d
    · simpa using h3d
  · have h1d : lambda (1 : Fin 4) = d := by
      have h1le := hle (1 : Fin 4)
      have h3le := hle (3 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h1le, h3le]
    have h3d : lambda (3 : Fin 4) = d := by
      have h1le := hle (1 : Fin 4)
      have h3le := hle (3 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h1le, h3le]
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
    refine ⟨rho, by decide, ?_⟩
    intro i
    fin_cases i
    · change lambda (rho.symm 0) = 0
      have : rho.symm (0 : Fin 4) = 0 := by decide
      rw [this, h0]
    · change lambda (rho.symm 1) = 0
      have : rho.symm (1 : Fin 4) = 2 := by decide
      rw [this, hz]
    · change lambda (rho.symm 2) = d
      have : rho.symm (2 : Fin 4) = 1 := by decide
      rw [this, h1d]
    · change lambda (rho.symm 3) = d
      have : rho.symm (3 : Fin 4) = 3 := by decide
      rw [this, h3d]
  · have h1d : lambda (1 : Fin 4) = d := by
      have h1le := hle (1 : Fin 4)
      have h2le := hle (2 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h1le, h2le]
    have h2d : lambda (2 : Fin 4) = d := by
      have h1le := hle (1 : Fin 4)
      have h2le := hle (2 : Fin 4)
      have htotal4 :
          lambda 0 + lambda 1 + lambda 2 + lambda 3 = 2 * d := by
        simpa [Fin.sum_univ_four] using htotal
      linarith [htotal4, h0, hz, h1le, h2le]
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
    refine ⟨rho, by decide, ?_⟩
    intro i
    fin_cases i
    · change lambda (rho.symm 0) = 0
      have : rho.symm (0 : Fin 4) = 0 := by decide
      rw [this, h0]
    · change lambda (rho.symm 1) = 0
      have : rho.symm (1 : Fin 4) = 3 := by decide
      rw [this, hz]
    · change lambda (rho.symm 2) = d
      have : rho.symm (2 : Fin 4) = 2 := by decide
      rw [this, h2d]
    · change lambda (rho.symm 3) = d
      have : rho.symm (3 : Fin 4) = 1 := by decide
      rw [this, h1d]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **G15 planar reduction from an honest terminal weight.**

Every honest marked terminal weight on the G13 fibre produces an explicit
planar Keller collision. -/
theorem FinalSeamMarkedTerminalWeight.hasPlanarKellerCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    Nonempty (PlanarKellerCollisionData K) := by
  rcases W.exists_second_zero_away_from_square with
    ⟨z, hz0, hzell, hzw⟩
  rcases
      twoZeroMarkedTerminalWeight_standardizes
        W.conformalFace W.nonnegative W.markedZero hz0 hzw with
    ⟨rho, hfix, hweight⟩

  have hd : 0 < W.degree :=
    nonnegative_nonScalar_terminal_degree_pos
      W.conformalFace W.nonnegative

  have hweightFun :
      (fun i : Fin 4 => W.lambda (rho.symm i)) =
        standardTwoZeroTerminalWeight W.degree := by
    funext i
    exact hweight i

  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight W.degree)
        W.degree
        (MvPolynomial.rename rho S.fibre) := by
    have h :=
      integralWeightedHomogeneous_rename_perm W.homogeneous rho
    rw [hweightFun] at h
    exact h

  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho S.fibre) :=
    isPolynomialMongeAmpere_rename_perm rho S.mongeAmpere

  have hcoll := S.exactCollision.rename_perm rho
  have hcollMarked :
      HasExactGradientCollision
        (MvPolynomial.rename rho S.fibre)
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K)) := by
    rw [terminalPermutePoint_zeroPoint] at hcoll
    rw [terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero
      rho hfix] at hcoll
    simpa [negativeLongitudinalAxisPoint] using hcoll

  exact
    standardTwoZero_negativeLongitudinalAxis_hasPlanarKellerCollision
      hd hhomRenamed hMARenamed hcollMarked

/-- The exact remaining HC4-specific extraction obligation after G15:
construct an honest marked terminal weight on the already-normalized G13
transverse-square fibre. -/
def HasFinalSeamMarkedTerminalWeightExtraction
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∀ S : T.FinalSeamTransverseSquareData,
    Nonempty S.FinalSeamMarkedTerminalWeight

/-- Once the one remaining marked terminal-weight extraction is supplied, the
entire final singular seam reduces unconditionally to one explicit planar
Keller collision. -/
theorem hasPlanarKellerCollision_of_markedTerminalWeightExtraction
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hextract : T.HasFinalSeamMarkedTerminalWeightExtraction) :
    Nonempty (PlanarKellerCollisionData K) := by
  rcases T.finalSeamTransverseSquareData with ⟨S⟩
  rcases hextract S with ⟨W⟩
  exact W.hasPlanarKellerCollision

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
