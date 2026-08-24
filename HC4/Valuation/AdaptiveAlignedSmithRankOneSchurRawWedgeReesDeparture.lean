import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTransverseReesKernelLeadingLayer
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurCorrectedRS2Fork
import Mathlib.Tactic

/-!
# Stage 4B36: raw Schur motion gives a first honest Rees projective departure

B32 isolates the correct projective obstruction on the raw binary Schur line,
while B34--B35 give an exact polynomial Rees kernel in literal source
coordinates and identify its first coefficient with the retained B8 leading
vector.

There is one final bookkeeping issue before the corrected-RS2 coefficient can
be taken: a nonzero raw Schur wedge may already be visible inside that leading
homogeneous coefficient, rather than first appearing in a strictly later
kernel coefficient.  Therefore the correct selector is the *first parameter
coefficient of the projective wedge itself*.

This file establishes that selector with full provenance.

* a nonzero raw binary Schur wedge forces the canonical left-pivot lift;
* its full lifted kernel has a nonzero projective wedge;
* swap/shear/permutation transport preserves existence of projective motion;
* evaluation of the B34 Rees kernel at `tau = 1` recovers the source kernel;
* hence the corresponding Rees projective wedge is nonzero;
* its least occurring parameter order is selected, is nonzero, and every
  lower projective-wedge layer vanishes.

The output is attached to the same B30 canonical RS2 provenance assembly.
No RS2 identity and no repair conclusion are asserted in this file: the next
local calculation may now work at one exact first projective Rees layer with
all lower projective terms literally zero.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Projective wedge of two components of an arbitrary polynomial vector. -/
def sourceVectorProjectiveWedge
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) : MvPolynomial (Fin 4) K :=
  W i * MvPolynomial.pderiv k (W j) -
    W j * MvPolynomial.pderiv k (W i)

/-- The same projective wedge for a vector over the auxiliary Rees coefficient
ring. -/
def reesVectorProjectiveWedge
    (W : Fin 4 → MvPolynomial (Fin 4) (Polynomial K))
    (i j k : Fin 4) : MvPolynomial (Fin 4) (Polynomial K) :=
  W i * MvPolynomial.pderiv k (W j) -
    W j * MvPolynomial.pderiv k (W i)

@[simp] theorem sourceVectorProjectiveWedge_sourceCoordinateKernelVector
    (rho : Equiv.Perm (Fin 4))
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) :
    sourceVectorProjectiveWedge
        (sourceCoordinateKernelVector rho W) (rho i) (rho j) k =
      sourceVectorProjectiveWedge W i j k := by
  simp [sourceVectorProjectiveWedge, sourceCoordinateKernelVector]

@[simp] theorem sourceVectorProjectiveWedge_swap02_zero_three
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (k : Fin 4) :
    sourceVectorProjectiveWedge (swap02KernelVector W) 0 3 k =
      sourceVectorProjectiveWedge W 2 3 k := by
  simp [sourceVectorProjectiveWedge, swap02KernelVector]

/-- The original `(2,3)` projective wedge is the difference of the two
corresponding wedges after the elementary input shear. -/
theorem sourceVectorProjectiveWedge_shear02_recover_two_three
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (k : Fin 4) :
    sourceVectorProjectiveWedge (shear02KernelVector W) 2 3 k -
        sourceVectorProjectiveWedge (shear02KernelVector W) 0 3 k =
      sourceVectorProjectiveWedge W 2 3 k := by
  simp [sourceVectorProjectiveWedge, shear02KernelVector]
  ring

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-! ## Canonical raw moving lift -/

private theorem specialFourBlock_schurA_eq_raw_coeff_zero_B36
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurA =
      C.chartData.schurData.block.polynomialSchurSeries.active.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurA C.chartData.schurData.block).symm

private theorem specialFourBlock_schurB_eq_raw_coeff_zero_B36
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurB =
      C.chartData.schurData.block.polynomialSchurSeries.offDiag.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurB C.chartData.schurData.block).symm

private theorem specialFourBlock_schurC_eq_raw_coeff_zero_B36
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurC =
      C.chartData.schurData.block.polynomialSchurSeries.kernel.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurC C.chartData.schurData.block).symm

namespace DenominatorClearedSpecialSchurKernelData

/-- For the canonical left-pivot binary generator `(-B,A)`, the projective
wedge of the last two cleared lifted coordinates is exactly `Delta^2` times
the raw binary Schur wedge. -/
theorem projectiveWedge_two_three_of_raw_generator
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (hu : E.u = -C.specialFourBlock.schurB)
    (hv : E.v = C.specialFourBlock.schurA)
    (k : Fin 4) :
    E.projectiveWedge 2 3 k =
      C.specialFourBlock.activeDet ^ 2 *
        C.rawSpecialSchurProjectiveWedge k := by
  unfold projectiveWedge fullVector
  rw [hu, hv]
  simp [GeneralFourBlock.clearedKernelLift,
    rawSpecialSchurProjectiveWedge, MvPolynomial.pderiv_mul]
  ring

/-- A nonzero `(2,3)` wedge of the full chart kernel survives removal of the
auxiliary coordinate/swap/shear chart and the retained coordinate
permutation, possibly in a different pair of vector coordinates. -/
theorem exists_sourceCoordinateProjectiveWedge_of_full_two_three
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (k : Fin 4)
    (hfull : E.projectiveWedge 2 3 k ≠ 0) :
    ∃ i j : Fin 4,
      sourceVectorProjectiveWedge E.sourceCoordinateData.vector i j k ≠ 0 := by
  classical
  let rho := C.chartData.chart.rho
  let D := E.toCoordinateSpecialKernelData
  have hsourceVector :
      E.sourceCoordinateData.vector =
        sourceCoordinateKernelVector rho D.vector := by
    rfl
  by_contra hnone
  push_neg at hnone
  generalize hkind : C.chartData.chart.kind = kind
  cases kind with
  | coordinate =>
      have hcoord : D.vector = E.fullVector := by
        change coordinateKernelVectorForChartKind
          C.chartData.chart.kind E.fullVector = E.fullVector
        simpa [coordinateKernelVectorForChartKind, hkind]
      have hz := hnone (rho 2) (rho 3)
      rw [hsourceVector,
        sourceVectorProjectiveWedge_sourceCoordinateKernelVector] at hz
      rw [hcoord] at hz
      exact hfull (by simpa [sourceVectorProjectiveWedge, projectiveWedge] using hz)
  | swap02 =>
      have hcoord : D.vector = swap02KernelVector E.fullVector := by
        change coordinateKernelVectorForChartKind
          C.chartData.chart.kind E.fullVector = swap02KernelVector E.fullVector
        simpa [coordinateKernelVectorForChartKind, hkind]
      have hz := hnone (rho 0) (rho 3)
      rw [hsourceVector,
        sourceVectorProjectiveWedge_sourceCoordinateKernelVector] at hz
      rw [hcoord] at hz
      have hz' : sourceVectorProjectiveWedge E.fullVector 2 3 k = 0 := by
        simpa using hz
      exact hfull (by simpa [sourceVectorProjectiveWedge, projectiveWedge] using hz')
  | shear02 =>
      have hcoord : D.vector = shear02KernelVector E.fullVector := by
        change coordinateKernelVectorForChartKind
          C.chartData.chart.kind E.fullVector = shear02KernelVector E.fullVector
        simpa [coordinateKernelVectorForChartKind, hkind]
      have hz23 := hnone (rho 2) (rho 3)
      have hz03 := hnone (rho 0) (rho 3)
      rw [hsourceVector,
        sourceVectorProjectiveWedge_sourceCoordinateKernelVector, hcoord] at hz23 hz03
      have hrecovered :=
        sourceVectorProjectiveWedge_shear02_recover_two_three
          (K := K) E.fullVector k
      rw [hz23, hz03] at hrecovered
      have hz' : sourceVectorProjectiveWedge E.fullVector 2 3 k = 0 := by
        simpa using hrecovered.symm
      exact hfull (by simpa [sourceVectorProjectiveWedge, projectiveWedge] using hz')

end DenominatorClearedSpecialSchurKernelData

/-- A nonzero raw Schur wedge canonically chooses the left-pivot binary
representative `(-B,A)`.  The right-axis pivot is impossible because there
both raw entries `A` and `B` vanish.  The returned source-coordinate wedge is
therefore attached to a specified denominator-cleared kernel. -/
theorem exists_denominatorClearedSpecialSchurKernelData_with_sourceWedge_of_rawWedge
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (hraw : C.rawSpecialSchurProjectiveWedge k ≠ 0) :
    ∃ E : C.DenominatorClearedSpecialSchurKernelData,
      ∃ i j : Fin 4,
        sourceVectorProjectiveWedge E.sourceCoordinateData.vector i j k ≠ 0 := by
  let H := C.chartData.schurData.block
  let S := H.polynomialSchurSeries
  let H0 := C.specialFourBlock
  have hA := C.specialFourBlock_schurA_eq_raw_coeff_zero_B36
  have hB := C.specialFourBlock_schurB_eq_raw_coeff_zero_B36
  have hC := C.specialFourBlock_schurC_eq_raw_coeff_zero_B36
  generalize hp : C.chartData.schurData.chosenPivot = p
  cases p with
  | right hright =>
      exfalso
      apply hraw
      unfold rawSpecialSchurProjectiveWedge
      rw [hA, hB, hright.1, hright.2.1]
      simp
  | left hleft =>
      let u : MvPolynomial (Fin 4) K := -H0.schurB
      let v : MvPolynomial (Fin 4) K := H0.schurA
      have hv : v ≠ 0 := by
        dsimp [v, H0]
        rw [hA]
        exact hleft.1
      have hdet : H0.schurA * H0.schurC = H0.schurB * H0.schurB := by
        dsimp [H0]
        rw [hA, hB, hC]
        exact hleft.2
      have hker : H0.IsClearedSchurKernel u v := by
        unfold GeneralFourBlock.IsClearedSchurKernel
        constructor
        · dsimp [u, v]
          ring
        · dsimp [u, v]
          rw [show H0.schurC * H0.schurA = H0.schurA * H0.schurC by ring]
          rw [hdet]
          ring
      let E : C.DenominatorClearedSpecialSchurKernelData := {
        u := u
        v := v
        binary_ne_zero := Or.inr hv
        schurKernel := hker
      }
      have huE : E.u = -C.specialFourBlock.schurB := by rfl
      have hvE : E.v = C.specialFourBlock.schurA := by rfl
      have hactive : C.specialFourBlock.activeDet ≠ 0 := by
        change
          (parameterConstantCoeffFourBlock C.chartData.schurData.block).activeDet ≠ 0
        rw [← parameterConstantCoeffFourBlock_activeDet]
        exact C.chartData.schurData.activeDet_coeff_zero_ne_zero
      have hfull : E.projectiveWedge 2 3 k ≠ 0 := by
        rw [E.projectiveWedge_two_three_of_raw_generator huE hvE k]
        exact mul_ne_zero (pow_ne_zero 2 hactive) hraw
      rcases E.exists_sourceCoordinateProjectiveWedge_of_full_two_three k hfull with
        ⟨i, j, hij⟩
      exact ⟨E, i, j, hij⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Rees projective-wedge transport and least coefficient -/

/-- Evaluating the B34 rescaled Rees kernel at `tau = 1` recovers the
original source-coordinate kernel component. -/
theorem map_evalOne_transverseSourceReesKernel
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (j : Fin 4) :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K))
        (transverseSourceReesKernel W j) = W j := by
  unfold transverseSourceReesKernel
  rw [map_mul]
  rw [map_evalOne_transverseSourceReesFamily]
  fin_cases j <;> simp [transverseReesKernelScale]

/-- Evaluation at `tau = 1` also recovers every projective wedge. -/
theorem map_evalOne_reesVectorProjectiveWedge
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K))
        (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k) =
      sourceVectorProjectiveWedge W i j k := by
  unfold reesVectorProjectiveWedge sourceVectorProjectiveWedge
  rw [map_sub, map_mul, map_mul]
  rw [← MvPolynomial.pderiv_map, ← MvPolynomial.pderiv_map]
  simp only [map_evalOne_transverseSourceReesKernel]

/-- A source-coordinate projective wedge cannot disappear in the auxiliary
Rees family. -/
theorem reesVectorProjectiveWedge_ne_zero_of_source
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4)
    (hsource : sourceVectorProjectiveWedge W i j k ≠ 0) :
    reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (MvPolynomial.map (Polynomial.evalRingHom (1 : K))) hzero
  rw [map_evalOne_reesVectorProjectiveWedge] at hmap
  simp at hmap
  exact hsource hmap

/-- Every nonzero polynomial-valued multivariate family has at least one
actual parameter order. -/
theorem familyParameterLayerOrders_nonempty_of_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0) :
    (familyParameterLayerOrders P).Nonempty := by
  classical
  rcases MvPolynomial.support_nonempty.mpr hP with ⟨d, hd⟩
  have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rcases Polynomial.support_nonempty.mpr hcoeff with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply (mem_familyParameterLayerOrders_iff P n).2
  refine ⟨d, hd, ?_⟩
  exact Polynomial.mem_support_iff.mp hn

/-- Least parameter order occurring in an arbitrary nonzero polynomial-valued
multivariate family.  Unlike the older `firstPositiveActualParameterOrder`,
order zero is intentionally allowed here. -/
noncomputable def firstActualParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0) : ℕ :=
  (familyParameterLayerOrders P).min'
    (familyParameterLayerOrders_nonempty_of_ne_zero P hP)

theorem firstActualParameterOrder_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0) :
    firstActualParameterOrder P hP ∈ familyParameterLayerOrders P := by
  unfold firstActualParameterOrder
  exact Finset.min'_mem _ _

/-- The selected first actual parameter coefficient is nonzero. -/
theorem firstActualParameterLayer_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0) :
    familyParameterLayer P (firstActualParameterOrder P hP) ≠ 0 := by
  exact familyParameterLayer_ne_zero_of_mem P
    (firstActualParameterOrder_mem P hP)

/-- Every parameter coefficient below the selected first actual order
vanishes. -/
theorem familyParameterLayer_eq_zero_of_lt_firstActualParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    {n : ℕ}
    (hn : n < firstActualParameterOrder P hP) :
    familyParameterLayer P n = 0 := by
  by_contra hlayer
  have hnmem : n ∈ familyParameterLayerOrders P := by
    classical
    rcases MvPolynomial.support_nonempty.mpr hlayer with ⟨d, hd⟩
    have hlayerCoeff : MvPolynomial.coeff d (familyParameterLayer P n) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hparamCoeff : (MvPolynomial.coeff d P).coeff n ≠ 0 := by
      simpa [familyParameterLayer_coeff] using hlayerCoeff
    have hcoeff : MvPolynomial.coeff d P ≠ 0 := by
      intro hz
      rw [hz] at hparamCoeff
      simp at hparamCoeff
    have hdP : d ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    exact (mem_familyParameterLayerOrders_iff P n).2
      ⟨d, hdP, hparamCoeff⟩
  have hle : firstActualParameterOrder P hP ≤ n := by
    unfold firstActualParameterOrder
    exact Finset.min'_le (familyParameterLayerOrders P) n hnmem
  omega

/-- Exact first projective departure of the B34 Rees kernel. -/
structure FirstReesProjectiveWedgeDepartureData
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) where
  wedge_ne_zero :
    reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k ≠ 0
  order : ℕ
  order_eq :
    order = firstActualParameterOrder
      (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k)
      wedge_ne_zero
  layer_ne_zero :
    familyParameterLayer
      (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k)
      order ≠ 0
  lower_layers_zero :
    ∀ n : ℕ, n < order →
      familyParameterLayer
        (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k) n = 0

/-- Construct the exact first Rees projective departure from any honest
nonzero source-coordinate wedge. -/
theorem exists_firstReesProjectiveWedgeDepartureData
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4)
    (hsource : sourceVectorProjectiveWedge W i j k ≠ 0) :
    Nonempty (FirstReesProjectiveWedgeDepartureData W i j k) := by
  let P := reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k
  have hP : P ≠ 0 :=
    reesVectorProjectiveWedge_ne_zero_of_source W i j k hsource
  let n := firstActualParameterOrder P hP
  refine ⟨{
    wedge_ne_zero := hP
    order := n
    order_eq := rfl
    layer_ne_zero := ?_
    lower_layers_zero := ?_
  }⟩
  · exact firstActualParameterLayer_ne_zero P hP
  · intro q hq
    exact familyParameterLayer_eq_zero_of_lt_firstActualParameterOrder
      P hP hq

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- **B30-provenanced first Rees projective departure.**

A nonzero raw binary Schur wedge is transported to an exact first
projective-wedge coefficient of the B34 Rees kernel belonging to the *same*
denominator-cleared kernel used to construct the B30 first-key assembly. -/
structure RawWedgeFirstReesDepartureProvenanceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4) where
  schurKernel : C.DenominatorClearedSpecialSchurKernelData
  assembly : C.FirstKeyCanonicalRS2ProvenanceAssemblyData
  assembly_schurKernel : assembly.schurKernel = schurKernel
  i : Fin 4
  j : Fin 4
  source_wedge_ne_zero :
    sourceVectorProjectiveWedge assembly.leading.sourceKernel.vector i j k ≠ 0
  departure :
    FirstReesProjectiveWedgeDepartureData
      assembly.leading.sourceKernel.vector i j k

/-- Produce the exact first Rees projective departure while retaining the
whole B30 first-key/`x0^e L^m` provenance packet. -/
theorem HasFirstTransverseSourceKey.exists_rawWedgeFirstReesDepartureProvenanceData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey)
    (k : Fin 4)
    (hraw : C.rawSpecialSchurProjectiveWedge k ≠ 0) :
    Nonempty (C.RawWedgeFirstReesDepartureProvenanceData k) := by
  rcases C.exists_denominatorClearedSpecialSchurKernelData_with_sourceWedge_of_rawWedge
      k hraw with ⟨E, i, j, hsource⟩
  rcases hkey.exists_leadingTransverseKernelData_of_schurKernel E with
    ⟨L, hsourceKernel⟩
  rcases L.exists_canonicalMaximalHomogeneousKernelData with ⟨M⟩
  rcases L.exists_longitudinalFactorData_unconditional with ⟨F⟩
  let A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData := {
    schurKernel := E
    leading := L
    sourceKernel_eq := hsourceKernel
    canonical := M
    factor := F
  }
  have hsourceA :
      sourceVectorProjectiveWedge A.leading.sourceKernel.vector i j k ≠ 0 := by
    change sourceVectorProjectiveWedge L.sourceKernel.vector i j k ≠ 0
    rw [hsourceKernel]
    exact hsource
  rcases exists_firstReesProjectiveWedgeDepartureData
      A.leading.sourceKernel.vector i j k hsourceA with ⟨D⟩
  exact ⟨{
    schurKernel := E
    assembly := A
    assembly_schurKernel := rfl
    i := i
    j := j
    source_wedge_ne_zero := hsourceA
    departure := D
  }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
