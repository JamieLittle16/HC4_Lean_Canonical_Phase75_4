import HC4.Newton.FiniteSupportCrossFacetRayAffineRRTerminal
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# Coordinate-normalise a balance-free cross-facet ray

`CrossFacetRayData` is intrinsically generic in its contact coordinate, while
the mature affine RationalRigidity consumer is written in the canonical
contact-`0` chart.

This module supplies the missing source-honest adapter.  For a ray with contact
coordinate `j`, swap `j` with coordinate `0`, transport the two actual
source support witnesses through `MvPolynomial.rename`, and run the canonical
finite-support ray extractor again on the renamed source.

No dependent ray record is transported and no support point is invented.
Hessian singularity is carried only by the existing coordinate-permutation
covariance theorem.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Rename the source of an arbitrary balance-free cross-facet ray so its
contact coordinate becomes `0`, then re-extract an honest canonical ray from
the renamed source support. -/
noncomputable def CrossFacetRayData.renameContactToZero
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j) :
    CrossFacetRayData
      (MvPolynomial.rename (Equiv.swap j (0 : Fin 4)) F)
      (0 : Fin 4) := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap j (0 : Fin 4)
  let v : Fin 4 →₀ ℕ := Finsupp.mapDomain rho R.facetExponent
  let o : Fin 4 →₀ ℕ := Finsupp.mapDomain rho R.outsideExponent

  have hvCoeff :
      MvPolynomial.coeff v (MvPolynomial.rename rho F) ≠ 0 := by
    dsimp [v]
    rw [MvPolynomial.coeff_rename_mapDomain
      (rho : Fin 4 → Fin 4) rho.injective]
    exact MvPolynomial.mem_support_iff.mp R.facet_mem_source
  have hoCoeff :
      MvPolynomial.coeff o (MvPolynomial.rename rho F) ≠ 0 := by
    dsimp [o]
    rw [MvPolynomial.coeff_rename_mapDomain
      (rho : Fin 4 → Fin 4) rho.injective]
    exact MvPolynomial.mem_support_iff.mp R.outside_mem_source

  have hvMem :
      v ∈ (MvPolynomial.rename rho F).support :=
    MvPolynomial.mem_support_iff.mpr hvCoeff
  have hoMem :
      o ∈ (MvPolynomial.rename rho F).support :=
    MvPolynomial.mem_support_iff.mpr hoCoeff

  have hv0 : v (0 : Fin 4) = 0 := by
    dsimp [v]
    rw [Finsupp.mapDomain_equiv_apply]
    simpa [rho] using R.facet_coordinate_zero
  have ho0 : 0 < o (0 : Fin 4) := by
    dsimp [o]
    rw [Finsupp.mapDomain_equiv_apply]
    simpa [rho] using R.outside_coordinate_pos

  have hfacet :
      (zeroCoordinateSupport (0 : Fin 4)
        (MvPolynomial.rename rho F)).Nonempty :=
    ⟨v, mem_zeroCoordinateSupport.mpr ⟨hvMem, hv0⟩⟩
  have hout :
      (positiveCoordinateSupport (0 : Fin 4)
        (MvPolynomial.rename rho F)).Nonempty :=
    ⟨o, mem_positiveCoordinateSupport.mpr ⟨hoMem, ho0⟩⟩

  simpa [rho] using
    (crossFacetRayData (K := K) hfacet hout)

/-- Hessian singularity is preserved by the source permutation used by
`renameContactToZero`. -/
theorem CrossFacetRayData.renameContactToZero_hessian_zero
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    (hzero : hessianDeterminant F = 0) :
    hessianDeterminant
      (MvPolynomial.rename (Equiv.swap j (0 : Fin 4)) F) = 0 := by
  rw [hessianDeterminant_rename_perm]
  rw [hzero]
  simp

/-- **Generic balance-free ray entry to the mature contact-`0` RR
terminal.**  Every arbitrary-contact ray can be source-renamed and re-extracted
so that the existing exact dichotomy applies: a rank-three `.qs` endpoint
with its full affine terminal certificate, or a genuine codimension-two
endpoint.

The result deliberately lives on the renamed source.  Later consumers may use
coordinate covariance to transport only the final polynomial obstruction,
rather than transporting the large ray record itself. -/
theorem CrossFacetRayData.renamedZero_terminalCertificate_or_codimensionTwo
    [IsAlgClosed K]
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    (hzero : hessianDeterminant F = 0) :
    let R0 := R.renameContactToZero
    (MvRankThreeOnFacet .qs R0.facetExponent ∧
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := R0.zeroCoefficientPolynomial)
        ((R0.facetExponent 1 : ℕ) : K)
        ((R0.facetExponent 2 : ℕ) : K)
        ((R0.facetExponent 3 : ℕ) : K)
        (1 : K)
        (R0.zeroSlope (1 : Fin 4))
        (R0.zeroSlope (2 : Fin 4))
        (R0.zeroSlope (3 : Fin 4))) ∨
      MvExponentOnCodimensionTwoBoundary R0.facetExponent := by
  let R0 := R.renameContactToZero
  have hzero0 :
      hessianDeterminant
        (MvPolynomial.rename (Equiv.swap j (0 : Fin 4)) F) = 0 :=
    R.renameContactToZero_hessian_zero hzero
  exact R0.zero_terminalCertificate_or_codimensionTwo hzero0


/-- Compact constructor form of the canonical terminal split.  Packaging the
large dependent certificate once here keeps downstream valuation adapters
cheap to elaborate. -/
inductive CrossFacetRayData.RenamedZeroTerminalOutcome
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j) : Prop
  | rankThree
      (hthree :
        MvRankThreeOnFacet .qs R.renameContactToZero.facetExponent)
      (certificate :
        HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
          (phi := R.renameContactToZero.zeroCoefficientPolynomial)
          ((R.renameContactToZero.facetExponent 1 : ℕ) : K)
          ((R.renameContactToZero.facetExponent 2 : ℕ) : K)
          ((R.renameContactToZero.facetExponent 3 : ℕ) : K)
          (1 : K)
          (R.renameContactToZero.zeroSlope (1 : Fin 4))
          (R.renameContactToZero.zeroSlope (2 : Fin 4))
          (R.renameContactToZero.zeroSlope (3 : Fin 4)))
  | codimensionTwo
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          R.renameContactToZero.facetExponent)

/-- Constructor-valued form of
`renamedZero_terminalCertificate_or_codimensionTwo`. -/
theorem CrossFacetRayData.renamedZeroTerminalOutcome
    [IsAlgClosed K]
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    (hzero : hessianDeterminant F = 0) :
    R.RenamedZeroTerminalOutcome := by
  rcases R.renamedZero_terminalCertificate_or_codimensionTwo hzero with
    hterminal | hcodim
  · exact .rankThree hterminal.1 hterminal.2
  · exact .codimensionTwo hcodim

end

end HC4.Newton
