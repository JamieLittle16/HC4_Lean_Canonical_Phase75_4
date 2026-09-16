import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofAffineRealisation
import HC4.Newton.TerminalCoordinatePermutation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import Mathlib.Tactic

/-!
# Terminal certificates from the source-honest cross-roof realisation

The previous adapter constructs the two exact coefficient profiles and proves
their degrees are the two literal cross-roof residuals.  This file keeps the
remaining closure deliberately thin: preserve the actual endpoint
coefficients under the same coordinate permutations, transport Hessian
singularity, invoke the generic affine-line terminal theorem twice, and feed
the resulting certificates to the already-verified cross-roof terminal
closure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open HC4.RationalRigidity

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}

/-- The same forward permutation used by the source-realisation adapter. -/
private def terminalHighPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1

/-- The same reverse three-cycle, written as the requested elementary swaps. -/
private def terminalLowPerm : Equiv.Perm (Fin 4) :=
  terminalHighPerm.trans (Equiv.swap (0 : Fin 4) 2)

@[simp] private theorem terminalHighPerm_symm_zero :
    terminalHighPerm.symm (0 : Fin 4) = 1 := by decide

@[simp] private theorem terminalLowPerm_symm_zero :
    terminalLowPerm.symm (0 : Fin 4) = 2 := by decide

/-- The literal lower source endpoint is the constant term of the forward
coefficient profile. -/
theorem highProfile_coeff_zero_ne
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (E.highSupportData hthree houtThree).coefficientProfile.coeff 0 ≠ 0 := by
  classical
  let D := E.highSupportData hthree houtThree
  let e0 : Fin 4 →₀ ℕ :=
    Finsupp.mapDomain terminalHighPerm E.hull.lo
  refine D.coeff_zero_ne_zero_of_mem_zero (e := e0) ?_ ?_
  · change e0 ∈
      (MvPolynomial.rename terminalHighPerm E.hull.face).support
    rw [MvPolynomial.support_rename_of_injective terminalHighPerm.injective]
    exact Finset.mem_image.mpr ⟨E.hull.lo, E.hull.lo_mem_face, rfl⟩
  · dsimp [e0]
    simpa only [Finsupp.mapDomain_equiv_apply,
      terminalHighPerm_symm_zero] using E.hull.lo_one_zero

/-- The literal high source endpoint is the constant term of the reversed
coefficient profile. -/
theorem lowProfile_coeff_zero_ne
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (E.lowSupportData hthree houtThree).coefficientProfile.coeff 0 ≠ 0 := by
  classical
  let D := E.lowSupportData hthree houtThree
  let e0 : Fin 4 →₀ ℕ :=
    Finsupp.mapDomain terminalLowPerm E.hi
  refine D.coeff_zero_ne_zero_of_mem_zero (e := e0) ?_ ?_
  · change e0 ∈
      (MvPolynomial.rename terminalLowPerm E.hull.face).support
    rw [MvPolynomial.support_rename_of_injective terminalLowPerm.injective]
    exact Finset.mem_image.mpr ⟨E.hi, E.hi_mem_face, rfl⟩
  · dsimp [e0]
    simpa only [Finsupp.mapDomain_equiv_apply,
      terminalLowPerm_symm_zero] using E.hi_two_zero

/-- Hessian singularity of the actual exposed source face survives the forward
coordinate permutation and literal affine-line reconstruction. -/
private theorem highAffineLine_hessian_zero
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianDeterminant
      (E.highSupportData hthree houtThree).affineLineData.polynomial = 0 := by
  let D := E.highSupportData hthree houtThree
  rw [D.affineLineData_polynomial_eq]
  change HC4.Polynomial.hessianDeterminant
    (MvPolynomial.rename terminalHighPerm E.hull.face) = 0
  rw [HC4.Newton.hessianDeterminant_rename_perm]
  rw [E.hull.face_hessian_zero]
  simp

/-- Hessian singularity of the same source face survives the reverse
coordinate permutation and reconstruction. -/
private theorem lowAffineLine_hessian_zero
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianDeterminant
      (E.lowSupportData hthree houtThree).affineLineData.polynomial = 0 := by
  let D := E.lowSupportData hthree houtThree
  rw [D.affineLineData_polynomial_eq]
  change HC4.Polynomial.hessianDeterminant
    (MvPolynomial.rename terminalLowPerm E.hull.face) = 0
  rw [HC4.Newton.hessianDeterminant_rename_perm]
  rw [E.hull.face_hessian_zero]
  simp

/-- Forward affine-line terminal certificate, retaining the literal lower roof
as its positive rank-three base endpoint. -/
theorem highTerminalCertificate
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HasRankThreePolynomialTerminalCertificate
      (phi := (E.highSupportData hthree houtThree).coefficientProfile)
      (E.kLo : K) (E.q : K) ((F.V * E.jLo : ℕ) : K) 1
      ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
      (-((E.q : K) / (E.v : K)))
      ((F.V : K) * (((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)) := by
  let D := E.highSupportData hthree houtThree
  change HasRankThreePolynomialTerminalCertificate
    (phi := D.coefficientProfile)
    (E.kLo : K) (E.q : K) ((F.V * E.jLo : ℕ) : K) 1
    ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
    (-((E.q : K) / (E.v : K)))
    ((F.V : K) * (((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K))
  have hVgt : 1 < F.V := F.V_gt_one
  have hV : 0 < F.V := by omega
  have hC : 0 < F.V * E.jLo := Nat.mul_pos hV E.jLo_pos
  have hdegEq : D.coefficientProfile.natDegree = E.v := by
    change (E.highSupportData hthree houtThree).coefficientProfile.natDegree = E.v
    exact E.highProfile_natDegree hthree houtThree
  have hdeg : 0 < D.coefficientProfile.natDegree := by
    rw [hdegEq]
    exact E.v_pos
  have hzero : D.coefficientProfile.coeff 0 ≠ 0 := by
    change (E.highSupportData hthree houtThree).coefficientProfile.coeff 0 ≠ 0
    exact E.highProfile_coeff_zero_ne hthree houtThree
  have hdet :
      HC4.Polynomial.hessianDeterminant D.affineLineData.polynomial = 0 := by
    change HC4.Polynomial.hessianDeterminant
      (E.highSupportData hthree houtThree).affineLineData.polynomial = 0
    exact E.highAffineLine_hessian_zero hthree houtThree
  exact hasRankThreePolynomialTerminalCertificate_of_affine_line
    (K := K)
    (A := E.kLo) (B := E.q) (C := F.V * E.jLo) (u1 := 1)
    (q := ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K)))
    (r := -((E.q : K) / (E.v : K)))
    (s := ((F.V : K) * (((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)))
    (phi := D.coefficientProfile)
    D.affineLineData
    E.kLo_pos E.q_pos hC (by norm_num)
    hdeg hzero hdet

/-- Reverse affine-line terminal certificate, retaining the literal high roof
as its positive rank-three base endpoint. -/
theorem lowTerminalCertificate
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HasRankThreePolynomialTerminalCertificate
      (phi := (E.lowSupportData hthree houtThree).coefficientProfile)
      ((E.jHi + 1 : ℕ) : K) (E.v : K)
      ((F.V * (E.kHi - 1) : ℕ) : K) 1
      (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
      (-((E.v : K) / (E.q : K)))
      ((F.V : K) * ((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K)) := by
  let D := E.lowSupportData hthree houtThree
  change HasRankThreePolynomialTerminalCertificate
    (phi := D.coefficientProfile)
    ((E.jHi + 1 : ℕ) : K) (E.v : K)
    ((F.V * (E.kHi - 1) : ℕ) : K) 1
    (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
    (-((E.v : K) / (E.q : K)))
    ((F.V : K) * ((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K))
  have hVgt : 1 < F.V := F.V_gt_one
  have hV : 0 < F.V := by omega
  have hkLoOne : 1 ≤ E.kLo := by omega
  have hOneLtKHi : 1 < E.kHi := lt_of_le_of_lt hkLoOne E.pair_lt
  have hkHiSub : 0 < E.kHi - 1 := Nat.sub_pos_of_lt hOneLtKHi
  have hC : 0 < F.V * (E.kHi - 1) := Nat.mul_pos hV hkHiSub
  have hdegEq : D.coefficientProfile.natDegree = E.q := by
    change (E.lowSupportData hthree houtThree).coefficientProfile.natDegree = E.q
    exact E.lowProfile_natDegree hthree houtThree
  have hdeg : 0 < D.coefficientProfile.natDegree := by
    rw [hdegEq]
    exact E.q_pos
  have hzero : D.coefficientProfile.coeff 0 ≠ 0 := by
    change (E.lowSupportData hthree houtThree).coefficientProfile.coeff 0 ≠ 0
    exact E.lowProfile_coeff_zero_ne hthree houtThree
  have hdet :
      HC4.Polynomial.hessianDeterminant D.affineLineData.polynomial = 0 := by
    change HC4.Polynomial.hessianDeterminant
      (E.lowSupportData hthree houtThree).affineLineData.polynomial = 0
    exact E.lowAffineLine_hessian_zero hthree houtThree
  exact hasRankThreePolynomialTerminalCertificate_of_affine_line
    (K := K)
    (A := E.jHi + 1) (B := E.v) (C := F.V * (E.kHi - 1)) (u1 := 1)
    (q := (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K)))
    (r := -((E.v : K) / (E.q : K)))
    (s := ((F.V : K) * ((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K)))
    (phi := D.coefficientProfile)
    D.affineLineData
    (Nat.succ_pos E.jHi) E.v_pos hC (by norm_num)
    hdeg hzero hdet

/-- **The actual exposed cross-roof source face is impossible.**

This is the end-to-end source-honest exposed branch: the two profiles are
extracted from the same literal singular face, their exact degrees are the two
roof residuals, and their generic affine-line terminal certificates feed the
already-verified arithmetic closure directly. -/
theorem impossible
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    False := by
  exact E.impossible_of_terminalCertificates
    hthree houtThree
    (E.highProfile_natDegree hthree houtThree)
    (E.highProfile_coeff_zero_ne hthree houtThree)
    (E.highTerminalCertificate hthree houtThree)
    (E.lowProfile_natDegree hthree houtThree)
    (E.lowProfile_coeff_zero_ne hthree houtThree)
    (E.lowTerminalCertificate hthree houtThree)

end QsOtherFacetPrLeftVExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
