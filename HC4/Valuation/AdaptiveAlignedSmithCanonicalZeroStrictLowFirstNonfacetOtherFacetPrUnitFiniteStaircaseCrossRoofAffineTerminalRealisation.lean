import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCrossRoofAffineRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCrossRoofTerminalClosure
import HC4.Newton.TerminalCoordinatePermutation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import Mathlib.Tactic

/-!
# Terminal certificates from the source-honest unit cross-roof realisation

The two exact unit coefficient profiles are extracted from one literal singular
source face.  Their endpoint coefficients are nonzero, Hessian singularity is
preserved by the two coordinate permutations, and the generic affine-line
terminal theorem produces the two certificates consumed by the state-free
unit cross-roof contradiction.
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

namespace QsOtherFacetPrUnitLeftExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}

private def terminalHighPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1

private def terminalLowPerm : Equiv.Perm (Fin 4) :=
  terminalHighPerm.trans (Equiv.swap (0 : Fin 4) 2)

@[simp] private theorem terminalHighPerm_symm_zero :
    terminalHighPerm.symm (0 : Fin 4) = 1 := by decide

@[simp] private theorem terminalLowPerm_symm_zero :
    terminalLowPerm.symm (0 : Fin 4) = 2 := by decide

/-- The literal lower source endpoint is the constant term of the forward
coefficient profile. -/
theorem highProfile_coeff_zero_ne
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
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
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
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

private theorem highAffineLine_hessian_zero
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
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

private theorem lowAffineLine_hessian_zero
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
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

/-- Forward affine-line terminal certificate. -/
theorem highTerminalCertificate
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HasRankThreePolynomialTerminalCertificate
      (phi := (E.highSupportData hthree houtThree).coefficientProfile)
      (E.kLo : K) (E.q : K) (E.jLo : K) 1
      ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
      (-((E.q : K) / (E.v : K)))
      ((((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)) := by
  let D := E.highSupportData hthree houtThree
  change HasRankThreePolynomialTerminalCertificate
    (phi := D.coefficientProfile)
    (E.kLo : K) (E.q : K) (E.jLo : K) 1
    ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K))
    (-((E.q : K) / (E.v : K)))
    ((((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K))
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
  simpa only [Nat.cast_one] using
    (hasRankThreePolynomialTerminalCertificate_of_affine_line
      (K := K)
      (A := E.kLo) (B := E.q) (C := E.jLo) (u1 := 1)
      (q := ((((E.jHi + 1 : ℕ) : K) - (E.kLo : K)) / (E.v : K)))
      (r := -((E.q : K) / (E.v : K)))
      (s := ((((E.kHi : K) - 1) - (E.jLo : K)) / (E.v : K)))
      (phi := D.coefficientProfile)
      D.affineLineData
      E.kLo_pos E.q_pos E.jLo_pos (by norm_num)
      hdeg hzero hdet)

/-- Reverse affine-line terminal certificate. -/
theorem lowTerminalCertificate
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HasRankThreePolynomialTerminalCertificate
      (phi := (E.lowSupportData hthree houtThree).coefficientProfile)
      ((E.jHi + 1 : ℕ) : K) (E.v : K)
      ((E.kHi - 1 : ℕ) : K) 1
      (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
      (-((E.v : K) / (E.q : K)))
      (((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K)) := by
  let D := E.lowSupportData hthree houtThree
  change HasRankThreePolynomialTerminalCertificate
    (phi := D.coefficientProfile)
    ((E.jHi + 1 : ℕ) : K) (E.v : K)
    ((E.kHi - 1 : ℕ) : K) 1
    (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K))
    (-((E.v : K) / (E.q : K)))
    (((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K))
  have hkLoOne : 1 ≤ E.kLo := E.kLo_pos
  have hOneLtKHi : 1 < E.kHi := lt_of_le_of_lt hkLoOne E.pair_lt
  have hkHiSub : 0 < E.kHi - 1 := Nat.sub_pos_of_lt hOneLtKHi
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
  simpa only [Nat.cast_one] using
    (hasRankThreePolynomialTerminalCertificate_of_affine_line
      (K := K)
      (A := E.jHi + 1) (B := E.v) (C := E.kHi - 1) (u1 := 1)
      (q := (((E.kLo : K) - ((E.jHi + 1 : ℕ) : K)) / (E.q : K)))
      (r := -((E.v : K) / (E.q : K)))
      (s := (((E.jLo : K) - ((E.kHi : K) - 1)) / (E.q : K)))
      (phi := D.coefficientProfile)
      D.affineLineData
      (Nat.succ_pos E.jHi) E.v_pos hkHiSub (by norm_num)
      hdeg hzero hdet)

/-- The actual exposed unit cross-roof source face is impossible. -/
theorem impossible
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
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

end QsOtherFacetPrUnitLeftExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
