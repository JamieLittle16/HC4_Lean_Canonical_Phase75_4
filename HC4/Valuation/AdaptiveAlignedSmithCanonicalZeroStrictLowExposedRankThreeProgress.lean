import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowLosslessFinalGeometryFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankThreeProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import HC4.Polynomial.MonomialHessianPrincipalMinor
import Mathlib.Tactic

/-!
# Canonical exposed rank-three boundary already gives actual source rank two

The balance-free A19 boundary vertex is not an arbitrary supported monomial.
It is obtained by four successive coordinate-maximal exact initial forms, and
the final face is literally one monomial.

If that canonical exposed exponent is rank three on any coordinate facet,
three source coordinates occur positively in the exposed monomial. Any two
of them give a nonzero principal Hessian minor of the monomial. Exact
initial-form covariance lifts that minor back through all four coordinate-max
exposures to the singular maximal ordinary top face, and then through the
ordinary top-face extraction to the represented determinant-one special
fibre.

Thus every rank-three constructor of the lossless strict-low frontier already
carries an actual represented-state rank-two Hessian chart and hence the
existing geometry-backed global rank-three successor. The only genuine
lossless residual is the codimension-two exposed boundary case.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem rankThree_exists_two_positive
    {d : Fin 4 →₀ ℕ}
    (facet : ToricFacet)
    (hthree : MvRankThreeOnFacet facet d) :
    ∃ i j : Fin 4, i ≠ j ∧ 0 < d i ∧ 0 < d j := by
  have h := (mvRankThreeOnFacet_iff facet d).1 hthree
  cases facet with
  | pr =>
      exact ⟨(0 : Fin 4), (2 : Fin 4), by decide, h.2.1, h.2.2.1⟩
  | rq =>
      exact ⟨(0 : Fin 4), (1 : Fin 4), by decide, h.2.1, h.2.2.1⟩
  | qs =>
      exact ⟨(1 : Fin 4), (2 : Fin 4), by decide, h.2.1, h.2.2.1⟩
  | sp =>
      exact ⟨(0 : Fin 4), (1 : Fin 4), by decide, h.2.1, h.2.2.1⟩

/-- The canonical four-coordinate exposed rank-three monomial forces a
nonzero principal Hessian minor already on the original singular source.

The proof deliberately reconstructs the exact coordinate-max chain used by
the canonical exposed vertex; no arbitrary exposed-vertex record is assumed
to carry provenance which it does not store. -/
theorem exposedSingularNonlinearBoundaryVertex_rankThree_sourcePrincipalMinor
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    (facet : ToricFacet)
    (hthree :
      MvRankThreeOnFacet facet
        (exposedSingularNonlinearBoundaryVertex
          F hF hzero hnonlinear).exponent) :
    ∃ i j : Fin 4,
      i ≠ j ∧ HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
  let E :=
    exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : HC4.Polynomial.hessianDeterminant D0.face = 0 := D0.hessian_zero hzero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : HC4.Polynomial.hessianDeterminant D1.face = 0 := D1.hessian_zero h0zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : HC4.Polynomial.hessianDeterminant D2.face = 0 := D2.hessian_zero h1zero
  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  have hthreeE : MvRankThreeOnFacet facet E.exponent := by
    simpa [E] using hthree
  rcases rankThree_exists_two_positive facet hthreeE with
    ⟨i, j, hij, hi, hj⟩

  have hmono :
      D3.face = MvPolynomial.monomial E.exponent E.coeff := by
    rw [D3.face_eq]
    exact E.exposed

  have hminor3 :
      HC4.Polynomial.hessianPrincipalMinor D3.face i j ≠ 0 := by
    rw [hmono]
    exact HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      E.coeff_ne_zero hij hi hj

  have hminor2 :
      HC4.Polynomial.hessianPrincipalMinor D2.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D3.weight_bound i j
    simpa [D3.face_eq] using hminor3

  have hminor1 :
      HC4.Polynomial.hessianPrincipalMinor D1.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D2.weight_bound i j
    simpa [D2.face_eq] using hminor2

  have hminor0 :
      HC4.Polynomial.hessianPrincipalMinor D0.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D1.weight_bound i j
    simpa [D1.face_eq] using hminor1

  have hminorF :
      HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D0.weight_bound i j
    simpa [D0.face_eq] using hminor0

  exact ⟨i, j, hij, hminorF⟩

/-- Two positive coordinates in the canonical exposed monomial are already
enough to force a nonzero principal Hessian minor on the original singular
source.  This is the rank-three lift above with the toric stratum information
removed. -/
theorem exposedSingularNonlinearBoundaryVertex_twoPositive_sourcePrincipalMinor
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hnonlinear :
      ∀ d ∈ F.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    (i j : Fin 4)
    (hij : i ≠ j)
    (hi :
      0 < (exposedSingularNonlinearBoundaryVertex
        F hF hzero hnonlinear).exponent i)
    (hj :
      0 < (exposedSingularNonlinearBoundaryVertex
        F hF hzero hnonlinear).exponent j) :
    HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
  let E :=
    exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : HC4.Polynomial.hessianDeterminant D0.face = 0 :=
    D0.hessian_zero hzero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : HC4.Polynomial.hessianDeterminant D1.face = 0 :=
    D1.hessian_zero h0zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : HC4.Polynomial.hessianDeterminant D2.face = 0 :=
    D2.hessian_zero h1zero
  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  have hiE : 0 < E.exponent i := by simpa [E] using hi
  have hjE : 0 < E.exponent j := by simpa [E] using hj

  have hmono :
      D3.face = MvPolynomial.monomial E.exponent E.coeff := by
    rw [D3.face_eq]
    exact E.exposed

  have hminor3 :
      HC4.Polynomial.hessianPrincipalMinor D3.face i j ≠ 0 := by
    rw [hmono]
    exact HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      E.coeff_ne_zero hij hiE hjE

  have hminor2 :
      HC4.Polynomial.hessianPrincipalMinor D2.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D3.weight_bound i j
    simpa [D3.face_eq] using hminor3

  have hminor1 :
      HC4.Polynomial.hessianPrincipalMinor D1.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D2.weight_bound i j
    simpa [D2.face_eq] using hminor2

  have hminor0 :
      HC4.Polynomial.hessianPrincipalMinor D0.face i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D1.weight_bound i j
    simpa [D1.face_eq] using hminor1

  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    D0.weight_bound i j
  simpa [D0.face_eq] using hminor0

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A rank-three canonical A19 boundary exponent already supplies an actual
principal Hessian minor on the represented determinant-one special fibre. -/
theorem exposedRankThree_actualRankTwoHessianChart
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree :
      MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  have hthree' :
      MvRankThreeOnFacet facet
        (exposedSingularNonlinearBoundaryVertex
          T.topFace.face
          T.topFace.face_ne_zero
          T.topFace.hessian_zero
          T.topFace.face_support_degree_ge_three).exponent := by
    simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.exposedSingularBoundaryVertex]
      using hthree

  rcases exposedSingularNonlinearBoundaryVertex_rankThree_sourcePrincipalMinor
      T.topFace.face_ne_zero
      T.topFace.hessian_zero
      T.topFace.face_support_degree_ge_three
      facet hthree' with
    ⟨i, j, hij, hminorTop⟩

  let source :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family

  have hweight :
      HC4.Polynomial.IsWeightLE
        (fun _ : Fin 4 => (1 : ℤ))
        (T.topFace.degree : ℤ)
        source := by
    intro d hd
    change
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d ≤
        (T.topFace.degree : ℤ)
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast T.topFace.maximal d hd

  have hminorSource :
      HC4.Polynomial.hessianPrincipalMinor source i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      hweight i j
    simpa [source, T.topFace.face_eq] using hminorTop

  exact
    ⟨actualRankTwoHessianChart_of_specialFiber_minor hij hminorSource⟩

/-- Literal pure-axis form of the canonical exposed nonlinear boundary
monomial. -/
structure ExposedPureAxisResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  axis : Fin 4
  axis_pos : 0 < T.exposedSingularBoundaryVertex.exponent axis
  other_zero :
    ∀ i : Fin 4, i ≠ axis →
      T.exposedSingularBoundaryVertex.exponent i = 0

/-- Any two positive coordinates of the canonical exposed boundary monomial
give an actual rank-two Hessian chart on the represented source. -/
theorem exposedTwoPositive_actualRankTwoHessianChart
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4)
    (hij : i ≠ j)
    (hi : 0 < T.exposedSingularBoundaryVertex.exponent i)
    (hj : 0 < T.exposedSingularBoundaryVertex.exponent j) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  have hi' :
      0 < (exposedSingularNonlinearBoundaryVertex
        T.topFace.face
        T.topFace.face_ne_zero
        T.topFace.hessian_zero
        T.topFace.face_support_degree_ge_three).exponent i := by
    simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.exposedSingularBoundaryVertex]
      using hi
  have hj' :
      0 < (exposedSingularNonlinearBoundaryVertex
        T.topFace.face
        T.topFace.face_ne_zero
        T.topFace.hessian_zero
        T.topFace.face_support_degree_ge_three).exponent j := by
    simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.exposedSingularBoundaryVertex]
      using hj
  have hminorTop :=
    exposedSingularNonlinearBoundaryVertex_twoPositive_sourcePrincipalMinor
      T.topFace.face_ne_zero
      T.topFace.hessian_zero
      T.topFace.face_support_degree_ge_three
      i j hij hi' hj'

  let source :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  have hweight :
      HC4.Polynomial.IsWeightLE
        (fun _ : Fin 4 => (1 : ℤ))
        (T.topFace.degree : ℤ)
        source := by
    intro d hd
    change
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d ≤
        (T.topFace.degree : ℤ)
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast T.topFace.maximal d hd
  have hminorSource :
      HC4.Polynomial.hessianPrincipalMinor source i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      hweight i j
    simpa [source, T.topFace.face_eq] using hminorTop
  exact
    ⟨actualRankTwoHessianChart_of_specialFiber_minor hij hminorSource⟩

/-- **Canonical boundary rank reduction.**  Without any toric case split, the
actual exposed nonlinear boundary monomial either already gives represented
rank-two Hessian geometry or is literally supported on one coordinate axis. -/
theorem exposedBoundary_actualRankTwo_or_pureAxis
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty T.ExposedPureAxisResidual := by
  classical
  let d := T.exposedSingularBoundaryVertex.exponent
  by_cases htwo :
      ∃ i j : Fin 4, i ≠ j ∧ 0 < d i ∧ 0 < d j
  · rcases htwo with ⟨i, j, hij, hi, hj⟩
    left
    exact T.exposedTwoPositive_actualRankTwoHessianChart
      i j hij (by simpa [d] using hi) (by simpa [d] using hj)
  · have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
      simpa [d] using T.exposedBoundary_exponent_degree_ge_three
    have hpos :
        0 < d (0 : Fin 4) ∨ 0 < d (1 : Fin 4) ∨
          0 < d (2 : Fin 4) ∨ 0 < d (3 : Fin 4) := by
      unfold HC4.Polynomial.ordinaryDegree4 at hdeg
      omega
    have pureAt (a : Fin 4) (ha : 0 < d a) :
        ∀ i : Fin 4, i ≠ a → d i = 0 := by
      intro i hia
      by_contra hne
      have hi : 0 < d i := Nat.pos_of_ne_zero hne
      exact htwo ⟨a, i, hia.symm, ha, hi⟩
    right
    rcases hpos with h0 | h1 | h2 | h3
    · exact ⟨{
        axis := (0 : Fin 4)
        axis_pos := by simpa [d] using h0
        other_zero := by
          intro i hi
          simpa [d] using pureAt (0 : Fin 4) h0 i hi
      }⟩
    · exact ⟨{
        axis := (1 : Fin 4)
        axis_pos := by simpa [d] using h1
        other_zero := by
          intro i hi
          simpa [d] using pureAt (1 : Fin 4) h1 i hi
      }⟩
    · exact ⟨{
        axis := (2 : Fin 4)
        axis_pos := by simpa [d] using h2
        other_zero := by
          intro i hi
          simpa [d] using pureAt (2 : Fin 4) h2 i hi
      }⟩
    · exact ⟨{
        axis := (3 : Fin 4)
        axis_pos := by simpa [d] using h3
        other_zero := by
          intro i hi
          simpa [d] using pureAt (3 : Fin 4) h3 i hi
      }⟩

/-- Strongest current local/global reduction: the honest strict-low terminal
either has a geometry-backed global rank-three successor or its canonical
exposed nonlinear boundary monomial is a literal pure-axis power. -/
theorem globalRankThreeProgress_or_pureAxisResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) ∨
      Nonempty T.ExposedPureAxisResidual := by
  rcases T.exposedBoundary_actualRankTwo_or_pureAxis with hactual | hpure
  · rcases hactual with ⟨A⟩
    exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)
  · exact Or.inr hpure

/-- The final residual after consuming the canonical exposed rank-three
boundary geometry. -/
structure LosslessCodimensionTwoResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  boundary :
    MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent
  geometry : T.ExposedCodimensionTwoResolvedRankTwoGeometry

/-- Every lossless constructor carrying a rank-three proof is immediately
genuine global progress through the actual represented-state Hessian chart.
The only remaining local object is the resolved codimension-two boundary
geometry. -/
theorem globalRankThreeProgress_or_codimensionTwoResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) ∨
      Nonempty T.LosslessCodimensionTwoResidual := by
  cases T.losslessFinalGeometryFrontier with
  | topBoundaryTransition facet rankThree _transition =>
      rcases T.exposedRankThree_actualRankTwoHessianChart facet rankThree with
        ⟨A⟩
      exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)

  | lowerBoundaryTransition facet rankThree _C _transition =>
      rcases T.exposedRankThree_actualRankTwoHessianChart facet rankThree with
        ⟨A⟩
      exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)

  | codimensionTwo hcodim geometry =>
      exact Or.inr ⟨⟨hcodim, geometry⟩⟩

  | quadraticSquare facet rankThree _d _mem _degree_two _omitted_two _pure =>
      rcases T.exposedRankThree_actualRankTwoHessianChart facet rankThree with
        ⟨A⟩
      exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)

  | nonlinearConfined facet rankThree _confined =>
      rcases T.exposedRankThree_actualRankTwoHessianChart facet rankThree with
        ⟨A⟩
      exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
