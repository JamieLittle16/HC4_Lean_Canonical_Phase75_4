import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisPotentialTiming
import HC4.Valuation.AdaptiveAlignedSmithAxisPreservingQuadraticNormalization
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerSupport
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingCanonicalSquareLattice
import Mathlib.Tactic

/-!
# Aligned fresh square at marked-axis potential closing

At exact closing of the honest marked-axis first-contact potential family,
the first actual source layer has nonzero quadratic curvature.  The generic
axis-preserving source-shear theorem moves that curvature to a square on a
transverse coordinate while preserving the marked collision.

Because the parameter-zero marked-axis fibre is a homogeneous degree-D slice
with D >= 3, it has no quadratic source monomials.  Because the selected layer
is the first positive actual layer, every positive coefficient below it also
vanishes.  Hence the aligned square is genuinely fresh and has exact parameter
order equal to the marked-axis Hessian defect.

This is potential-level data throughout; no Schur polynomial is identified
with a potential.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

structure TopKernelMarkedAxisAlignedFreshSquareData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  k : Fin 4
  ell : Fin 4
  a : K
  k_ne_ell : k ≠ ell
  ell_ne_zero : ell ≠ (0 : Fin 4)
  squareCoeff_zero :
    (MvPolynomial.coeff
      (Finsupp.single ell 1 + Finsupp.single ell 1)
      (transverseSourceShearHom
        (K := K) k ell (Polynomial.C a)
        T.topKernelMarkedAxisFirstContactFamily)).coeff 0 = 0
  squareCoeff_closing_ne :
    (MvPolynomial.coeff
      (Finsupp.single ell 1 + Finsupp.single ell 1)
      (transverseSourceShearHom
        (K := K) k ell (Polynomial.C a)
        T.topKernelMarkedAxisFirstContactFamily)).coeff
      T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0
  squareCoeff_lower_zero :
    ∀ n : ℕ, 0 < n →
      n < T.topKernelMarkedAxisFirstActualLayerOrder →
      (MvPolynomial.coeff
        (Finsupp.single ell 1 + Finsupp.single ell 1)
        (transverseSourceShearHom
          (K := K) k ell (Polynomial.C a)
          T.topKernelMarkedAxisFirstContactFamily)).coeff n = 0
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      (transverseSourceShearHom
        (K := K) k ell (Polynomial.C a)
        T.topKernelMarkedAxisFirstContactFamily)
      (4 * T.topFace.degree - 6)
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      (transverseSourceShearHom
        (K := K) k ell (Polynomial.C a)
        T.topKernelMarkedAxisFirstContactFamily)
      (zeroPolynomialSection (K := K))
      (transverseSourceUnshearSection
        k ell (Polynomial.C a)
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))))
  rightSpecialPoint :
    polynomialSectionSpecialPoint
      (transverseSourceUnshearSection
        k ell (Polynomial.C a)
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4)))) =
      coordinateAxisPoint (K := K) (0 : Fin 4)

namespace TopKernelMarkedAxisAlignedFreshSquareData

noncomputable def family
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  transverseSourceShearHom
    (K := K) D.k D.ell (Polynomial.C D.a)
    T.topKernelMarkedAxisFirstContactFamily

noncomputable def rightSection
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Fin 4 → Polynomial K :=
  transverseSourceUnshearSection
    D.k D.ell (Polynomial.C D.a)
    (polynomialConstantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4)))

def squareExponent
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Fin 4 →₀ ℕ :=
  Finsupp.single D.ell 1 + Finsupp.single D.ell 1

theorem squareSupport
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    D.squareExponent ∈ D.family.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  apply D.squareCoeff_closing_ne
  have h :=
    congrArg
      (fun p : Polynomial K =>
        p.coeff T.topKernelMarkedAxisFirstActualLayerOrder) hz
  simpa [family, squareExponent] using h

theorem squareExactOrder
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    smithFamilyCoefficientParameterOrder
        D.family D.squareExponent D.squareSupport =
      T.topKernelMarkedAxisFirstActualLayerOrder := by
  let q :=
    smithFamilyCoefficientParameterOrder
      D.family D.squareExponent D.squareSupport
  have hqle :
      q ≤ T.topKernelMarkedAxisFirstActualLayerOrder := by
    apply polynomialParameterOrder_le_of_coeff_ne_zero
      (MvPolynomial.coeff D.squareExponent D.family)
      (MvPolynomial.mem_support_iff.mp D.squareSupport)
    simpa [q, smithFamilyCoefficientParameterOrder,
      family, squareExponent] using D.squareCoeff_closing_ne
  have hqcoeff :
      (MvPolynomial.coeff D.squareExponent D.family).coeff q ≠ 0 := by
    simpa [q, smithFamilyCoefficientParameterOrder] using
      polynomialParameterOrder_coeff_ne_zero
        (MvPolynomial.coeff D.squareExponent D.family)
        (MvPolynomial.mem_support_iff.mp D.squareSupport)
  have hjle :
      T.topKernelMarkedAxisFirstActualLayerOrder ≤ q := by
    by_contra hnot
    have hqlt : q < T.topKernelMarkedAxisFirstActualLayerOrder :=
      Nat.lt_of_not_ge hnot
    by_cases hq0 : q = 0
    · subst q
      apply hqcoeff
      simpa [family, squareExponent] using D.squareCoeff_zero
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      apply hqcoeff
      simpa [family, squareExponent] using
        D.squareCoeff_lower_zero q hqpos hqlt
  exact Nat.le_antisymm hqle hjle

/-- The inverse source shear fixes the marked constant section exactly.
This is stronger than the special-point statement stored in the package and
removes the moving-section divisibility gate from the canonical square
exposure. -/
theorem rightSection_eq_markedConstantSection
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    D.rightSection =
      polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  funext i
  unfold rightSection transverseSourceUnshearSection polynomialConstantSection
  by_cases hik : i = D.k
  · subst i
    have hell0 : D.ell ≠ (0 : Fin 4) := D.ell_ne_zero
    simp [D.k_ne_ell, hell0, coordinateAxisPoint]
  · simp [hik, coordinateAxisPoint]

/-- The old direct-closing canonical square weight has zero weight on the
distinguished fresh square in the new marked-axis package as well. -/
theorem canonicalSquareWeight_squareExponent
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Finsupp.weight
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell)
        D.squareExponent = 0 := by
  simp [squareExponent, directClosingCanonicalSquareWeight,
    Finsupp.weight_single]

/-- Ramifying and pulling back the marked right section is automatically
integral for the canonical square weight: coordinate zero has weight zero,
and every other coordinate of the section is the zero polynomial. -/
theorem canonicalSquare_rightSectionIntegrality
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    HasIntegralAdaptiveSmithSection
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell)
      (parameterRamificationSection
        (K := K) directClosingCanonicalSquareRamification D.rightSection) := by
  rw [D.rightSection_eq_markedConstantSection]
  intro i
  by_cases hi : i = (0 : Fin 4)
  · subst i
    simp [parameterRamificationSection, polynomialConstantSection,
      coordinateAxisPoint]
  · have hz :
        parameterRamificationSection
            (K := K) directClosingCanonicalSquareRamification
            (polynomialConstantSection
              (coordinateAxisPoint (K := K) (0 : Fin 4))) i = 0 := by
      simp [parameterRamificationSection, polynomialConstantSection,
        coordinateAxisPoint, hi]
    rw [hz]
    exact dvd_zero _

/-- At exact marked-axis Hessian closing the fresh square lies exactly on the
canonical terminal level.  Thus the section gate and the contact arithmetic
are fully discharged; only family coefficient integrality remains. -/
theorem canonicalSquare_contactLevel_of_eq_defect
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    directClosingCanonicalSquareRamification *
          T.topKernelMarkedAxisFirstActualLayerOrder +
        Finsupp.weight
          (directClosingCanonicalSquareWeight
            (4 * T.topFace.degree - 6) D.ell)
          D.squareExponent =
      directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6) := by
  rw [D.canonicalSquareWeight_squareExponent, heq]
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel]

end TopKernelMarkedAxisAlignedFreshSquareData

/-- At exact marked-axis determinant closing, one honest axis-preserving
source shear produces a fresh transverse square of exact closing order while
retaining the exact Hessian clock and marked collision. -/
theorem topKernelMarkedAxis_exists_alignedFreshSquare_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    Nonempty T.TopKernelMarkedAxisAlignedFreshSquareData := by
  let P := T.topKernelMarkedAxisFirstContactFamily
  let j := T.topKernelMarkedAxisFirstActualLayerOrder
  have hH :
      quadraticFamilyHessianMatrix (familyParameterLayer P j) ≠ 0 := by
    simpa [P, j] using
      T.topKernelMarkedAxisFirstActualLayer_originHessian_ne_zero_of_eq_defect heq
  rcases exists_axisPreservingShear_layerTransverseDiagonal_ne_zero
      (K := K) P j hH with
    ⟨k, ell, a, hkl, hell0, hdiagj⟩
  let Q :=
    transverseSourceShearHom
      (K := K) k ell (Polynomial.C a) P
  let d : Fin 4 →₀ ℕ :=
    Finsupp.single ell 1 + Finsupp.single ell 1

  have hbase0 :
      ∀ r s : Fin 4,
        (quadraticFamilyHessianMatrix P r s).coeff 0 = 0 := by
    intro r s
    rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    rw [familyParameterLayer_zero_eq_polynomialFamilySpecialFiber]
    rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
    have hz :
        MvPolynomial.coeff
          (Finsupp.single s 1 + Finsupp.single r 1)
          (polynomialFamilySpecialFiber P) = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      simpa [P] using
        T.topKernelMarkedAxisFirstContact_specialFiber_no_quadratic r s
    rw [hz]
    simp

  have hdiag0 :
      (quadraticFamilyHessianMatrix Q ell ell).coeff 0 = 0 := by
    dsimp [Q]
    rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
      k ell hkl a P 0]
    simp [hbase0]

  have hbaseLower :
      ∀ n : ℕ, 0 < n → n < j →
        ∀ r s : Fin 4,
          (quadraticFamilyHessianMatrix P r s).coeff n = 0 := by
    intro n hnpos hnlt r s
    rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    have hlayer :
        familyParameterLayer P n = 0 := by
      apply familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
        P T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer hnpos
      simpa [P, j, topKernelMarkedAxisFirstActualLayerOrder] using hnlt
    rw [hlayer]
    simp [quadraticFamilyHessianMatrix]

  have hdiagLower :
      ∀ n : ℕ, 0 < n → n < j →
        (quadraticFamilyHessianMatrix Q ell ell).coeff n = 0 := by
    intro n hnpos hnlt
    dsimp [Q]
    rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
      k ell hkl a P n]
    simp [hbaseLower n hnpos hnlt]

  have hdiagSquare
      (n : ℕ) :
      (quadraticFamilyHessianMatrix Q ell ell).coeff n =
        (MvPolynomial.coeff d Q).coeff n * (2 : K) := by
    rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
    rw [familyParameterLayer_coeff]
    simp [d]
    ring

  have hsquare0 :
      (MvPolynomial.coeff d Q).coeff 0 = 0 := by
    have h := hdiagSquare 0
    rw [hdiag0] at h
    have htwo : (2 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h.symm).resolve_right htwo

  have hsquarej :
      (MvPolynomial.coeff d Q).coeff j ≠ 0 := by
    intro hz
    apply hdiagj
    have h := hdiagSquare j
    rw [hz] at h
    simpa [Q, P, j] using h

  have hsquareLower :
      ∀ n : ℕ, 0 < n → n < j →
        (MvPolynomial.coeff d Q).coeff n = 0 := by
    intro n hnpos hnlt
    have h := hdiagSquare n
    rw [hdiagLower n hnpos hnlt] at h
    have htwo : (2 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h.symm).resolve_right htwo

  have hdef :
      HasPolynomialFamilyHessianDefect (K := K) Q
        (4 * T.topFace.degree - 6) := by
    dsimp [Q, P]
    exact transverseSourceShearHom_preservesHessianDefect
      (K := K) k ell hkl (Polynomial.C a)
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasHessianDefect

  let right :=
    transverseSourceUnshearSection
      k ell (Polynomial.C a)
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)))

  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        Q (zeroPolynomialSection (K := K)) right := by
    have h :=
      polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) k ell hkl (Polynomial.C a)
        P
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4)))
        T.topKernelMarkedAxisFirstContact_exactGradientCollision
    simpa [Q, P, right, transverseSourceUnshearSection_zero] using h

  have hright :
      polynomialSectionSpecialPoint right =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    have hell :
        polynomialSectionSpecialPoint
          (polynomialConstantSection
            (coordinateAxisPoint (K := K) (0 : Fin 4))) ell = 0 := by
      simp [polynomialSectionSpecialPoint, polynomialConstantSection,
        coordinateAxisPoint, hell0]
    have h :=
      polynomialSectionSpecialPoint_transverseUnshear_of_addedCoord_zero
        (K := K) k ell a
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))) hell
    simpa [right, polynomialSectionSpecialPoint, polynomialConstantSection] using h

  refine ⟨{
    k := k
    ell := ell
    a := a
    k_ne_ell := hkl
    ell_ne_zero := hell0
    squareCoeff_zero := ?_
    squareCoeff_closing_ne := ?_
    squareCoeff_lower_zero := ?_
    hessianDefect := ?_
    exactCollision := ?_
    rightSpecialPoint := ?_
  }⟩
  · simpa [Q, P, d] using hsquare0
  · simpa [Q, P, d, j] using hsquarej
  · intro n hnpos hnlt
    simpa [Q, P, d, j] using hsquareLower n hnpos hnlt
  · simpa [Q, P] using hdef
  · simpa [Q, P, right] using hcoll
  · simpa [right] using hright

/-- Timing frontier with the exact-closing branch upgraded from a bare
quadratic coefficient to the fully aligned fresh-square source package. -/
inductive TopKernelMarkedAxisAlignedSquareTimingFrontier
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | preclosing
      (order_lt :
        T.topKernelMarkedAxisFirstActualLayerOrder <
          4 * T.topFace.degree - 6)
  | exactClosing
      (order_eq :
        T.topKernelMarkedAxisFirstActualLayerOrder =
          4 * T.topFace.degree - 6)
      (square : T.TopKernelMarkedAxisAlignedFreshSquareData)

/-- The honest marked-axis potential always reaches either strict preclosing,
or an exact-closing source which already carries the aligned fresh square,
the exact Hessian clock and the marked moving collision. -/
theorem topKernelMarkedAxisAlignedSquareTimingFrontier_nonempty
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.TopKernelMarkedAxisAlignedSquareTimingFrontier := by
  rcases T.topKernelMarkedAxisPotentialTimingFrontier_nonempty with
    F
  rcases F with ⟨F⟩
  cases F with
  | preclosing hlt =>
      exact ⟨.preclosing hlt⟩
  | exactClosingQuadratic heq _i _k _hcoeff =>
      rcases T.topKernelMarkedAxis_exists_alignedFreshSquare_of_eq_defect heq with
        ⟨D⟩
      exact ⟨.exactClosing heq D⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
