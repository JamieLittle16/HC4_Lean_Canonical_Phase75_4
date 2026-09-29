import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisAlignedFreshSquare

/-!
# Canonical square lattice for the zero-strict-low marked-axis family

At exact marked-axis Hessian closing the preceding module produces an honest
source-equivalent polynomial family with

* exact Hessian defect `4D - 6`;
* the marked exact moving collision;
* a fresh transverse square of exact first-actual-layer order; and
* an automatically integral marked right section for the canonical square
  source weight.

This file packages the only remaining arithmetic gate: coefficientwise
integrality of the polynomial family itself.  Thus exact closing reduces to a
finite dichotomy between an honest canonical square exposure and one explicit
family coefficient which fails the divisibility inequality.

No JC2 input occurs.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Family-integrality certificate for the canonical square exposure attached
to the new marked-axis fresh-square package.  The moving-section gate is not a
field because it is already automatic. -/
structure TopKernelMarkedAxisCanonicalSquareIntegralityData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Prop where
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure
      directClosingCanonicalSquareRamification
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell)
      (directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6))
      D.family

/-- Explicit failure of the sole remaining canonical square gate. -/
structure TopKernelMarkedAxisCanonicalSquareFamilyObstruction
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  exponent : Fin 4 →₀ ℕ
  mem_family : exponent ∈ D.family.support
  not_divisible :
    ¬ Polynomial.X ^
        (directClosingCanonicalSquareCommonLevel
          (4 * T.topFace.degree - 6)) ∣
      adaptiveSmithExposureCoefficientFactor
        directClosingCanonicalSquareRamification
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell)
        D.family exponent

/-- The canonical marked-axis square has exactly one arithmetic gate left:
either all family coefficients are integrally exposed, or one supported
coefficient explicitly witnesses failure. -/
theorem topKernelMarkedAxisCanonicalSquare_integral_or_obstruction
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) ∨
      Nonempty (T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) := by
  classical
  by_cases h :
      HasIntegralAdaptiveSmithExposure
        directClosingCanonicalSquareRamification
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell)
        (directClosingCanonicalSquareCommonLevel
          (4 * T.topFace.degree - 6))
        D.family
  · exact Or.inl ⟨⟨h⟩⟩
  · right
    unfold HasIntegralAdaptiveSmithExposure at h
    push_neg at h
    rcases h with ⟨d, hd, hnot⟩
    exact ⟨{
      exponent := d
      mem_family := hd
      not_divisible := hnot
    }⟩

namespace TopKernelMarkedAxisCanonicalSquareFamilyObstruction

variable
  {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
    (K := K) state}
  {D : T.TopKernelMarkedAxisAlignedFreshSquareData}

/-- Failure of family integrality is equivalent to a genuinely earlier
weighted coefficient clock on the canonical square ray. -/
theorem strictEarlierWeightedClock
    (O : T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) :
    directClosingCanonicalSquareRamification *
          smithFamilyCoefficientParameterOrder
            D.family O.exponent O.mem_family +
        Finsupp.weight
          (directClosingCanonicalSquareWeight
            (4 * T.topFace.degree - 6) D.ell)
          O.exponent <
      directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6) := by
  let q :=
    smithFamilyCoefficientParameterOrder
      D.family O.exponent O.mem_family
  let w :=
    Finsupp.weight
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell)
      O.exponent
  let total := directClosingCanonicalSquareRamification * q + w
  have hqdiv :
      Polynomial.X ^ q ∣ MvPolynomial.coeff O.exponent D.family := by
    simpa [q] using
      smithFamilyCoefficientParameterOrder_dvd
        D.family O.exponent O.mem_family
  have hramdiv :
      Polynomial.X ^
          (directClosingCanonicalSquareRamification * q) ∣
        parameterRamificationHom (K := K)
          directClosingCanonicalSquareRamification
          (MvPolynomial.coeff O.exponent D.family) := by
    exact parameterRamification_pow_dvd
      directClosingCanonicalSquareRamification q
      (MvPolynomial.coeff O.exponent D.family) hqdiv
  rcases hramdiv with ⟨r, hr⟩
  have htotaldiv :
      Polynomial.X ^ total ∣
        adaptiveSmithExposureCoefficientFactor
          directClosingCanonicalSquareRamification
          (directClosingCanonicalSquareWeight
            (4 * T.topFace.degree - 6) D.ell)
          D.family O.exponent := by
    refine ⟨r, ?_⟩
    unfold adaptiveSmithExposureCoefficientFactor
    dsimp [total, w]
    rw [hr, pow_add]
    ring
  change total <
    directClosingCanonicalSquareCommonLevel
      (4 * T.topFace.degree - 6)
  by_contra hlt
  have hle :
      directClosingCanonicalSquareCommonLevel
          (4 * T.topFace.degree - 6) ≤ total :=
    Nat.le_of_not_gt hlt
  have hpow :
      Polynomial.X ^
          (directClosingCanonicalSquareCommonLevel
            (4 * T.topFace.degree - 6)) ∣
        (Polynomial.X : Polynomial K) ^ total :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6))
      total hle
  exact O.not_divisible (dvd_trans hpow htotaldiv)

/-- In particular the offending coefficient occurs strictly before the
marked-axis determinant-closing order. -/
theorem parameterOrder_lt_defect
    (O : T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) :
    smithFamilyCoefficientParameterOrder
        D.family O.exponent O.mem_family <
      4 * T.topFace.degree - 6 := by
  have hlt := O.strictEarlierWeightedClock
  have hw :
      0 ≤ Finsupp.weight
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell)
        O.exponent := Nat.zero_le _
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel] at hlt
  omega

/-- Every family obstruction is therefore either already on the special
fibre (order zero) or is a genuine positive parameter layer strictly before
the closing clock. -/
theorem zeroOrder_or_positiveEarlier
    (O : T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) :
    smithFamilyCoefficientParameterOrder
        D.family O.exponent O.mem_family = 0 ∨
      (0 <
          smithFamilyCoefficientParameterOrder
            D.family O.exponent O.mem_family ∧
        smithFamilyCoefficientParameterOrder
            D.family O.exponent O.mem_family <
          4 * T.topFace.degree - 6) := by
  let q :=
    smithFamilyCoefficientParameterOrder
      D.family O.exponent O.mem_family
  by_cases hq : q = 0
  · exact Or.inl hq
  · exact Or.inr ⟨Nat.pos_of_ne_zero hq,
      by simpa [q] using O.parameterOrder_lt_defect⟩

end TopKernelMarkedAxisCanonicalSquareFamilyObstruction

namespace TopKernelMarkedAxisCanonicalSquareIntegralityData

variable
  {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
    (K := K) state}
  {D : T.TopKernelMarkedAxisAlignedFreshSquareData}

/-- Honest adaptive Smith exposure selected by the canonical marked-axis square
arithmetic. -/
noncomputable def exposedFamily
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    directClosingCanonicalSquareRamification
    (directClosingCanonicalSquareWeight
      (4 * T.topFace.degree - 6) D.ell)
    (directClosingCanonicalSquareCommonLevel
      (4 * T.topFace.degree - 6))
    D.family G.familyIntegrality

/-- Integral left section of the canonical square exposure. -/
noncomputable def leftSection
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection
    (directClosingCanonicalSquareWeight
      (4 * T.topFace.degree - 6) D.ell)
    (parameterRamificationSection
      (K := K) directClosingCanonicalSquareRamification
      (zeroPolynomialSection (K := K)))
    (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K)
      directClosingCanonicalSquareRamification
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell))

/-- Integral right section.  Its divisibility is the automatic theorem proved
for the marked-axis fresh-square package. -/
noncomputable def rightSection
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection
    (directClosingCanonicalSquareWeight
      (4 * T.topFace.degree - 6) D.ell)
    (parameterRamificationSection
      (K := K) directClosingCanonicalSquareRamification D.rightSection)
    D.canonicalSquare_rightSectionIntegrality

/-- Exact transformed Hessian clock of the canonical square exposure. -/
theorem exposedFamily_hasHessianDefect
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) :
    HasPolynomialFamilyHessianDefect (K := K)
      G.exposedFamily 0 := by
  have hnonneg :
      4 * directClosingCanonicalSquareCommonLevel
          (4 * T.topFace.degree - 6) ≤
        directClosingCanonicalSquareRamification *
            (4 * T.topFace.degree - 6) +
          2 * ∑ i : Fin 4,
            directClosingCanonicalSquareWeight
              (4 * T.topFace.degree - 6) D.ell i := by
    rw [directClosingCanonicalSquare_terminalArithmetic]
  have hdef :=
    adaptiveSmithFirstContactExposureFamily_hasHessianDefect
      directClosingCanonicalSquareRamification
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell)
      (directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6))
      (4 * T.topFace.degree - 6)
      directClosingCanonicalSquareRamification_pos
      hnonneg D.family G.familyIntegrality D.hessianDefect
  simpa [exposedFamily,
    directClosingCanonicalSquare_terminalArithmetic] using hdef

/-- The exact marked collision survives the honest canonical square exposure. -/
theorem exposedFamily_exactCollision
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D) :
    HasPolynomialFamilyExactGradientCollision
      G.exposedFamily G.leftSection G.rightSection := by
  have hram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      directClosingCanonicalSquareRamification
      D.family
      (zeroPolynomialSection (K := K))
      D.rightSection
      D.exactCollision
  exact
    polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      directClosingCanonicalSquareRamification
      (directClosingCanonicalSquareWeight
        (4 * T.topFace.degree - 6) D.ell)
      (directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6))
      directClosingCanonicalSquareRamification_pos
      D.family G.familyIntegrality
      (parameterRamificationSection
        (K := K) directClosingCanonicalSquareRamification
        (zeroPolynomialSection (K := K)))
      (parameterRamificationSection
        (K := K) directClosingCanonicalSquareRamification D.rightSection)
      (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
        (K := K)
        directClosingCanonicalSquareRamification
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell))
      D.canonicalSquare_rightSectionIntegrality
      hram

end TopKernelMarkedAxisCanonicalSquareIntegralityData

/-- **Exact marked-axis closing -> honest canonical exposure or one finite
family obstruction.**

This is the downstream-facing form: choose the aligned fresh square supplied
at exact closing, discharge the section gate automatically, and retain either
the honest defect-zero collision family or one explicit coefficient failure. -/
theorem topKernelMarkedAxisCanonicalSquareExposure_or_obstruction_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    (∃ (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
        (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D),
        HasPolynomialFamilyHessianDefect (K := K) G.exposedFamily 0 ∧
          HasPolynomialFamilyExactGradientCollision
            G.exposedFamily G.leftSection G.rightSection) ∨
      (∃ D : T.TopKernelMarkedAxisAlignedFreshSquareData,
        Nonempty (T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D)) := by
  let D := Classical.choice
    (T.topKernelMarkedAxis_exists_alignedFreshSquare_of_eq_defect heq)
  rcases T.topKernelMarkedAxisCanonicalSquare_integral_or_obstruction D with
    hG | hobs
  · rcases hG with ⟨G⟩
    left
    exact ⟨D, G, G.exposedFamily_hasHessianDefect,
      G.exposedFamily_exactCollision⟩
  · right
    exact ⟨D, hobs⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
