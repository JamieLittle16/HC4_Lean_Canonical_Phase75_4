import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisAlignedFreshSquare
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareZeroOrderFamilyWallShape
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareWallFaceCurvature
import HC4.Valuation.AdaptiveAlignedSmithCanonicalLowDimensionalStationaryConvergence
import HC4.Valuation.AdaptiveAlignedSmithCanonicalLowDimensionalPlanarAffineNormalForm
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCore
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCurvedElimination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTerminalNormalForm
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingOriginPencil

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

/-- Residue-field source transvection corresponding to the constant
parameter source shear. -/
def topKernelMarkedAxisTransverseShearVariableBase
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    MvPolynomial (Fin 4) K :=
  if i = k then
    MvPolynomial.X k + MvPolynomial.C a * MvPolynomial.X ell
  else
    MvPolynomial.X i

/-- Residue-field ring homomorphism induced by the same source transvection. -/
noncomputable def topKernelMarkedAxisTransverseShearHomBase
    (k ell : Fin 4) (a : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (topKernelMarkedAxisTransverseShearVariableBase k ell a)

@[simp] theorem topKernelMarkedAxisTransverseShearHomBase_C
    (k ell : Fin 4) (a c : K) :
    topKernelMarkedAxisTransverseShearHomBase k ell a (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [topKernelMarkedAxisTransverseShearHomBase]

@[simp] theorem topKernelMarkedAxisTransverseShearHomBase_X
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    topKernelMarkedAxisTransverseShearHomBase k ell a (MvPolynomial.X i) =
      topKernelMarkedAxisTransverseShearVariableBase k ell a i := by
  simp [topKernelMarkedAxisTransverseShearHomBase]

/-- Away from the added direction, the residue-field marked-axis shear has
the identity chain rule. -/
theorem pderiv_topKernelMarkedAxisTransverseShearHomBase_of_ne_added
    (k ell : Fin 4) (hkl : k ≠ ell) (a : K)
    (j : Fin 4) (hjl : j ≠ ell)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv j
        (topKernelMarkedAxisTransverseShearHomBase k ell a P) =
      topKernelMarkedAxisTransverseShearHomBase k ell a
        (MvPolynomial.pderiv j P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp only [map_mul, topKernelMarkedAxisTransverseShearHomBase_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnk : n = k
    · subst n
      by_cases hkj : k = j
      · subst j
        simp [topKernelMarkedAxisTransverseShearVariableBase, hkl] <;> ring
      · have hjk : j ≠ k := Ne.symm hkj
        simp [topKernelMarkedAxisTransverseShearVariableBase,
          hkl, hkj, hjk, hjl] <;> ring
    · by_cases hnj : n = j
      · subst n
        have hjk : j ≠ k := by
          intro h
          exact hnk h
        simp [topKernelMarkedAxisTransverseShearVariableBase,
          hnk, hjk, hjl] <;> ring
      · have hjn : j ≠ n := Ne.symm hnj
        simp [topKernelMarkedAxisTransverseShearVariableBase,
          hnk, hnj, hjn, hjl] <;> ring

/-- Taking an exact parameter layer commutes with a source shear whose
coefficient is parameter-constant.  This is the layerwise analogue of the
already-used special-fibre transport theorem. -/
theorem familyParameterLayer_transverseSourceShearHom_constant
    (k ell : Fin 4) (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    familyParameterLayer
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P) n =
      topKernelMarkedAxisTransverseShearHomBase k ell a
        (familyParameterLayer P n) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [familyParameterLayer,
      topKernelMarkedAxisTransverseShearHomBase]
  · intro p q hp hq
    simpa [familyParameterLayer, map_add] using
      congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    have hvar :
        familyParameterLayer
            (transverseSourceShearHom (K := K) k ell (Polynomial.C a)
              (MvPolynomial.X i)) n =
          topKernelMarkedAxisTransverseShearHomBase k ell a
            (familyParameterLayer (MvPolynomial.X i) n) := by
      by_cases hn : n = 0
      · subst n
        by_cases hi : i = k
        · subst i
          simp [familyParameterLayer,
            transverseSourceShearHom,
            transverseSourceShearVariable,
            topKernelMarkedAxisTransverseShearHomBase,
            topKernelMarkedAxisTransverseShearVariableBase]
        · simp [familyParameterLayer,
            transverseSourceShearHom,
            transverseSourceShearVariable,
            topKernelMarkedAxisTransverseShearHomBase,
            topKernelMarkedAxisTransverseShearVariableBase, hi]
      · by_cases hi : i = k
        · subst i
          simp [familyParameterLayer,
            transverseSourceShearHom,
            transverseSourceShearVariable,
            topKernelMarkedAxisTransverseShearHomBase,
            topKernelMarkedAxisTransverseShearVariableBase, hn]
        · simp [familyParameterLayer,
            transverseSourceShearHom,
            transverseSourceShearVariable,
            topKernelMarkedAxisTransverseShearHomBase,
            topKernelMarkedAxisTransverseShearVariableBase, hi, hn]
    have hmul := congrArg₂ (fun x y => x * y) hp hvar
    simpa [familyParameterLayer, map_mul] using hmul

/-- The aligned fresh-square family inherits the gap before the marked first
actual layer: constant source shearing cannot create an earlier parameter
layer. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.familyParameterLayer_eq_zero_of_pos_lt_firstActual
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
    {n : ℕ}
    (hnpos : 0 < n)
    (hnlt : n < T.topKernelMarkedAxisFirstActualLayerOrder) :
    familyParameterLayer D.family n = 0 := by
  rw [familyParameterLayer_transverseSourceShearHom_constant]
  have hzero :=
    familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
      hnpos
      (by
        simpa [topKernelMarkedAxisFirstActualLayerOrder] using hnlt)
  rw [hzero]
  simp [topKernelMarkedAxisTransverseShearHomBase]

/-- Every residue-field shear variable is an ordinary linear form. -/
theorem topKernelMarkedAxisTransverseShearVariableBase_isHomogeneous_one
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    (topKernelMarkedAxisTransverseShearVariableBase k ell a i).IsHomogeneous 1 := by
  by_cases hik : i = k
  · subst i
    unfold topKernelMarkedAxisTransverseShearVariableBase
    simp only [if_pos rfl]
    exact
      (MvPolynomial.isHomogeneous_X K k).add
        (MvPolynomial.isHomogeneous_C_mul_X a ell)
  · unfold topKernelMarkedAxisTransverseShearVariableBase
    rw [if_neg hik]
    exact MvPolynomial.isHomogeneous_X K i

/-- The residue-field constant source transvection preserves ordinary source
homogeneity. -/
theorem topKernelMarkedAxisTransverseShearHomBase_isHomogeneous
    {d : ℕ}
    (k ell : Fin 4) (a : K)
    (P : MvPolynomial (Fin 4) K)
    (hP : P.IsHomogeneous d) :
    (topKernelMarkedAxisTransverseShearHomBase k ell a P).IsHomogeneous d := by
  have hout :=
    hP.eval₂
      MvPolynomial.C
      (topKernelMarkedAxisTransverseShearVariableBase k ell a)
      (fun r => MvPolynomial.isHomogeneous_C (Fin 4) r)
      (fun i =>
        topKernelMarkedAxisTransverseShearVariableBase_isHomogeneous_one
          k ell a i)
  simpa [topKernelMarkedAxisTransverseShearHomBase] using hout

/-- The unsheared marked-axis special fibre is ordinarily homogeneous of the
maximal top-face degree. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_isHomogeneous
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (polynomialFamilySpecialFiber
      T.topKernelMarkedAxisFirstContactFamily).IsHomogeneous
        T.topFace.degree := by
  unfold MvPolynomial.IsHomogeneous MvPolynomial.IsWeightedHomogeneous
  intro d hcoeff
  have hd :
      d ∈ (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have htop :=
    (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero d).1 hd
  have hdeg := T.topFace.ordinaryDegree_eq_of_mem_support htop.1
  simpa [HC4.Polynomial.ordinaryDegree4,
    Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four] using hdeg

/-- Exact special-fibre transport for the aligned fresh-square family. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.specialFiber_eq_baseShear
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    polynomialFamilySpecialFiber D.family =
      topKernelMarkedAxisTransverseShearHomBase D.k D.ell D.a
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) := by
  rw [← familyParameterLayer_zero_eq_polynomialFamilySpecialFiber,
    ← familyParameterLayer_zero_eq_polynomialFamilySpecialFiber]
  simpa [TopKernelMarkedAxisAlignedFreshSquareData.family] using
    familyParameterLayer_transverseSourceShearHom_constant
      D.k D.ell D.a T.topKernelMarkedAxisFirstContactFamily 0

/-- The aligned marked-axis special fibre remains independent of the marked
coordinate.  The added shear direction is transverse, so the marked partial
derivative commutes with the residue-field source transvection. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.specialFiber_pderiv_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    MvPolynomial.pderiv (0 : Fin 4)
        (polynomialFamilySpecialFiber D.family) = 0 := by
  rw [D.specialFiber_eq_baseShear]
  rw [pderiv_topKernelMarkedAxisTransverseShearHomBase_of_ne_added
    D.k D.ell D.k_ne_ell D.a (0 : Fin 4) D.ell_ne_zero]
  rw [T.topKernelMarkedAxisFirstContact_specialFiber_pderiv_zero]
  simp

/-- Consequently every actual monomial of the aligned special fibre has zero
marked exponent. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.specialFiber_exponent_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ (polynomialFamilySpecialFiber D.family).support) :
    d (0 : Fin 4) = 0 := by
  exact exponent_eq_zero_of_pderiv_eq_zero
    (0 : Fin 4)
    (polynomialFamilySpecialFiber D.family)
    D.specialFiber_pderiv_zero
    d
    (MvPolynomial.mem_support_iff.mp hd)

/-- Hence the aligned fresh-square special fibre remains ordinarily
homogeneous of degree `T.topFace.degree`. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.specialFiber_isHomogeneous
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    (polynomialFamilySpecialFiber D.family).IsHomogeneous T.topFace.degree := by
  rw [D.specialFiber_eq_baseShear]
  exact
    topKernelMarkedAxisTransverseShearHomBase_isHomogeneous
      D.k D.ell D.a
      (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily)
      T.topKernelMarkedAxisFirstContact_specialFiber_isHomogeneous

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

/-- At exact marked-axis closing the positive-earlier obstruction branch is
impossible: constant source shear preserves the complete gap below the first
actual layer.  Hence every failed canonical square coefficient is already
present on the special fibre. -/
theorem parameterOrder_eq_zero_of_eq_defect
    (O : T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    smithFamilyCoefficientParameterOrder
        D.family O.exponent O.mem_family = 0 := by
  rcases O.zeroOrder_or_positiveEarlier with hzero | hpos
  · exact hzero
  · rcases hpos with ⟨hqpos, hqlt⟩
    let q :=
      smithFamilyCoefficientParameterOrder
        D.family O.exponent O.mem_family
    have hq_lt_first :
        q < T.topKernelMarkedAxisFirstActualLayerOrder := by
      rw [heq]
      simpa [q] using hqlt
    have hlayerZero :
        familyParameterLayer D.family q = 0 :=
      D.familyParameterLayer_eq_zero_of_pos_lt_firstActual
        (by simpa [q] using hqpos) hq_lt_first
    have hcoeff :
        (MvPolynomial.coeff O.exponent D.family).coeff q ≠ 0 := by
      simpa [q, smithFamilyCoefficientParameterOrder] using
        polynomialParameterOrder_coeff_ne_zero
          (MvPolynomial.coeff O.exponent D.family)
          (MvPolynomial.mem_support_iff.mp O.mem_family)
    have hlayerCoeff :
        MvPolynomial.coeff O.exponent
            (familyParameterLayer D.family q) ≠ 0 := by
      rw [familyParameterLayer_coeff]
      exact hcoeff
    rw [hlayerZero] at hlayerCoeff
    simp at hlayerCoeff

/-- Canonical square failure after timing reduction is a literal special-fibre
wall: one supported order-zero coefficient lies strictly below the canonical
source-weight level. -/
structure TopKernelMarkedAxisCanonicalSquareZeroOrderWall
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  exponent : Fin 4 →₀ ℕ
  mem_family : exponent ∈ D.family.support
  order_zero :
    smithFamilyCoefficientParameterOrder
      D.family exponent mem_family = 0
  weighted_lt :
    Finsupp.weight
        (directClosingCanonicalSquareWeight
          (4 * T.topFace.degree - 6) D.ell)
        exponent <
      directClosingCanonicalSquareCommonLevel
        (4 * T.topFace.degree - 6)

/-- Every failed family-integrality gate at exact closing yields the concrete
zero-order special-fibre wall above. -/
theorem toZeroOrderWall
    (O : T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) := by
  have hzero := O.parameterOrder_eq_zero_of_eq_defect heq
  have hlt := O.strictEarlierWeightedClock
  rw [hzero] at hlt
  simp only [Nat.mul_zero, zero_add] at hlt
  exact ⟨{
    exponent := O.exponent
    mem_family := O.mem_family
    order_zero := hzero
    weighted_lt := hlt
  }⟩

namespace TopKernelMarkedAxisCanonicalSquareZeroOrderWall

variable
  {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
    (K := K) state}
  {D : T.TopKernelMarkedAxisAlignedFreshSquareData}

/-- Exact parameter order zero means that the offending family monomial lies
on the actual special fibre of the aligned marked-axis family. -/
theorem mem_specialFiber_support
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    W.exponent ∈ (polynomialFamilySpecialFiber D.family).support := by
  rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber]
  have hc : MvPolynomial.coeff W.exponent D.family ≠ 0 :=
    MvPolynomial.mem_support_iff.mp W.mem_family
  have hne :=
    polynomialParameterOrder_coeff_ne_zero
      (MvPolynomial.coeff W.exponent D.family) hc
  have horder :
      polynomialParameterOrder
          (MvPolynomial.coeff W.exponent D.family) hc = 0 := by
    simpa [smithFamilyCoefficientParameterOrder] using W.order_zero
  change (MvPolynomial.coeff W.exponent D.family).coeff 0 ≠ 0
  simpa [horder] using hne

/-- The zero-order wall has no marked longitudinal exponent. -/
theorem markedExponent_zero
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    W.exponent (0 : Fin 4) = 0 :=
  D.specialFiber_exponent_zero W.exponent W.mem_specialFiber_support

/-- The offending order-zero monomial still lies on the degree-`D`
ordinary top layer after the constant source shear. -/
theorem ordinaryDegree_eq_topFaceDegree
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    HC4.Polynomial.ordinaryDegree4 W.exponent = T.topFace.degree := by
  have hhom := D.specialFiber_isHomogeneous
  have hdegree :=
    hhom (MvPolynomial.mem_support_iff.mp W.mem_specialFiber_support)
  simpa [HC4.Polynomial.ordinaryDegree4,
    Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four] using hdegree

/-- A zero-order marked-axis canonical square wall is supported in transverse
complementary degree at most one.  Thus, apart from the square axis itself,
at most one unit of transverse degree can survive. -/
theorem complementDegree_le_one
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
        D.ell W.exponent ≤ 1 := by
  have hDelta : 0 < 4 * T.topFace.degree - 6 := by
    have hD := T.topFace.degree_ge_three
    omega
  have hweight := W.weighted_lt
  rw [AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingCanonicalSquareWeight_transverse
      (4 * T.topFace.degree - 6) D.ell D.ell_ne_zero W.exponent] at hweight
  by_contra hnot
  have hdeg :
      2 ≤
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
          D.ell W.exponent := by
    omega
  have hmul :
      (3 * (4 * T.topFace.degree - 6)) * 2 ≤
        (3 * (4 * T.topFace.degree - 6)) *
          AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
            D.ell W.exponent :=
    Nat.mul_le_mul_left (3 * (4 * T.topFace.degree - 6)) hdeg
  have h6 :
      6 * (4 * T.topFace.degree - 6) ≤
        3 * (4 * T.topFace.degree - 6) *
          AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
            D.ell W.exponent := by
    calc
      6 * (4 * T.topFace.degree - 6) =
          (3 * (4 * T.topFace.degree - 6)) * 2 := by ring
      _ ≤ _ := hmul
  have h46 :
      4 * (4 * T.topFace.degree - 6) <
        6 * (4 * T.topFace.degree - 6) := by
    omega
  simp [directClosingCanonicalSquareCommonLevel] at hweight
  omega


/-- Exact finite shape of the remaining zero-order wall.  Since the
marked exponent is zero, the total degree is `D`, and at most one unit of
degree lies away from the fresh-square axis, the wall monomial is either the
pure axis power or one adjacent linear departure. -/
theorem pureAxis_or_singleComplement
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    W.exponent = Finsupp.single D.ell T.topFace.degree ∨
      ∃ r : Fin 4,
        r ≠ (0 : Fin 4) ∧ r ≠ D.ell ∧
          W.exponent =
            Finsupp.single D.ell (T.topFace.degree - 1) +
              Finsupp.single r 1 := by
  have h0 := W.markedExponent_zero
  have hdeg := W.ordinaryDegree_eq_topFaceDegree
  have hcomp := W.complementDegree_le_one
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  fin_cases hEll : D.ell
  · exact (D.ell_ne_zero hEll).elim
  · have hsum : W.exponent 2 + W.exponent 3 ≤ 1 := by
      simpa [hEll,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree,
        Fin.sum_univ_four] using hcomp
    by_cases h2 : W.exponent (2 : Fin 4) = 0
    · by_cases h3 : W.exponent (3 : Fin 4) = 0
      · left
        ext i
        fin_cases i <;>
          simp [hEll, h0, h2, h3, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg ⊢ <;> omega
      · right
        refine ⟨(3 : Fin 4), by decide, ?_, ?_⟩
        · simpa [hEll]
        · ext i
          fin_cases i <;>
            simp [hEll, h0, h2, HC4.Polynomial.ordinaryDegree4,
              Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega
    · right
      refine ⟨(2 : Fin 4), by decide, ?_, ?_⟩
      · simpa [hEll]
      · ext i
        fin_cases i <;>
          simp [hEll, h0, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega
  · have hsum : W.exponent 1 + W.exponent 3 ≤ 1 := by
      simpa [hEll,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree,
        Fin.sum_univ_four] using hcomp
    by_cases h1 : W.exponent (1 : Fin 4) = 0
    · by_cases h3 : W.exponent (3 : Fin 4) = 0
      · left
        ext i
        fin_cases i <;>
          simp [hEll, h0, h1, h3, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg ⊢ <;> omega
      · right
        refine ⟨(3 : Fin 4), by decide, ?_, ?_⟩
        · simpa [hEll]
        · ext i
          fin_cases i <;>
            simp [hEll, h0, h1, HC4.Polynomial.ordinaryDegree4,
              Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega
    · right
      refine ⟨(1 : Fin 4), by decide, ?_, ?_⟩
      · simpa [hEll]
      · ext i
        fin_cases i <;>
          simp [hEll, h0, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega
  · have hsum : W.exponent 1 + W.exponent 2 ≤ 1 := by
      simpa [hEll,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree,
        Fin.sum_univ_four] using hcomp
    by_cases h1 : W.exponent (1 : Fin 4) = 0
    · by_cases h2 : W.exponent (2 : Fin 4) = 0
      · left
        ext i
        fin_cases i <;>
          simp [hEll, h0, h1, h2, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg ⊢ <;> omega
      · right
        refine ⟨(2 : Fin 4), by decide, ?_, ?_⟩
        · simpa [hEll]
        · ext i
          fin_cases i <;>
            simp [hEll, h0, h1, HC4.Polynomial.ordinaryDegree4,
              Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega
    · right
      refine ⟨(1 : Fin 4), by decide, ?_, ?_⟩
      · simpa [hEll]
      · ext i
        fin_cases i <;>
          simp [hEll, h0, HC4.Polynomial.ordinaryDegree4,
            Fin.sum_univ_four] at hdeg hsum ⊢ <;> omega

/-- Exact complementary-degree face carried by the surviving zero-order
marked-axis square wall.  Because the square axis is transverse, there is only
the transverse branch of the older canonical-wall face construction. -/
structure TopKernelMarkedAxisCanonicalSquareZeroOrderWallFaceData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  wall : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D
  complementDegree : ℕ
  complementDegree_eq :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
      D.ell wall.exponent = complementDegree
  complementDegree_le_one : complementDegree ≤ 1
  face : MvPolynomial (Fin 4) K
  face_eq :
    face =
      HC4.Polynomial.initialForm
        (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
          D.ell)
        (-(complementDegree : ℤ))
        (polynomialFamilySpecialFiber D.family)
  face_ne_zero : face ≠ 0
  support_complementDegree :
    ∀ e ∈ face.support,
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
        D.ell e = complementDegree
  complementHessian_zero :
    ∀ i j : Fin 4,
      i ≠ (0 : Fin 4) → i ≠ D.ell →
      j ≠ (0 : Fin 4) → j ≠ D.ell →
        MvPolynomial.pderiv j (MvPolynomial.pderiv i face) = 0

namespace TopKernelMarkedAxisCanonicalSquareZeroOrderWall

/-- Promote the single offending monomial to the complete exact
complementary-degree initial face containing it. -/
theorem toWallFaceData
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (W : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWall D) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareZeroOrderWallFaceData D) := by
  let m :=
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
      D.ell W.exponent
  let F0 := polynomialFamilySpecialFiber D.family
  let face :=
    HC4.Polynomial.initialForm
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
        D.ell)
      (-(m : ℤ)) F0
  have hweight :
      Finsupp.weight
          (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
            D.ell)
          W.exponent =
        -(m : ℤ) := by
    exact
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.weight_directClosingTransverseComplementWeight
        D.ell W.exponent
  have hface_ne : face ≠ 0 := by
    exact
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.initialForm_ne_zero_of_support_weight
        F0
        (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
          D.ell)
        (-(m : ℤ))
        W.exponent
        W.mem_specialFiber_support
        hweight
  have hsupport :
      ∀ e ∈ face.support,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
          D.ell e = m := by
    intro e he
    exact
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.support_initialForm_transverseComplementDegree_eq
        D.ell F0 m (by simpa [face] using he)
  have hm_le : m ≤ 1 := by
    simpa [m] using W.complementDegree_le_one
  have hsupp_le :
      ∀ e ∈ face.support,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
          D.ell e ≤ 1 := by
    intro e he
    rw [hsupport e he]
    exact hm_le
  have hhess :
      ∀ i j : Fin 4,
        i ≠ (0 : Fin 4) → i ≠ D.ell →
        j ≠ (0 : Fin 4) → j ≠ D.ell →
          MvPolynomial.pderiv j (MvPolynomial.pderiv i face) = 0 := by
    intro i j hi0 hiel hj0 hjel
    exact
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.pderiv_pderiv_eq_zero_of_transverseComplementDegree_le_one
        D.ell face hsupp_le i j hi0 hiel hj0 hjel
  exact ⟨{
    wall := W
    complementDegree := m
    complementDegree_eq := rfl
    complementDegree_le_one := hm_le
    face := face
    face_eq := rfl
    face_ne_zero := hface_ne
    support_complementDegree := hsupport
    complementHessian_zero := hhess
  }⟩

end TopKernelMarkedAxisCanonicalSquareZeroOrderWall

end TopKernelMarkedAxisCanonicalSquareZeroOrderWall

end TopKernelMarkedAxisCanonicalSquareFamilyObstruction

/-- Marked-axis affine/separated refinement of the exact zero-order wall face.
All complementary pure Hessian entries already vanish on the wall face; this
package records that every mixed derivative in a complementary direction
vanishes as well. -/
structure TopKernelMarkedAxisCanonicalSquareAffineSeparatedWallFaceData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  wallFace : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWallFaceData D
  mixed_zero :
    ∀ U V : Fin 4,
      V ≠ (0 : Fin 4) → V ≠ D.ell →
        directionalMixedDerivative U V wallFace.face = 0

/-- **Marked-axis wall-face curvature dichotomy.**

The new zero-order wall face is already the transverse branch of the older
canonical-square face construction.  Hence one nonzero mixed derivative is
immediately the already-green rank-one-to-rank-two repair source.  If no such
mixed derivative exists, retain the complete exact face together with
affine/separated mixed vanishing. -/
theorem TopKernelMarkedAxisCanonicalSquareZeroOrderWallFaceData.mixedRepair_or_affineSeparated
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (F : T.TopKernelMarkedAxisCanonicalSquareZeroOrderWallFaceData D)
    (complexity : ℕ) :
    (∃ (face : MvPolynomial (Fin 4) K) (U V : Fin 4),
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingWallFaceMixedRepairData
        complexity face U V) ∨
      Nonempty (T.TopKernelMarkedAxisCanonicalSquareAffineSeparatedWallFaceData D) := by
  by_cases hmixed :
      ∃ U V : Fin 4,
        V ≠ (0 : Fin 4) ∧ V ≠ D.ell ∧
          directionalMixedDerivative U V F.face ≠ 0
  · rcases hmixed with ⟨U, V, hV0, hVell, hUV⟩
    have hVV : directionalSecondDerivative V F.face = 0 := by
      unfold directionalSecondDerivative
      exact F.complementHessian_zero V V hV0 hVell hV0 hVell
    left
    exact ⟨F.face, U, V,
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingWallFaceMixedRepairData_of_mixed
        complexity F.face U V hVV hUV⟩
  · right
    refine ⟨{
      wallFace := F
      mixed_zero := ?_
    }⟩
    intro U V hV0 hVell
    by_contra hUV
    exact hmixed ⟨U, V, hV0, hVell, hUV⟩

/-- Marked-axis low-dimensional wall face after every possible Hessian
curvature exit has been consumed.  The Hessian is supported on the base plane
spanned by the marked coordinate and the fresh-square coordinate, and its
binary determinant on that plane vanishes. -/
structure TopKernelMarkedAxisCanonicalSquareLowDimensionalWallFaceData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  affine : T.TopKernelMarkedAxisCanonicalSquareAffineSeparatedWallFaceData D
  hessian_support :
    ∀ i j : Fin 4,
      (i ≠ (0 : Fin 4) ∧ i ≠ D.ell) ∨
      (j ≠ (0 : Fin 4) ∧ j ≠ D.ell) →
        HC4.Polynomial.hessian affine.wallFace.face i j = 0
  base_det_zero :
    binaryDirectionalHessianDet (0 : Fin 4) D.ell affine.wallFace.face = 0

/-- **Final marked-axis affine-face curvature dichotomy.**

Once complementary mixed curvature has vanished, the only possible remaining
rank-two source is the intrinsic binary Hessian determinant on the base plane
`(0, ell)`.  A nonzero determinant is the already-green rank-two repair
packet; otherwise the exact wall face is genuinely low-dimensional. -/
theorem TopKernelMarkedAxisCanonicalSquareAffineSeparatedWallFaceData.basePlaneRepair_or_lowDimensional
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (A : T.TopKernelMarkedAxisCanonicalSquareAffineSeparatedWallFaceData D)
    (complexity : ℕ) :
    (∃ (face : MvPolynomial (Fin 4) K) (i j : Fin 4),
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingWallFaceBasePlaneRankTwoRepairData
        complexity face i j) ∨
      Nonempty (T.TopKernelMarkedAxisCanonicalSquareLowDimensionalWallFaceData D) := by
  by_cases hdet :
      binaryDirectionalHessianDet (0 : Fin 4) D.ell A.wallFace.face = 0
  · right
    refine ⟨{
      affine := A
      hessian_support := ?_
      base_det_zero := hdet
    }⟩
    exact
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseAffineWallFace_hessian_support
        D.ell A.wallFace.face A.mixed_zero
  · left
    exact ⟨A.wallFace.face, (0 : Fin 4), D.ell,
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingWallFaceBasePlaneRankTwoRepairData_of_det_ne_zero
        complexity A.wallFace.face (0 : Fin 4) D.ell hdet⟩

/-- Literal affine-gradient form of the surviving marked-axis wall.  Every
gradient component complementary to the base plane is a scalar polynomial. -/
structure TopKernelMarkedAxisCanonicalSquareLowDimensionalGradientData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  low : T.TopKernelMarkedAxisCanonicalSquareLowDimensionalWallFaceData D
  complement_gradient_constant :
    ∀ i : Fin 4,
      i ≠ (0 : Fin 4) → i ≠ D.ell →
        MvPolynomial.pderiv i low.affine.wallFace.face =
          MvPolynomial.C
            (MvPolynomial.coeff 0
              (MvPolynomial.pderiv i low.affine.wallFace.face))

/-- Promote the rank-at-most-one Hessian packet to the same literal
affine-gradient normal form used by the mature low-dimensional stationary
chain. -/
theorem TopKernelMarkedAxisCanonicalSquareLowDimensionalWallFaceData.toGradientData
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquareLowDimensionalWallFaceData D) :
    T.TopKernelMarkedAxisCanonicalSquareLowDimensionalGradientData D := by
  exact {
    low := L
    complement_gradient_constant :=
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseLowDimensional_gradient_constant
        D.ell L.affine.wallFace.face L.hessian_support
  }

/-- Literal planar-affine support normal form for the surviving marked-axis
wall.  Every supported monomial either lies in the base plane `(0, ell)` or
is one pure affine monomial in a complementary variable. -/
structure TopKernelMarkedAxisCanonicalSquarePlanarAffineWallFaceData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  gradient : T.TopKernelMarkedAxisCanonicalSquareLowDimensionalGradientData D
  support_shape :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransversePlanarAffineSupport
      D.ell gradient.low.affine.wallFace.face

/-- Promote the derivative-level marked-axis core to the exact support normal
form used by the mature planar reduction. -/
theorem TopKernelMarkedAxisCanonicalSquareLowDimensionalGradientData.toPlanarAffineData
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquareLowDimensionalGradientData D) :
    T.TopKernelMarkedAxisCanonicalSquarePlanarAffineWallFaceData D := by
  exact {
    gradient := L
    support_shape :=
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transversePlanarAffineSupport_of_gradient_constant
        D.ell L.low.affine.wallFace.face L.complement_gradient_constant
  }

/-- Exact stationary split of the marked-axis planar-affine wall.  Since
the marked-axis construction is always transverse, only the base-plane core
and pure affine-tail constructors are needed. -/
inductive TopKernelMarkedAxisCanonicalSquareStationaryPlanarCoreData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1)
  | transverseCore
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face =
          HC4.Polynomial.initialForm
            (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
              D.ell)
            0
            (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (base_support :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
          D.ell face)
      (base_det_zero :
        binaryDirectionalHessianDet (0 : Fin 4) D.ell face = 0)
  | transverseAffineTail
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face =
          HC4.Polynomial.initialForm
            (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
              D.ell)
            (-1)
            (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (pure_affine :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransversePureAffineSupport
          D.ell face)
      (hessian_zero :
        ∀ i j : Fin 4, HC4.Polynomial.hessian face i j = 0)

/-- The marked-axis planar-affine face is either a genuine degree-zero
base-plane core or completely Hessian-invisible affine noise. -/
theorem TopKernelMarkedAxisCanonicalSquarePlanarAffineWallFaceData.toStationaryPlanarCore
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquarePlanarAffineWallFaceData D) :
    T.TopKernelMarkedAxisCanonicalSquareStationaryPlanarCoreData D := by
  let F := L.gradient.low.affine.wallFace
  have hm_cases : F.complementDegree = 0 ∨ F.complementDegree = 1 := by
    omega
  rcases hm_cases with hzero | hone
  · refine .transverseCore F.face ?_ F.face_ne_zero ?_
      L.gradient.low.base_det_zero
    · rw [F.face_eq, hzero]
      simp
    · intro d hd i hi0 hiell
      rcases L.support_shape d hd with hbase | ⟨k, hk0, hkell, hk⟩
      · exact hbase i hi0 hiell
      · subst d
        have hdeg :=
          AdaptiveAlignedSmithRankOneClosingSourceCarrier.support_initialForm_transverseComplementDegree_eq
            D.ell (polynomialFamilySpecialFiber D.family) 0
            (by
              rw [← F.face_eq, hzero]
              simpa using hd)
        have hone' :
            AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
                D.ell (Finsupp.single k 1) = 1 := by
          have hadd :=
            AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree_add_single
              D.ell k hk0 hkell (0 : Fin 4 →₀ ℕ)
          have hz :
              AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
                  D.ell (0 : Fin 4 →₀ ℕ) = 0 := by
            exact
              AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree_eq_zero_of_baseSupport
                D.ell 0 (by intro r hr0 hrell; simp)
          simpa only [zero_add, hz] using hadd
        omega
  · have hpure :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransversePureAffineSupport
          D.ell F.face := by
      intro d hd
      rcases L.support_shape d hd with hbase | hpure
      · have hdeg :=
          AdaptiveAlignedSmithRankOneClosingSourceCarrier.support_initialForm_transverseComplementDegree_eq
            D.ell (polynomialFamilySpecialFiber D.family) 1
            (by
              rw [← F.face_eq, hone]
              simpa using hd)
        have hz :
            AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree
                D.ell d = 0 :=
          AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementDegree_eq_zero_of_baseSupport
            D.ell d hbase
        omega
      · exact hpure
    refine .transverseAffineTail F.face ?_ F.face_ne_zero hpure ?_
    · rw [F.face_eq, hone]
      norm_num
    · exact
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.transversePureAffine_hessian_zero
          D.ell F.face hpure L.gradient.complement_gradient_constant

/-- Ordinary homogeneity of degree at least three kills every linear
coefficient on the aligned marked-axis special fibre. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.specialFiber_linearCoeff_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (polynomialFamilySpecialFiber D.family) = 0 := by
  apply D.specialFiber_isHomogeneous.coeff_eq_zero
  have hD := T.topFace.degree_ge_three
  simp [Finsupp.degree]
  omega

/-- A pure affine marked-axis wall tail is impossible: its nonzero face would
contain a pure linear monomial, while every linear coefficient of the aligned
special fibre vanishes. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.transverseAffineTail_impossible
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData)
    (face : MvPolynomial (Fin 4) K)
    (face_eq :
      face =
        HC4.Polynomial.initialForm
          (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
            D.ell)
          (-1)
          (polynomialFamilySpecialFiber D.family))
    (face_ne_zero : face ≠ 0)
    (pure_affine :
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransversePureAffineSupport
        D.ell face) :
    False := by
  rcases MvPolynomial.support_nonempty.mpr face_ne_zero with ⟨d, hd⟩
  rcases pure_affine d hd with ⟨i, hi0, hiell, hdi⟩
  subst d
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single i 1) face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [face_eq, HC4.Polynomial.coeff_initialForm] at hcoeff
  have hzero := D.specialFiber_linearCoeff_zero i
  simp [hzero] at hcoeff

/-- Genuine marked-axis planar core after the affine tail has been removed.
Only complementary degree zero survives. -/
structure TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  face : MvPolynomial (Fin 4) K
  face_eq :
    face =
      HC4.Polynomial.initialForm
        (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingTransverseComplementWeight
          D.ell)
        0
        (polynomialFamilySpecialFiber D.family)
  face_ne_zero : face ≠ 0
  base_support :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
      D.ell face
  base_det_zero :
    binaryDirectionalHessianDet (0 : Fin 4) D.ell face = 0

/-- Remove the impossible degree-one affine tail from the marked-axis
stationary split. -/
theorem TopKernelMarkedAxisCanonicalSquareStationaryPlanarCoreData.toZeroJetPlanarCore
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquareStationaryPlanarCoreData D) :
    T.TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData D := by
  cases L with
  | transverseCore face face_eq face_ne_zero base_support base_det_zero =>
      exact {
        face := face
        face_eq := face_eq
        face_ne_zero := face_ne_zero
        base_support := base_support
        base_det_zero := base_det_zero
      }
  | transverseAffineTail face face_eq face_ne_zero pure_affine hessian_zero =>
      exact False.elim
        (D.transverseAffineTail_impossible face face_eq face_ne_zero pure_affine)

/-- Exact binary planarisation of the surviving marked-axis base-plane
core.  Collision orientation is deliberately not stored here: the entire
binary singular-Hessian analysis below is carrier-independent. -/
structure TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) : Type (u + 1) where
  face : MvPolynomial (Fin 4) K
  binaryFace : MvPolynomial (Fin 2) K
  face_eq_rename :
    MvPolynomial.rename
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
        D.ell D.ell_ne_zero)
      binaryFace = face
  face_ne_zero : face ≠ 0
  binaryFace_ne_zero : binaryFace ≠ 0
  binary_det_zero :
    binaryDirectionalHessianDet (0 : Fin 2) 1 binaryFace = 0
  face_linear_zero :
    ∀ i : Fin 4,
      MvPolynomial.coeff (Finsupp.single i 1) face = 0

/-- Every linear coefficient on a marked-axis zero-jet core vanishes. -/
theorem TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData.face_linear_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData D)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1) L.face = 0 := by
  rw [L.face_eq, HC4.Polynomial.coeff_initialForm]
  split
  · exact D.specialFiber_linearCoeff_zero i
  · rfl

/-- Exact binary planarisation of the genuine marked-axis zero-jet core. -/
theorem TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData.toBinaryStationaryCore
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (L : T.TopKernelMarkedAxisCanonicalSquareZeroJetStationaryPlanarCoreData D) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData D) := by
  rcases
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseSupport_exists_binaryPlanarisation
        D.ell_ne_zero L.base_support with
    ⟨Q, hQrename⟩
  have hQne : Q ≠ 0 := by
    intro hQ
    apply L.face_ne_zero
    rw [← hQrename, hQ]
    simp
  have hdetTransport :=
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.binaryDirectionalHessianDet_rename_transverseBaseEmbedding
      D.ell D.ell_ne_zero Q
  have hrenameDet :
      MvPolynomial.rename
          (AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
            D.ell D.ell_ne_zero)
          (binaryDirectionalHessianDet (0 : Fin 2) 1 Q) = 0 := by
    rw [← hdetTransport, hQrename, L.base_det_zero]
  have hdetQ :
      binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0 := by
    apply MvPolynomial.rename_injective
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
        D.ell D.ell_ne_zero)
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
        D.ell D.ell_ne_zero).injective
    simpa using hrenameDet
  exact ⟨{
    face := L.face
    binaryFace := Q
    face_eq_rename := hQrename
    face_ne_zero := L.face_ne_zero
    binaryFace_ne_zero := hQne
    binary_det_zero := hdetQ
    face_linear_zero := L.face_linear_zero
  }⟩

/-- The ambient zero linear jet descends through the injective marked-axis
binary planarisation. -/
theorem TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData.binaryFace_linear_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (B : T.TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData D)
    (i : Fin 2) :
    MvPolynomial.coeff (Finsupp.single i 1) B.binaryFace = 0 := by
  let emb :=
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
      D.ell D.ell_ne_zero
  have hder := congrArg (MvPolynomial.pderiv (emb i)) B.face_eq_rename
  have hcomm :=
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.pderiv_rename_transverseBaseEmbedding
      D.ell D.ell_ne_zero i B.binaryFace
  rw [hcomm] at hder
  have hc0 := congrArg
    (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff 0 P) hder
  change MvPolynomial.coeff 0
      (MvPolynomial.rename emb (MvPolynomial.pderiv i B.binaryFace)) =
    MvPolynomial.coeff 0 (MvPolynomial.pderiv (emb i) B.face) at hc0
  have hrename :
      MvPolynomial.coeff 0
          (MvPolynomial.rename emb (MvPolynomial.pderiv i B.binaryFace)) =
        MvPolynomial.coeff 0 (MvPolynomial.pderiv i B.binaryFace) := by
    simpa only [MvPolynomial.constantCoeff_eq] using
      (MvPolynomial.constantCoeff_rename emb
        (MvPolynomial.pderiv i B.binaryFace))
  rw [hrename] at hc0
  rw [coeff_pderiv_backport, coeff_pderiv_backport] at hc0
  simp only [zero_add, Nat.cast_one, one_mul] at hc0
  have hamb := B.face_linear_zero (emb i)
  rw [hamb] at hc0
  simpa using hc0

/-- **Marked-axis entry to the complete carrier-independent binary Hesse
frontier.** -/
theorem TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData.curvedEliminatedFrontier
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (B : T.TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData D) :
    Nonempty (BinarySingularHessianCurvedEliminatedFrontier B.binaryFace) := by
  exact binarySingularHessian_curvedEliminatedFrontier
    B.binaryFace B.binaryFace_ne_zero B.binary_det_zero B.binaryFace_linear_zero

/-- Final carrier-independent binary normal form for the surviving marked-axis
wall.  The low-degree branch is forced to degree zero by the zero linear jet;
every nonlinear curved-eliminated branch is straightened to one exact axis. -/
inductive TopKernelMarkedAxisCanonicalSquareBinaryTerminalNormalForm
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (B : T.TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData D) :
    Type (u + 1)
  | degreeZero
      (H : MvPolynomial (Fin 2) K)
      (H_eq : H = binaryOrdinaryDegreeComponent B.binaryFace 0)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ B.binaryFace.support, d.degree ≤ 0)
  | nonlinearAxis
      (straight : BinarySingularHessianNonlinearAxisStraighteningData B.binaryFace)

/-- Consume the full curved-eliminated binary frontier into the final
degree-zero-or-one-axis normal form. -/
theorem TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData.terminalNormalForm
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (B : T.TopKernelMarkedAxisCanonicalSquareBinaryStationaryCoreData D) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareBinaryTerminalNormalForm B) := by
  rcases B.curvedEliminatedFrontier with ⟨F⟩
  cases F with
  | lowDegree n H hn H_eq H_ne_zero maximal =>
      have hn0 :=
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.binaryStationaryLowDegree_zeroJet_forces_degree_zero
          B.binaryFace n H hn H_eq H_ne_zero B.binaryFace_linear_zero
      subst n
      exact ⟨.degreeZero H H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed n H hn H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      let straight :=
        binarySingularHessian_nonlinearAxisStraightening
          B.binaryFace n H hn H_eq H_ne_zero maximal a c normalForm
          B.binaryFace_linear_zero B.binary_det_zero
      exact ⟨.nonlinearAxis straight⟩
  | nonlinearNextAffine n H hn H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero =>
      let straight :=
        binarySingularHessian_nonlinearAxisStraightening
          B.binaryFace n H hn H_eq H_ne_zero maximal a c normalForm
          B.binaryFace_linear_zero B.binary_det_zero
      exact ⟨.nonlinearAxis straight⟩
  | nonlinearNextLocked n H hn H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero transverse_first_zero =>
      let straight :=
        binarySingularHessian_nonlinearAxisStraightening
          B.binaryFace n H hn H_eq H_ne_zero maximal a c normalForm
          B.binaryFace_linear_zero B.binary_det_zero
      exact ⟨.nonlinearAxis straight⟩

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
