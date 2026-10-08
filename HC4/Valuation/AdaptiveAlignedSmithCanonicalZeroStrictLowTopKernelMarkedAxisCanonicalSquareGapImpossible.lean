import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisCanonicalSquareLattice
import Mathlib.Tactic

/-!
# Exact-closing canonical square: the parameter gap excludes integral exposure

At exact marked-axis closing, every coefficient of the aligned sheared source
is a constant plus a multiple of X^Delta.  The canonical square exposure has
ramification 4, common level 4*Delta, and weights 0,0,3*Delta,3*Delta.

The coefficient of order 4*Delta in the inflated source coefficient shows
that the exposed special fibre cannot contain any monomial involving one of
the complementary positive-weight coordinates: the constant source term has
order 3*Delta*n != 4*Delta and the deformation has order strictly larger than
4*Delta there.

Hence a complementary Hessian row vanishes in the exposed special fibre.  Its
Hessian determinant is zero, contradicting the already-proved defect-zero
exposure family, which has determinant one on its special fibre.

This eliminates the *integral* alternative of the canonical-square first-wall
dichotomy without postulating a terminal cocharacter, a rank-three endpoint,
or a stronger first-contact producer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Coefficient at the common divided level of an integral exposure.

For a family with no positive parameter terms below Delta, a monomial of
positive source weight unequal to the common level R*Delta cannot survive
in the special fibre of an integral exposure.  This is an exact polynomial
coefficient calculation, not Laurent-series reasoning. -/
private theorem exposure_specialFiber_coeff_zero_of_gap
    (R Delta : ℕ) (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W (R * Delta) P)
    (hgap : ∀ d : Fin 4 →₀ ℕ,
      ∃ a : K, ∃ r : Polynomial K,
        MvPolynomial.coeff d P =
          Polynomial.C a + Polynomial.X ^ Delta * r)
    (d : Fin 4 →₀ ℕ)
    (hwpos : 0 < Finsupp.weight W d)
    (hwne : Finsupp.weight W d ≠ R * Delta) :
    MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          (adaptiveSmithExposureFamily R W (R * Delta) P hint)) = 0 := by
  let w : ℕ := Finsupp.weight W d
  let m : ℕ := R * Delta
  rcases hgap d with ⟨a, r, hgapd⟩
  have hramC :
      parameterRamificationHom (K := K) R (Polynomial.C a) =
        Polynomial.C a := by
    simp [parameterRamificationHom_apply]
  have hid :=
    adaptiveSmithExposureFamily_coefficient_identity R W m P hint d
  change Polynomial.X ^ m *
        MvPolynomial.coeff d
          (adaptiveSmithExposureFamily R W m P hint) =
      Polynomial.X ^ w *
        parameterRamificationHom (K := K) R
          (MvPolynomial.coeff d P) at hid
  rw [hgapd, map_add, map_mul, parameterRamificationHom_X_pow, hramC] at hid
  change Polynomial.X ^ m *
        MvPolynomial.coeff d
          (adaptiveSmithExposureFamily R W m P hint) =
      Polynomial.X ^ w *
        (Polynomial.C a +
          Polynomial.X ^ m * parameterRamificationHom (K := K) R r) at hid
  rw [mul_add, ← mul_assoc, ← pow_add,
    mul_comm (Polynomial.X ^ w) (Polynomial.C a)] at hid
  have hleft :
      (Polynomial.X ^ m *
        MvPolynomial.coeff d
          (adaptiveSmithExposureFamily R W m P hint)).coeff m =
        (MvPolynomial.coeff d
          (adaptiveSmithExposureFamily R W m P hint)).coeff 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  have hconstant :
      (Polynomial.C a * Polynomial.X ^ w).coeff m = 0 := by
    rw [Polynomial.coeff_C_mul_X_pow]
    have hmw : m ≠ w := by
      intro heq
      exact hwne heq.symm
    simp [hmw]
  have hpositive :
      (Polynomial.X ^ (w + m) *
        parameterRamificationHom (K := K) R r).coeff m = 0 := by
    have hgt : m < w + m := by omega
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hgt]
  have hc := congrArg (fun p : Polynomial K => p.coeff m) hid
  change
    (Polynomial.X ^ m *
      MvPolynomial.coeff d (adaptiveSmithExposureFamily R W m P hint)).coeff m =
    (Polynomial.C a * Polynomial.X ^ w +
      Polynomial.X ^ (w + m) * parameterRamificationHom (K := K) R r).coeff m
      at hc
  rw [hleft, Polynomial.coeff_add, hconstant, hpositive] at hc
  have hz :
      (MvPolynomial.coeff d
        (adaptiveSmithExposureFamily R W m P hint)).coeff 0 = 0 := by
    simpa using hc
  simpa [coeff_polynomialFamilySpecialFiber, m] using hz

/-- Choose one complementary coordinate of the canonical marked-axis square.
Its coefficient in the canonical source weight is 3*Delta.  Any monomial
involving this coordinate has positive weight divisible by 3*Delta. -/
private theorem canonicalSquare_complement_weight_multiple
    (Delta : ℕ) (ell : Fin 4) (hell : ell ≠ 0)
    (d : Fin 4 →₀ ℕ)
    (hpos : 0 < d (if ell = (1 : Fin 4) then (2 : Fin 4)
                     else (1 : Fin 4))) :
    ∃ n : ℕ, 0 < n ∧
      Finsupp.weight (directClosingCanonicalSquareWeight Delta ell) d =
        3 * Delta * n := by
  fin_cases ell
  · exact (hell rfl).elim
  · refine ⟨d (2 : Fin 4) + d (3 : Fin 4), ?_, ?_⟩
    · change 0 < d (2 : Fin 4) at hpos
      omega
    · simp [Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_four, directClosingCanonicalSquareWeight]
      ring
  · refine ⟨d (1 : Fin 4) + d (3 : Fin 4), ?_, ?_⟩
    · change 0 < d (1 : Fin 4) at hpos
      omega
    · simp [Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_four, directClosingCanonicalSquareWeight]
      ring
  · refine ⟨d (1 : Fin 4) + d (2 : Fin 4), ?_, ?_⟩
    · change 0 < d (1 : Fin 4) at hpos
      omega
    · simp [Finsupp.weight_apply, Finsupp.sum_fintype,
        Fin.sum_univ_four, directClosingCanonicalSquareWeight]
      ring

/-- No positive multiple of 3*Delta can equal 4*Delta when Delta is
strictly positive. -/
private theorem canonicalSquare_weight_ne_commonLevel
    (Delta n : ℕ) (hDelta : 0 < Delta) (_hn : 0 < n) :
    3 * Delta * n ≠ 4 * Delta := by
  intro heq
  have hmul : Delta * (3 * n) = Delta * 4 := by
    calc
      Delta * (3 * n) = 3 * Delta * n := by ring
      _ = 4 * Delta := heq
      _ = Delta * 4 := by ring
  have hn34 : 3 * n = 4 := Nat.mul_left_cancel hDelta hmul
  omega

/-- The exact-closing integral canonical square would produce a determinant-one
special fibre independent of a complementary variable.  This is impossible. -/
theorem TopKernelMarkedAxisCanonicalSquareIntegralityData.impossible_of_exactClosing
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {D : T.TopKernelMarkedAxisAlignedFreshSquareData}
    (G : T.TopKernelMarkedAxisCanonicalSquareIntegralityData D)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    False := by
  let Delta : ℕ := 4 * T.topFace.degree - 6
  let W : Fin 4 → ℕ := directClosingCanonicalSquareWeight Delta D.ell
  let j : Fin 4 := if D.ell = (1 : Fin 4) then 2 else 1
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber G.exposedFamily
  have hDelta : 0 < Delta := by
    have hdeg := T.topFace.degree_ge_three
    dsimp [Delta]
    omega
  have hgap : ∀ d : Fin 4 →₀ ℕ,
      ∃ a : K, ∃ r : Polynomial K,
        MvPolynomial.coeff d D.family =
          Polynomial.C a + Polynomial.X ^ Delta * r := by
    intro d
    rcases D.family_coefficient_firstActual_gap d with ⟨a, r, h⟩
    exact ⟨a, r, by simpa [Delta, heq] using h⟩
  have hcoeff : ∀ d : Fin 4 →₀ ℕ, 0 < d j →
      MvPolynomial.coeff d F = 0 := by
    intro d hd
    rcases canonicalSquare_complement_weight_multiple
        Delta D.ell D.ell_ne_zero d (by simpa [j] using hd) with
      ⟨n, hn, hweight⟩
    have hwpos : 0 < Finsupp.weight W d := by
      rw [show Finsupp.weight W d = 3 * Delta * n by simpa [W] using hweight]
      exact Nat.mul_pos (Nat.mul_pos (by omega) hDelta) hn
    have hwne : Finsupp.weight W d ≠ 4 * Delta := by
      rw [show Finsupp.weight W d = 3 * Delta * n by simpa [W] using hweight]
      exact canonicalSquare_weight_ne_commonLevel Delta n hDelta hn
    have hzero :=
      exposure_specialFiber_coeff_zero_of_gap
        (K := K) 4 Delta W D.family G.familyIntegrality
        hgap d hwpos hwne
    simpa [F, W, Delta,
      TopKernelMarkedAxisCanonicalSquareIntegralityData.exposedFamily,
      directClosingCanonicalSquareRamification,
      directClosingCanonicalSquareCommonLevel] using hzero
  have hderiv : MvPolynomial.pderiv j F = 0 := by
    apply MvPolynomial.ext
    intro d
    rw [coeff_pderiv_commSemiring]
    have hdpos :
        0 < ((d + Finsupp.single j 1 : Fin 4 →₀ ℕ) j) := by
      simp
    rw [hcoeff (d + Finsupp.single j 1) hdpos]
    simp
  have hzero : HC4.Polynomial.hessianDeterminant F = 0 := by
    unfold HC4.Polynomial.hessianDeterminant
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro k
    simp [HC4.Polynomial.hessian_apply, hderiv]
  have hone : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    rw [hessianDeterminant_polynomialFamilySpecialFiber]
    have hdef := G.exposedFamily_hasHessianDefect
    unfold HasPolynomialFamilyHessianDefect at hdef
    rw [hdef]
    simp
  have hbad : (1 : MvPolynomial (Fin 4) K) = 0 :=
    hone.symm.trans hzero
  exact one_ne_zero hbad

/-- Exact marked-axis closing therefore forces the finite family-obstruction
alternative; the integral-exposure alternative is impossible. -/
theorem topKernelMarkedAxisCanonicalSquare_obstruction_of_eq_defect
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (heq :
      T.topKernelMarkedAxisFirstActualLayerOrder =
        4 * T.topFace.degree - 6) :
    ∃ D : T.TopKernelMarkedAxisAlignedFreshSquareData,
      Nonempty (T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) := by
  rcases T.topKernelMarkedAxisCanonicalSquareExposure_or_obstruction_of_eq_defect
      heq with hexposed | hobstruction
  · rcases hexposed with ⟨D, G, _, _⟩
    exact (G.impossible_of_exactClosing heq).elim
  · exact hobstruction


/-! ## The actual preclosing canonical-square obstruction

The first-actual-layer clock is always strictly below the Hessian defect:
`j ≤ D < 4D - 6 = Delta`.  The fresh-square exponent has source weight
zero and its family coefficient at order `j` is nonzero.  After the canonical
fourfold ramification it is still nonzero at order `4*j < 4*Delta`, so
the required common-level divisibility fails *at that explicit exponent*.

This is a genuine preclosing certificate, rather than the unreachable
exact-closing subcase considered above. -/

/-- The distinguished fresh square is itself a concrete counterexample to
the canonical-square coefficientwise integrality gate.  Its failure occurs
at the true positive first-actual clock, strictly before Hessian closure. -/
noncomputable def TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D := by
  let Delta : ℕ := 4 * T.topFace.degree - 6
  let j : ℕ := T.topKernelMarkedAxisFirstActualLayerOrder
  have hjlt : 4 * j < 4 * Delta := by
    have h := T.topKernelMarkedAxisFirstActualLayerOrder_lt_defect
    dsimp [j, Delta]
    omega
  have hsquare :
      (MvPolynomial.coeff D.squareExponent D.family).coeff j ≠ 0 := by
    simpa [j, TopKernelMarkedAxisAlignedFreshSquareData.squareExponent,
      TopKernelMarkedAxisAlignedFreshSquareData.family] using
      D.squareCoeff_closing_ne
  have hram :
      (parameterRamificationHom (K := K) 4
        (MvPolynomial.coeff D.squareExponent D.family)).coeff (4 * j) ≠ 0 := by
    rw [parameterRamificationHom_eq_expand]
    rw [Polynomial.coeff_expand_mul' (R := K) (by norm_num)]
    exact hsquare
  refine {
    exponent := D.squareExponent
    mem_family := D.squareSupport
    not_divisible := ?_
  }
  intro hdiv
  change
    Polynomial.X ^ (4 * Delta) ∣
      Polynomial.X ^
          Finsupp.weight
            (directClosingCanonicalSquareWeight Delta D.ell)
            D.squareExponent *
        parameterRamificationHom (K := K) 4
          (MvPolynomial.coeff D.squareExponent D.family) at hdiv
  rw [D.canonicalSquareWeight_squareExponent] at hdiv
  simp only [pow_zero, one_mul] at hdiv
  have hzero :=
    (Polynomial.X_pow_dvd_iff.mp hdiv) (4 * j) hjlt
  exact hram hzero

/-- The canonical square family obstruction exists for every aligned
fresh-square packet, without any equality between the first actual layer
and the Hessian closing order.  Moreover the witness is precisely the
fresh-square exponent of positive preclosing order. -/
theorem topKernelMarkedAxisCanonicalSquare_obstruction
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) :=
  ⟨D.freshSquareObstruction⟩

/-- The explicit obstruction's parameter order is the first actual
positive layer, hence is strictly below the determinant closing clock. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction_order
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    smithFamilyCoefficientParameterOrder
        D.family
        D.freshSquareObstruction.exponent
        D.freshSquareObstruction.mem_family =
      T.topKernelMarkedAxisFirstActualLayerOrder := by
  simpa [TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction] using
    D.squareExactOrder

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
