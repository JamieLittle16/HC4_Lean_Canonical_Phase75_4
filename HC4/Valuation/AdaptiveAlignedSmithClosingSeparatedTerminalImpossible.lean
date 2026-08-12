import HC4.Valuation.AdaptiveAlignedSmithClosingSourceLattice
import HC4.Valuation.StrictSmithFirstContactGeometry
import HC4.Valuation.QuadraticFamilyCollision
import HC4.Newton.TerminalWeightPermutation
import Mathlib.Tactic

/-!
# A separated adaptive source exposure cannot be a positive-defect terminal jump

`AdaptiveAlignedSmithClosingSourceLatticeData` deliberately uses the same
ramification certificate as the surviving-wall exposure.  Its
`positiveLayerSeparated` field keeps every positive parameter layer strictly
above the divided source level.

That is exactly right for an ordinary restart exposure, but it has an
important consequence at determinant closure: it cannot model a genuine
positive-defect direct jump.

Indeed every monomial which survives in the exposed special fibre must come
from parameter order zero and have source weight exactly `commonLevel`.
Hence the special fibre is genuinely weighted homogeneous for the natural
integral source weight.  If its Hessian determinant is one, a nonzero
Leibniz term of the actual Hessian pairs the four weights and gives

    2 * sum W = 4 * commonLevel.

On the other hand terminal transformed defect zero says

    R * Delta + 2 * sum W = 4 * commonLevel.

Therefore `R * Delta = 0`; positive ramification forces `Delta = 0`.

Thus a positive-defect rank-one Schur closing cannot be terminalised by a
`positiveLayerSeparated` exposure.  The true closing extraction must instead
be a *first-contact* lattice which deliberately allows the closing positive
parameter layer to land on the special fibre.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Exact order of a separated exposed coefficient -/

/-- Integrality of a supported adaptive exposure coefficient bounds the
common divided level by the exact ramified coefficient order plus source
weight. -/
theorem adaptiveSmithExposure_commonLevel_le_exactOrder
    {W : Fin 4 → ℕ} {m Delta : ℕ}
    (ram : AdaptiveSmithExposureRamificationData W m Delta)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure ram.R W m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    m ≤ ram.R * smithFamilyCoefficientParameterOrder P d hd +
      Finsupp.weight W d := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  let u := polynomialParameterPrimitivePart c hc
  let v := parameterRamificationHom (K := K) ram.R u
  let total := ram.R * q + Finsupp.weight W d

  have hprimitive : c = Polynomial.X ^ q * u := by
    simpa [q, u, c, smithFamilyCoefficientParameterOrder] using
      (polynomialParameterPrimitivePart_spec c hc)
  have huconst : Polynomial.constantCoeff u ≠ 0 := by
    simpa [u] using
      (polynomialParameterPrimitivePart_constantCoeff_ne_zero c hc)
  have hvconst : Polynomial.constantCoeff v ≠ 0 := by
    change v.coeff 0 ≠ 0
    dsimp [v]
    have hramconst :=
      constantCoeff_parameterRamificationHom
        (K := K) ram.R ram.R_pos u
    change
      ((parameterRamificationHom (K := K) ram.R u).coeff 0) =
        u.coeff 0 at hramconst
    change u.coeff 0 ≠ 0 at huconst
    rw [hramconst]
    exact huconst
  have hvne : v ≠ 0 := by
    intro hv
    apply hvconst
    rw [hv]
    simp

  have hfactor :
      adaptiveSmithExposureCoefficientFactor ram.R W P d =
        Polynomial.X ^ total * v := by
    unfold adaptiveSmithExposureCoefficientFactor
    change
      Polynomial.X ^ Finsupp.weight W d *
          parameterRamificationHom (K := K) ram.R c =
        Polynomial.X ^ total * v
    rw [hprimitive, map_mul, parameterRamificationHom_X_pow]
    dsimp [v]
    rw [← mul_assoc, ← pow_add]
    have htotal :
        Finsupp.weight W d + ram.R * q = total := by
      dsimp [total]
      exact Nat.add_comm _ _
    rw [htotal]

  have hfactorNe :
      adaptiveSmithExposureCoefficientFactor ram.R W P d ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hvne

  have horder :
      polynomialParameterOrder
          (adaptiveSmithExposureCoefficientFactor ram.R W P d) hfactorNe =
        total := by
    exact
      polynomialParameterOrder_eq_of_exact_X_power_factorisation
        (adaptiveSmithExposureCoefficientFactor ram.R W P d)
        hfactorNe total v hvconst hfactor

  have hle :=
    polynomial_X_pow_dvd_le_parameterOrder
      (adaptiveSmithExposureCoefficientFactor ram.R W P d)
      hfactorNe m (hint d hd)
  rw [horder] at hle
  simpa [total] using hle

/-- Exact factorisation of a supported coefficient after a separated
adaptive exposure.  The quotient has the expected residual order and a
primitive ramified factor. -/
theorem adaptiveSmithExposure_supportedCoefficient_exactFactorisation
    {W : Fin 4 → ℕ} {m Delta : ℕ}
    (ram : AdaptiveSmithExposureRamificationData W m Delta)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure ram.R W m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (adaptiveSmithExposureFamily ram.R W m P hint) =
      Polynomial.X ^
          (ram.R * smithFamilyCoefficientParameterOrder P d hd +
            Finsupp.weight W d - m) *
        parameterRamificationHom (K := K) ram.R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  let u := polynomialParameterPrimitivePart c hc
  let v := parameterRamificationHom (K := K) ram.R u
  let total := ram.R * q + Finsupp.weight W d

  have hprimitive : c = Polynomial.X ^ q * u := by
    simpa [q, u, c, smithFamilyCoefficientParameterOrder] using
      (polynomialParameterPrimitivePart_spec c hc)
  have hfactor :
      adaptiveSmithExposureCoefficientFactor ram.R W P d =
        Polynomial.X ^ total * v := by
    unfold adaptiveSmithExposureCoefficientFactor
    change
      Polynomial.X ^ Finsupp.weight W d *
          parameterRamificationHom (K := K) ram.R c =
        Polynomial.X ^ total * v
    rw [hprimitive, map_mul, parameterRamificationHom_X_pow]
    dsimp [v]
    rw [← mul_assoc, ← pow_add]
    have htotal :
        Finsupp.weight W d + ram.R * q = total := by
      dsimp [total]
      exact Nat.add_comm _ _
    rw [htotal]

  have hle : m ≤ total := by
    dsimp [total, q]
    exact adaptiveSmithExposure_commonLevel_le_exactOrder ram P hint hd

  have hid :=
    adaptiveSmithExposureFamily_coefficient_identity
      ram.R W m P hint d
  have heq :
      Polynomial.X ^ m *
          MvPolynomial.coeff d
            (adaptiveSmithExposureFamily ram.R W m P hint) =
        Polynomial.X ^ m * (Polynomial.X ^ (total - m) * v) := by
    calc
      Polynomial.X ^ m *
          MvPolynomial.coeff d
            (adaptiveSmithExposureFamily ram.R W m P hint) =
          adaptiveSmithExposureCoefficientFactor ram.R W P d := hid
      _ = Polynomial.X ^ total * v := hfactor
      _ = Polynomial.X ^ m * (Polynomial.X ^ (total - m) * v) := by
        rw [← mul_assoc, ← pow_add]
        rw [show m + (total - m) = total by omega]

  have hcancel := polynomial_X_pow_mul_cancel (K := K) m heq
  simpa [total, q, u, v, c] using hcancel

/-- A nonzero monomial of the separated exposure's special fibre has source
weight exactly equal to the divided common level.  Positive parameter layers
cannot survive because the ramification certificate separates all of them. -/
theorem adaptiveSmithExposure_specialFiber_weight_eq_commonLevel
    {W : Fin 4 → ℕ} {m Delta : ℕ}
    (ram : AdaptiveSmithExposureRamificationData W m Delta)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure ram.R W m P)
    (d : Fin 4 →₀ ℕ)
    (hcoeff :
      MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          (adaptiveSmithExposureFamily ram.R W m P hint)) ≠ 0) :
    Finsupp.weight W d = m := by
  have hconst :
      Polynomial.constantCoeff
        (MvPolynomial.coeff d
          (adaptiveSmithExposureFamily ram.R W m P hint)) ≠ 0 := by
    rw [← coeff_polynomialFamilySpecialFiber]
    exact hcoeff

  have hd : d ∈ P.support := by
    by_contra hd
    have hzero :
        MvPolynomial.coeff d
          (adaptiveSmithExposureFamily ram.R W m P hint) = 0 := by
      rw [coeff_adaptiveSmithExposureFamily]
      unfold adaptiveSmithExposureCoefficientQuotient
      simp [hd]
    apply hconst
    rw [hzero]
    simp

  let q := smithFamilyCoefficientParameterOrder P d hd
  let res := ram.R * q + Finsupp.weight W d - m
  let u :=
    parameterRamificationHom (K := K) ram.R
      (polynomialParameterPrimitivePart
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd))

  have hfac :=
    adaptiveSmithExposure_supportedCoefficient_exactFactorisation
      ram P hint hd
  have hfac' :
      MvPolynomial.coeff d
          (adaptiveSmithExposureFamily ram.R W m P hint) =
        Polynomial.X ^ res * u := by
    simpa [res, q, u] using hfac

  have hres0 : res = 0 := by
    by_contra hres
    have hrespos : 0 < res := Nat.pos_of_ne_zero hres
    apply hconst
    rw [hfac']
    change (Polynomial.X ^ res * u).coeff 0 = 0
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hrespos]

  have hq0 : q = 0 := by
    by_contra hq
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hsep := ram.positiveLayerSeparated q hqpos d
    have hsep' :
        m < ram.R * q + Finsupp.weight W d := by
      simpa [Nat.mul_comm] using hsep
    dsimp [res] at hres0
    omega

  have hle :
      m ≤ ram.R * q + Finsupp.weight W d := by
    dsimp [q]
    exact adaptiveSmithExposure_commonLevel_le_exactOrder ram P hint hd

  dsimp [res] at hres0
  rw [hq0] at hres0 hle
  norm_num at hres0 hle
  omega

/-! ## Weighted homogeneity of the separated terminal fibre -/

/-- Natural source weighted degree agrees with the integral weighted-degree
convention used by the terminal endpoint theory. -/
theorem integralWeightedDegree_natCast_eq_weight
    (W : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    integralWeightedDegree (fun i : Fin 4 => (W i : ℤ)) d =
      (Finsupp.weight W d : ℤ) := by
  unfold integralWeightedDegree
  rw [Finsupp.weight_apply]
  push_cast
  rfl

namespace AdaptiveAlignedSmithClosingTerminalLatticeData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- The special fibre of a separated terminal lattice is automatically
weighted homogeneous for its actual natural source weight. -/
theorem weightedHomogeneous
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    IsIntegralWeightedHomogeneous
      (fun i : Fin 4 => (T.lattice.weight i : ℤ))
      (T.lattice.commonLevel : ℤ)
      T.fibre := by
  intro d hcoeff
  have hw :=
    adaptiveSmithExposure_specialFiber_weight_eq_commonLevel
      T.lattice.ramification
      B.aligned.endpoint.rightRecenteredFamily
      T.lattice.familyIntegrality
      d
      (by
        simpa [fibre, AdaptiveAlignedSmithClosingSourceLatticeData.family] using hcoeff)
  rw [integralWeightedDegree_natCast_eq_weight]
  exact_mod_cast hw

/-- For a four-variable Monge--Ampere polynomial, the actual Hessian at the
origin has nonzero determinant. -/
theorem mongeAmpere_hasNondegenerateActualHessian
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    HasNondegenerateTerminalActualHessian
      (0 : Fin 4) 1 2 3 T.fibre := by
  unfold HasNondegenerateTerminalActualHessian
  have hmatrix :
      terminalActualHessianMatrix (0 : Fin 4) 1 2 3 T.fibre =
        quadraticFamilyHessianMatrix T.fibre := by
    ext i j
    unfold terminalActualHessianMatrix quadraticFamilyHessianMatrix
    simp only [terminalFourCoordinate_standard]
    unfold mvHessianComponentAt
    change
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j T.fibre)) =
        MvPolynomial.constantCoeff
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i T.fibre))
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
    rw [pderiv_comm_commRing i j T.fibre]
  rw [hmatrix, quadraticFamilyHessianMatrix_det]
  have hMA := T.mongeAmpere
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere at hMA
  rw [hMA]
  simp

/-- Determinant nondegeneracy and weighted homogeneity pair all four source
weights.  Summing one nonzero Leibniz term gives the terminal balance
`2*sum W = 4*m`. -/
theorem sourceWeight_balance
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    2 * (∑ i : Fin 4, T.lattice.weight i) =
      4 * T.lattice.commonLevel := by
  have hdet := T.mongeAmpere_hasNondegenerateActualHessian
  unfold HasNondegenerateTerminalActualHessian at hdet
  rcases
      matrix4_det_ne_zero_exists_permutation_entries_ne_zero
        (terminalActualHessianMatrix (0 : Fin 4) 1 2 3 T.fibre)
        hdet with
    ⟨pi, hentries⟩

  have hpairs :
      ∀ i : Fin 4,
        (T.lattice.weight (pi i) : ℤ) +
            (T.lattice.weight i : ℤ) =
          (T.lattice.commonLevel : ℤ) := by
    intro i
    have hentry :
        mvHessianComponentAt
          (fun _ : Fin 4 => (0 : K))
          T.fibre (pi i) i ≠ 0 := by
      simpa only [terminalActualHessianMatrix,
        terminalFourCoordinate_standard] using hentries i
    have hquad :=
      mvHessianComponentAt_origin_ne_zero_quadraticCoeff
        T.fibre (pi i) i hentry
    exact
      weightedHomogeneous_quadraticCoeff_weightSum
        T.weightedHomogeneous (pi i) i hquad

  have hsum :
      (∑ i : Fin 4,
        ((T.lattice.weight (pi i) : ℤ) +
          (T.lattice.weight i : ℤ))) =
        ∑ _i : Fin 4, (T.lattice.commonLevel : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpairs i

  have hperm :
      (∑ i : Fin 4, (T.lattice.weight (pi i) : ℤ)) =
        ∑ i : Fin 4, (T.lattice.weight i : ℤ) := by
    simpa using
      (Equiv.sum_comp pi
        (fun i : Fin 4 => (T.lattice.weight i : ℤ)))

  rw [Finset.sum_add_distrib, hperm] at hsum
  have hbalanceZ :
      2 * (∑ i : Fin 4, (T.lattice.weight i : ℤ)) =
        4 * (T.lattice.commonLevel : ℤ) := by
    simpa [two_mul, Fin.sum_univ_four] using hsum
  exact_mod_cast hbalanceZ

/-- **Separated terminal impossibility at positive incoming defect.**
A terminal defect-zero exposure with all positive parameter layers separated
can only have come from an incoming source whose Hessian defect was already
zero. -/
theorem sourceDefect_eq_zero
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    B.aligned.endpoint.defect = 0 := by
  let S := ∑ i : Fin 4, T.lattice.weight i
  have hterminal :
      T.lattice.ramification.R * B.aligned.endpoint.defect + 2 * S =
        4 * T.lattice.commonLevel := by
    have hnonneg :=
      T.lattice.ramification.determinantExponentNonnegative
    have hz := T.terminalDefect
    unfold AdaptiveAlignedSmithClosingSourceLatticeData.defect at hz
    dsimp [S] at hnonneg hz ⊢
    omega
  have hbalance :
      2 * S = 4 * T.lattice.commonLevel := by
    dsimp [S]
    exact T.sourceWeight_balance
  have hprod :
      T.lattice.ramification.R * B.aligned.endpoint.defect = 0 := by
    omega
  rcases Nat.mul_eq_zero.mp hprod with hR | hDelta
  · exact False.elim (Nat.ne_of_gt T.lattice.ramification.R_pos hR)
  · exact hDelta

end AdaptiveAlignedSmithClosingTerminalLatticeData

/-! ## Closing-carrier corollaries -/

/-- A positive-defect rank-one Schur closing cannot be terminalised by the
separated source-lattice exposure.  Its actual terminal extraction must be a
first-contact construction. -/
theorem AdaptiveAlignedSmithRankOneClosingSourceCarrier.noSeparatedTerminalLattice
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpos : 0 < B.aligned.endpoint.defect) :
    ¬ Nonempty (AdaptiveAlignedSmithRankOneClosingTerminalLatticeData C) := by
  rintro ⟨T⟩
  exact (Nat.ne_of_gt hpos) T.sourceDefect_eq_zero

/-- The same obstruction applies to a positive-defect zero-Schur closing if
one tries to terminalise it with the separated exposure rather than first
using its kernel restart. -/
theorem AdaptiveAlignedSmithZeroSchurClosingSourceCarrier.noSeparatedTerminalLattice
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (hpos : 0 < B.aligned.endpoint.defect) :
    ¬ Nonempty (AdaptiveAlignedSmithZeroSchurClosingTerminalLatticeData C) := by
  rintro ⟨T⟩
  exact (Nat.ne_of_gt hpos) T.sourceDefect_eq_zero

end

end HC4.Valuation
