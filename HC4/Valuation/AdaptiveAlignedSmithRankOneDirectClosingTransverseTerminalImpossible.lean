import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingTerminalCocharacterFrontier
import Mathlib.Tactic

/-!
# Transverse canonical terminal square contact is impossible

The canonical terminal square ray has a particularly rigid arithmetic in the
transverse branch.  If the fresh square is in a coordinate `ell != 0`, the two
coordinates complementary to `{0, ell}` have source weight `3 * Delta`.

At `j = Delta`, every quadratic source coefficient below positive order `j`
vanishes, and this remains true after the marked-axis-preserving constant
transvections used to align the fresh kernel direction.  On a terminal
canonical exposure every surviving coefficient satisfies the exact contact
identity

    4 q + wt(d) = 4 Delta.

A quadratic monomial involving either complementary coordinate has weight at
least `3 Delta`.  If its parameter order is positive, the first-layer gap
forces `q >= Delta`, so it overshoots the terminal level.  If its order is
zero, its quadratic weight is either `3 Delta` or `6 Delta`, never `4 Delta`.
Hence the terminal Hessian has a zero complementary row, contradicting the
Monge--Ampere determinant `1`.

No JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Constant source shears preserve a vanished Hessian layer -/

/-- If one parameter coefficient of the entire origin Hessian vanishes, a
constant transverse source transvection preserves that vanishing. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_eq_zero_of_zero
    (k ell : Fin 4) (hkl : k ≠ ell) (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) (n : ℕ)
    (hzero : ∀ i r : Fin 4,
      (quadraticFamilyHessianMatrix P i r).coeff n = 0) :
    ∀ i r : Fin 4,
      (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        i r).coeff n = 0 := by
  intro i r
  by_cases hi : i = ell
  · subst i
    by_cases hr : r = ell
    · subst r
      rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
        k ell hkl a P n]
      simp [hzero]
    · rw [quadraticFamilyHessianMatrix_coeff_symmetric
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        n ell r]
      rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
        k ell r hkl hr a P n]
      simp [hzero]
  · by_cases hr : r = ell
    · subst r
      rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
        k ell i hkl hi a P n]
      simp [hzero]
    · rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
        k ell i r hkl hi hr a P n]
      exact hzero i r

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- All positive origin-Hessian layers below `j` remain zero on the actual
three-transvection transverse aligned family. -/
theorem DirectClosingTransverseAlignedSquareData.sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    {n : ℕ} (hnpos : 0 < n) (hnlt : n < C.firstActualLayerOrder) :
    sourceOriginHessianLayer A.family n = 0 := by
  have h0 : ∀ i r : Fin 4,
      (quadraticFamilyHessianMatrix C.family i r).coeff n = 0 := by
    intro i r
    rw [← sourceOriginHessianLayer_apply]
    rw [C.sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual hnpos hnlt]
    rfl
  have h1 := quadraticFamilyHessianMatrix_coeff_transverseSourceShear_eq_zero_of_zero
    (K := K) A.k₁ A.ell A.k₁_ne_ell A.a₁ C.family n h0
  have h2 := quadraticFamilyHessianMatrix_coeff_transverseSourceShear_eq_zero_of_zero
    (K := K) A.k₂ A.ell A.k₂_ne_ell A.a₂
      (transverseSourceShearHom (K := K) A.k₁ A.ell (Polynomial.C A.a₁) C.family)
      n h1
  have h3 := quadraticFamilyHessianMatrix_coeff_transverseSourceShear_eq_zero_of_zero
    (K := K) A.k₃ A.ell A.k₃_ne_ell A.a₃
      (transverseSourceShearHom (K := K) A.k₂ A.ell (Polynomial.C A.a₂)
        (transverseSourceShearHom (K := K) A.k₁ A.ell (Polynomial.C A.a₁) C.family))
      n h2
  apply Matrix.ext
  intro i r
  rw [sourceOriginHessianLayer_apply]
  simpa [DirectClosingTransverseAlignedSquareData.family,
    tripleTransverseSourceShearFamily] using h3 i r

/-- Every quadratic coefficient on a transverse aligned source has parameter
order either zero or at least the first positive actual order. -/
theorem DirectClosingTransverseAlignedSquareData.quadraticOrder_eq_zero_or_firstActual_le
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    (i r : Fin 4)
    (hd : directClosingQuadraticExponent i r ∈ A.family.support) :
    smithFamilyCoefficientParameterOrder A.family
        (directClosingQuadraticExponent i r) hd = 0 ∨
      C.firstActualLayerOrder ≤
        smithFamilyCoefficientParameterOrder A.family
          (directClosingQuadraticExponent i r) hd := by
  let d := directClosingQuadraticExponent i r
  let q := smithFamilyCoefficientParameterOrder A.family d (by simpa [d] using hd)
  by_cases hq0 : q = 0
  · exact Or.inl (by simpa [q, d] using hq0)
  · right
    by_contra hnot
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqlt : q < C.firstActualLayerOrder := Nat.lt_of_not_ge hnot
    have hHzero := A.sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual hqpos hqlt
    have hentry0 := congrArg
      (fun M : Matrix (Fin 4) (Fin 4) K => M i r) hHzero
    change sourceOriginHessianLayer A.family q i r = 0 at hentry0
    have hcoeff :
        (MvPolynomial.coeff d A.family).coeff q ≠ 0 := by
      let hd' : d ∈ A.family.support := by simpa [d] using hd
      have hc : MvPolynomial.coeff d A.family ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hd'
      have h := polynomialParameterOrder_coeff_ne_zero
        (MvPolynomial.coeff d A.family) hc
      simpa [q, d, smithFamilyCoefficientParameterOrder] using h
    have hf := quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient
      (familyParameterLayer A.family q) i r
    rw [familyParameterLayer_coeff] at hf
    change sourceOriginHessianLayer A.family q i r = _ at hf
    rw [hentry0] at hf
    have hscalar :
        ((((Finsupp.single r 1) i + 1 : ℕ) : K)) ≠ 0 := by
      by_cases hri : r = i
      · subst r
        simp
      · have hir : i ≠ r := Ne.symm hri
        simp [Finsupp.single_apply, hir]
    have hzcoeff : (MvPolynomial.coeff d A.family).coeff q = 0 := by
      have hzmul :
          (MvPolynomial.coeff d A.family).coeff q *
            (((Finsupp.single r 1) i + 1 : ℕ) : K) = 0 := by
        simpa [d, directClosingQuadraticExponent] using hf.symm
      exact (mul_eq_zero.mp hzmul).resolve_right hscalar
    exact hcoeff hzcoeff

/-! ## Exact source contact level of every terminal coefficient -/

/-- Every nonzero coefficient of a generic terminal first-contact fibre comes
from an original supported coefficient whose *exact* parameter order plus
source weight equals the divided common level. -/
theorem DirectClosingSquareFirstContactTerminalData.sourceContactLevel_of_coeff_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L)
    {d : Fin 4 →₀ ℕ}
    (hcoeff : MvPolynomial.coeff d T.fibre ≠ 0) :
    ∃ hd : d ∈ D.family.support,
      L.R * smithFamilyCoefficientParameterOrder D.family d hd +
          Finsupp.weight L.weight d = L.commonLevel := by
  have hconst :
      Polynomial.constantCoeff (MvPolynomial.coeff d L.family) ≠ 0 := by
    simpa [DirectClosingSquareFirstContactTerminalData.fibre,
      coeff_polynomialFamilySpecialFiber] using hcoeff
  have hfamilyCoeff : MvPolynomial.coeff d L.family ≠ 0 := by
    intro hz
    apply hconst
    rw [hz]
    simp
  have hdL : d ∈ L.family.support := MvPolynomial.mem_support_iff.mpr hfamilyCoeff
  have hd : d ∈ D.family.support :=
    support_adaptiveSmithExposureFamily_subset
      L.R L.weight L.commonLevel D.family L.familyIntegrality hdL
  refine ⟨hd, ?_⟩
  let q := smithFamilyCoefficientParameterOrder D.family d hd
  let total := L.R * q + Finsupp.weight L.weight d
  have hle : L.commonLevel ≤ total := by
    simpa [q, total] using
      adaptiveSmithFirstContactExposure_commonLevel_le_exactOrder
        L.R L.R_pos D.family L.familyIntegrality hd
  have hfac0 :=
    adaptiveSmithFirstContactExposure_supportedCoefficient_exactFactorisation
      L.R L.R_pos D.family L.familyIntegrality hd
  have hfac :
      MvPolynomial.coeff d L.family =
        Polynomial.X ^
            (L.R * smithFamilyCoefficientParameterOrder D.family d hd +
              Finsupp.weight L.weight d - L.commonLevel) *
          parameterRamificationHom (K := K) L.R
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d D.family)
              (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [DirectClosingSquareFirstContactLatticeData.family] using hfac0
  by_contra hne
  have hlt : L.commonLevel < total := lt_of_le_of_ne hle (Ne.symm hne)
  have hpos : 0 < total - L.commonLevel := Nat.sub_pos_of_lt hlt
  have hrespos :
      0 < L.R * smithFamilyCoefficientParameterOrder D.family d hd +
          Finsupp.weight L.weight d - L.commonLevel := by
    simpa [q, total] using hpos
  have hz : Polynomial.constantCoeff (MvPolynomial.coeff d L.family) = 0 := by
    rw [hfac]
    change
      (Polynomial.X ^
          (L.R * smithFamilyCoefficientParameterOrder D.family d hd +
            Finsupp.weight L.weight d - L.commonLevel) *
        parameterRamificationHom (K := K) L.R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d D.family)
            (MvPolynomial.mem_support_iff.mp hd))).coeff 0 = 0
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hrespos]
  exact hconst hz

/-! ## Canonical transverse weight arithmetic -/

/-- A quadratic involving a coordinate complementary to `{0,i}` on a
transverse canonical square ray has weight at least `3*Delta`. -/
theorem directClosingCanonicalSquareWeight_quadratic_high_ge
    (Delta : ℕ) (i h r : Fin 4)
    (hi0 : i ≠ 0) (hh0 : h ≠ 0) (hhi : h ≠ i) :
    3 * Delta ≤
      Finsupp.weight (directClosingCanonicalSquareWeight Delta i)
        (directClosingQuadraticExponent h r) := by
  fin_cases i <;> fin_cases h <;> fin_cases r <;>
    simp [directClosingCanonicalSquareWeight, directClosingQuadraticExponent,
      Finsupp.weight_single] at * <;> omega

/-- In the same situation the weight of a quadratic high-row monomial is
never the terminal value `4*Delta` when `Delta>0`. -/
theorem directClosingCanonicalSquareWeight_quadratic_high_ne_four
    (Delta : ℕ) (i h r : Fin 4)
    (hDelta : 0 < Delta)
    (hi0 : i ≠ 0) (hh0 : h ≠ 0) (hhi : h ≠ i) :
    Finsupp.weight (directClosingCanonicalSquareWeight Delta i)
        (directClosingQuadraticExponent h r) ≠ 4 * Delta := by
  fin_cases i <;> fin_cases h <;> fin_cases r <;>
    simp [directClosingCanonicalSquareWeight, directClosingQuadraticExponent,
      Finsupp.weight_single] at * <;> omega

/-! ## A canonical complementary transverse coordinate -/

/-- Choose one coordinate complementary to `{0, ell}`. -/
def directClosingTransverseComplement (ell : Fin 4) : Fin 4 :=
  if ell = (1 : Fin 4) then (2 : Fin 4) else (1 : Fin 4)

@[simp] theorem directClosingTransverseComplement_ne_zero (ell : Fin 4) :
    directClosingTransverseComplement ell ≠ (0 : Fin 4) := by
  unfold directClosingTransverseComplement
  split <;> decide

theorem directClosingTransverseComplement_ne_self
    (ell : Fin 4) (hell0 : ell ≠ (0 : Fin 4)) :
    directClosingTransverseComplement ell ≠ ell := by
  fin_cases ell <;>
    simp [directClosingTransverseComplement] at *

/-! ## Transverse terminal impossibility -/

/-- One complementary row of a canonical transverse terminal Hessian must
vanish. -/
theorem DirectClosingTransverseAlignedSquareData.canonicalTerminal_highRow_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (G : DirectClosingCanonicalSquareIntegralityData A.toAlignedSquareSource)
    (T : DirectClosingSquareFirstContactTerminalData
      (G.toFirstContactLattice heq))
    (h : Fin 4) (hh0 : h ≠ 0) (hhell : h ≠ A.ell) :
    ∀ r : Fin 4, quadraticFamilyHessianMatrix T.fibre h r = 0 := by
  intro r
  by_contra hentry
  let d := directClosingQuadraticExponent h r
  have hdT : MvPolynomial.coeff d T.fibre ≠ 0 := by
    intro hz
    apply hentry
    have hf := quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient
      T.fibre h r
    have hz' :
        MvPolynomial.coeff
          ((Finsupp.single r 1) + Finsupp.single h 1) T.fibre = 0 := by
      simpa [d, directClosingQuadraticExponent] using hz
    rw [hz'] at hf
    simpa using hf
  rcases T.sourceContactLevel_of_coeff_ne_zero hdT with ⟨hd, hlevel⟩
  let q := smithFamilyCoefficientParameterOrder
    A.toAlignedSquareSource.family d hd
  have hdA : d ∈ A.family.support := by
    simpa [DirectClosingTransverseAlignedSquareData.toAlignedSquareSource] using hd
  have hqcases := A.quadraticOrder_eq_zero_or_firstActual_le h r hdA
  have hDelta : 0 < B.aligned.endpoint.defect := by
    rw [← heq]
    exact C.firstActualLayerOrder_pos
  have hi0 : A.ell ≠ 0 := A.ell_ne_zero
  have hwge := directClosingCanonicalSquareWeight_quadratic_high_ge
    B.aligned.endpoint.defect A.ell h r hi0 hh0 hhell
  have hwne := directClosingCanonicalSquareWeight_quadratic_high_ne_four
    B.aligned.endpoint.defect A.ell h r hDelta hi0 hh0 hhell
  have hwge' :
      3 * B.aligned.endpoint.defect ≤
        Finsupp.weight
          (directClosingCanonicalSquareWeight B.aligned.endpoint.defect A.ell) d := by
    simpa [d] using hwge
  have hlevel' :
      4 * q +
          Finsupp.weight
            (directClosingCanonicalSquareWeight B.aligned.endpoint.defect A.ell) d =
        4 * B.aligned.endpoint.defect := by
    simpa [DirectClosingCanonicalSquareIntegralityData.toFirstContactLattice,
      directClosingCanonicalSquareRamification,
      directClosingCanonicalSquareCommonLevel,
      DirectClosingTransverseAlignedSquareData.toAlignedSquareSource,
      q, d] using hlevel
  rcases hqcases with hq0 | hqge
  · have hq0' : q = 0 := by
      simpa [q, DirectClosingTransverseAlignedSquareData.toAlignedSquareSource] using hq0
    have : Finsupp.weight
          (directClosingCanonicalSquareWeight B.aligned.endpoint.defect A.ell) d =
        4 * B.aligned.endpoint.defect := by
      rw [hq0'] at hlevel'
      simpa using hlevel'
    exact hwne (by simpa [d] using this)
  · have hqge' : B.aligned.endpoint.defect ≤ q := by
      simpa [heq, q, DirectClosingTransverseAlignedSquareData.toAlignedSquareSource,
        d] using hqge
    omega

/-- **Canonical transverse terminal square contact is impossible.** -/
theorem DirectClosingTransverseAlignedSquareData.canonicalTerminal_impossible
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (G : DirectClosingCanonicalSquareIntegralityData A.toAlignedSquareSource)
    (T : DirectClosingSquareFirstContactTerminalData
      (G.toFirstContactLattice heq)) : False := by
  let h := directClosingTransverseComplement A.ell
  have hh0 : h ≠ (0 : Fin 4) := by
    simpa [h] using directClosingTransverseComplement_ne_zero A.ell
  have hhell : h ≠ A.ell := by
    simpa [h] using directClosingTransverseComplement_ne_self A.ell A.ell_ne_zero
  have hrow := A.canonicalTerminal_highRow_zero heq G T h hh0 hhell
  have hdetzero : (quadraticFamilyHessianMatrix T.fibre).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero h
    exact hrow
  have hdetne : (quadraticFamilyHessianMatrix T.fibre).det ≠ 0 := by
    rw [quadraticFamilyHessianMatrix_det]
    have hMA := T.mongeAmpere
    unfold HC4.MongeAmpere.IsPolynomialMongeAmpere at hMA
    rw [hMA]
    simp
  exact hdetne hdetzero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
