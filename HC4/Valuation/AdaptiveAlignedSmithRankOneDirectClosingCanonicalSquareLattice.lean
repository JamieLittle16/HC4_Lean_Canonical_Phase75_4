import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingSquareContactSource
import Mathlib.Tactic

/-!
# Canonical terminal arithmetic for a direct-closing fresh square

At `j = Delta` the previous green modules produce an honest marked source
family with a distinguished fresh square of exact order `Delta`.  The
remaining Newton step was phrased as a search for arbitrary integers
`R > 0`, source weights `W`, and common level `m`.

For a square there is a canonical terminal arithmetic candidate, so no such
search is necessary.  We take

* `R = 4`;
* `m = 4 * Delta`;
* source weight zero on the marked longitudinal coordinate `0`;
* source weight zero on the square coordinate;
* total source weight `6 * Delta`.

Concretely, if the square is longitudinal, each of the three transverse
coordinates receives weight `2 * Delta`.  If the square is transverse, the
two coordinates complementary to `{0, i}` each receive weight `3 * Delta`.
Thus in every case

    sum W = 6 Delta,
    weight_W(X_i^2) = 0,
    4 Delta + 2 sum W - 4 (4 Delta) = 0.

Hence the distinguished square lands exactly at the divided level and the
transformed Hessian defect is exactly zero.  The only remaining issue for
this canonical candidate is honest coefficient/section integrality.

This file packages those two integrality gates and proves an exhaustive
finite obstruction dichotomy.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Canonical terminal source weight attached to a distinguished square.

If `i = 0`, all three transverse coordinates have weight `2*Delta`.
If `i != 0`, the marked coordinate `0` and the square coordinate `i` have
weight zero, while the two complementary coordinates have weight `3*Delta`.
-/
def directClosingCanonicalSquareWeight
    (Delta : ℕ) (i k : Fin 4) : ℕ :=
  if hi : i = 0 then
    if hk : k = 0 then 0 else 2 * Delta
  else
    if hk0 : k = 0 then 0
    else if hki : k = i then 0 else 3 * Delta

@[simp] theorem directClosingCanonicalSquareWeight_zero
    (Delta : ℕ) (i : Fin 4) :
    directClosingCanonicalSquareWeight Delta i 0 = 0 := by
  by_cases hi : i = 0 <;>
    simp [directClosingCanonicalSquareWeight, hi]

@[simp] theorem directClosingCanonicalSquareWeight_index
    (Delta : ℕ) (i : Fin 4) :
    directClosingCanonicalSquareWeight Delta i i = 0 := by
  by_cases hi : i = 0
  · subst i
    simp [directClosingCanonicalSquareWeight]
  · simp [directClosingCanonicalSquareWeight, hi]

/-- The canonical square weight always has total source weight `6*Delta`. -/
theorem directClosingCanonicalSquareWeight_sum
    (Delta : ℕ) (i : Fin 4) :
    (∑ k : Fin 4, directClosingCanonicalSquareWeight Delta i k) =
      6 * Delta := by
  fin_cases i <;>
    simp [directClosingCanonicalSquareWeight, Fin.sum_univ_four] <;>
    omega

/-- The distinguished square itself has source weight zero. -/
theorem directClosingCanonicalSquareWeight_squareExponent
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) :
    Finsupp.weight
        (directClosingCanonicalSquareWeight B.aligned.endpoint.defect D.index)
        D.squareExponent = 0 := by
  simp [DirectClosingAlignedSquareSourceData.squareExponent,
    directClosingQuadraticExponent, Finsupp.weight_single]

/-- Canonical ramification for square terminal arithmetic. -/
def directClosingCanonicalSquareRamification : ℕ := 4

@[simp] theorem directClosingCanonicalSquareRamification_pos :
    0 < directClosingCanonicalSquareRamification := by
  norm_num [directClosingCanonicalSquareRamification]

/-- Canonical common divided level. -/
def directClosingCanonicalSquareCommonLevel (Delta : ℕ) : ℕ :=
  4 * Delta

/-- The canonical square arithmetic makes the determinant exponent exactly
zero. -/
theorem directClosingCanonicalSquare_terminalArithmetic
    (Delta : ℕ) (i : Fin 4) :
    directClosingCanonicalSquareRamification * Delta +
        2 * ∑ k : Fin 4, directClosingCanonicalSquareWeight Delta i k =
      4 * directClosingCanonicalSquareCommonLevel Delta := by
  rw [directClosingCanonicalSquareWeight_sum]
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel]
  omega

/-- In particular the nonnegativity gate for the Hessian exponent is an
exact equality for the canonical square candidate. -/
theorem directClosingCanonicalSquare_determinantExponentNonnegative
    (Delta : ℕ) (i : Fin 4) :
    4 * directClosingCanonicalSquareCommonLevel Delta ≤
      directClosingCanonicalSquareRamification * Delta +
        2 * ∑ k : Fin 4, directClosingCanonicalSquareWeight Delta i k := by
  rw [directClosingCanonicalSquare_terminalArithmetic]

/-- At `j = Delta`, the fresh square lands exactly on the canonical common
level. -/
theorem DirectClosingAlignedSquareSourceData.canonicalSquareContactLevel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    directClosingCanonicalSquareRamification * C.firstActualLayerOrder +
        Finsupp.weight
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index)
          D.squareExponent =
      directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect := by
  rw [directClosingCanonicalSquareWeight_squareExponent D]
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel, heq]

/-! ## The two honest integrality gates -/

/-- The only extra data needed to realise the canonical square arithmetic as
an honest polynomial source exposure. -/
structure DirectClosingCanonicalSquareIntegralityData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) where
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure
      directClosingCanonicalSquareRamification
      (directClosingCanonicalSquareWeight
        B.aligned.endpoint.defect D.index)
      (directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      D.family
  rightSectionIntegrality :
    HasIntegralAdaptiveSmithSection
      (directClosingCanonicalSquareWeight
        B.aligned.endpoint.defect D.index)
      (parameterRamificationSection
        (K := K) directClosingCanonicalSquareRamification D.rightSection)

/-- Once the two integrality gates hold, the canonical arithmetic is an
honest square first-contact lattice. -/
noncomputable def DirectClosingCanonicalSquareIntegralityData.toFirstContactLattice
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (G : DirectClosingCanonicalSquareIntegralityData D)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingSquareFirstContactLatticeData D where
  weight := directClosingCanonicalSquareWeight
    B.aligned.endpoint.defect D.index
  commonLevel := directClosingCanonicalSquareCommonLevel
    B.aligned.endpoint.defect
  R := directClosingCanonicalSquareRamification
  R_pos := directClosingCanonicalSquareRamification_pos
  familyIntegrality := G.familyIntegrality
  rightSectionIntegrality := G.rightSectionIntegrality
  determinantExponentNonnegative :=
    directClosingCanonicalSquare_determinantExponentNonnegative
      B.aligned.endpoint.defect D.index
  squareContactLevel := D.canonicalSquareContactLevel heq

/-- The canonical square lattice is already terminal: its transformed pure
Hessian defect is exactly zero. -/
theorem DirectClosingCanonicalSquareIntegralityData.firstContact_defect_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (G : DirectClosingCanonicalSquareIntegralityData D)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (G.toFirstContactLattice heq).defect = 0 := by
  change
    directClosingCanonicalSquareRamification * B.aligned.endpoint.defect +
        2 * ∑ i : Fin 4,
          directClosingCanonicalSquareWeight B.aligned.endpoint.defect D.index i -
      4 * directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect = 0
  rw [directClosingCanonicalSquareWeight_sum]
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel]
  omega

/-- Hence honest integrality of the canonical square candidate directly
constructs a terminal first-contact Monge--Ampere collision fibre. -/
noncomputable def DirectClosingCanonicalSquareIntegralityData.toTerminalData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (G : DirectClosingCanonicalSquareIntegralityData D)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingSquareFirstContactTerminalData
      (G.toFirstContactLattice heq) where
  terminalDefect := G.firstContact_defect_zero heq

/-! ## Exact finite obstruction frontier -/

/-- Failure of the canonical candidate is witnessed either by an actual
source coefficient which is not divisible to the canonical common level, or
by an actual moving-section coordinate which is not divisible by its
canonical source weight. -/
inductive DirectClosingCanonicalSquareIntegralityObstruction
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) : Prop
  | family
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ D.family.support)
      (hnot :
        ¬ Polynomial.X ^
            (directClosingCanonicalSquareCommonLevel
              B.aligned.endpoint.defect) ∣
          adaptiveSmithExposureCoefficientFactor
            directClosingCanonicalSquareRamification
            (directClosingCanonicalSquareWeight
              B.aligned.endpoint.defect D.index)
            D.family d)
  | sectionObstruction
      (i : Fin 4)
      (hnot :
        ¬ Polynomial.X ^
            (directClosingCanonicalSquareWeight
              B.aligned.endpoint.defect D.index i) ∣
          parameterRamificationSection
            (K := K) directClosingCanonicalSquareRamification
            D.rightSection i)

/-- The canonical square candidate has an exhaustive gate/obstruction split.
This is finite because `D.family.support` and `Fin 4` are finite. -/
theorem directClosingCanonicalSquare_integral_or_obstruction
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) :
    Nonempty (DirectClosingCanonicalSquareIntegralityData D) ∨
      DirectClosingCanonicalSquareIntegralityObstruction D := by
  classical
  by_cases hfamily :
      HasIntegralAdaptiveSmithExposure
        directClosingCanonicalSquareRamification
        (directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index)
        (directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
        D.family
  · by_cases hsection :
      HasIntegralAdaptiveSmithSection
        (directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index)
        (parameterRamificationSection
          (K := K) directClosingCanonicalSquareRamification D.rightSection)
    · left
      exact ⟨{
        familyIntegrality := hfamily
        rightSectionIntegrality := hsection
      }⟩
    · right
      unfold HasIntegralAdaptiveSmithSection at hsection
      push_neg at hsection
      rcases hsection with ⟨i, hi⟩
      exact .sectionObstruction i hi
  · right
    unfold HasIntegralAdaptiveSmithExposure at hfamily
    push_neg at hfamily
    rcases hfamily with ⟨d, hd, hnot⟩
    exact .family d hd hnot


/-- A failed canonical integrality gate is equivalently an *earlier wall* in
numerical order arithmetic.  This is the form needed by the restart/first-wall
machinery: either an actual family coefficient reaches the canonical ray
strictly before the square level, or a moving-section coordinate reaches its
source boundary strictly before its assigned weight. -/
inductive DirectClosingCanonicalSquareEarlierWall
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) : Prop
  | family
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ D.family.support)
      (hlt :
        directClosingCanonicalSquareRamification *
              smithFamilyCoefficientParameterOrder D.family d hd +
            Finsupp.weight
              (directClosingCanonicalSquareWeight
                B.aligned.endpoint.defect D.index) d <
          directClosingCanonicalSquareCommonLevel
            B.aligned.endpoint.defect)
  | sectionWall
      (i : Fin 4)
      (hi : D.rightSection i ≠ 0)
      (hlt :
        directClosingCanonicalSquareRamification *
              polynomialParameterOrder (D.rightSection i) hi <
          directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index i)

/-- Nondivisibility of a supported coefficient at the canonical common level
forces a strictly earlier coefficient wall. -/
theorem familyIntegralityObstruction_to_earlierWall
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ D.family.support)
    (hnot :
      ¬ Polynomial.X ^
          (directClosingCanonicalSquareCommonLevel
            B.aligned.endpoint.defect) ∣
        adaptiveSmithExposureCoefficientFactor
          directClosingCanonicalSquareRamification
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index)
          D.family d) :
    directClosingCanonicalSquareRamification *
          smithFamilyCoefficientParameterOrder D.family d hd +
        Finsupp.weight
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index) d <
      directClosingCanonicalSquareCommonLevel
        B.aligned.endpoint.defect := by
  let q := smithFamilyCoefficientParameterOrder D.family d hd
  let w := Finsupp.weight
    (directClosingCanonicalSquareWeight B.aligned.endpoint.defect D.index) d
  let total := directClosingCanonicalSquareRamification * q + w
  have hqdiv : Polynomial.X ^ q ∣ MvPolynomial.coeff d D.family := by
    simpa [q] using smithFamilyCoefficientParameterOrder_dvd D.family d hd
  have hramdiv :
      Polynomial.X ^ (directClosingCanonicalSquareRamification * q) ∣
        parameterRamificationHom (K := K)
          directClosingCanonicalSquareRamification
          (MvPolynomial.coeff d D.family) := by
    exact parameterRamification_pow_dvd
      directClosingCanonicalSquareRamification q
      (MvPolynomial.coeff d D.family) hqdiv
  rcases hramdiv with ⟨r, hr⟩
  have htotaldiv :
      Polynomial.X ^ total ∣
        adaptiveSmithExposureCoefficientFactor
          directClosingCanonicalSquareRamification
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index)
          D.family d := by
    refine ⟨r, ?_⟩
    unfold adaptiveSmithExposureCoefficientFactor
    dsimp [total, w]
    rw [hr, pow_add]
    ring
  change total < directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect
  by_contra hlt
  have hle :
      directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect ≤
        total := Nat.le_of_not_gt hlt
  have hpow :
      Polynomial.X ^
          (directClosingCanonicalSquareCommonLevel
            B.aligned.endpoint.defect) ∣
        (Polynomial.X : Polynomial K) ^ total :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      total hle
  exact hnot (dvd_trans hpow htotaldiv)

/-- Nondivisibility of a ramified moving-section coordinate forces a strictly
earlier section wall on the same canonical ray. -/
theorem sectionIntegralityObstruction_to_earlierWall
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hnot :
      ¬ Polynomial.X ^
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index i) ∣
        parameterRamificationSection
          (K := K) directClosingCanonicalSquareRamification
          D.rightSection i) :
    ∃ hi : D.rightSection i ≠ 0,
      directClosingCanonicalSquareRamification *
            polynomialParameterOrder (D.rightSection i) hi <
        directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index i := by
  have hi : D.rightSection i ≠ 0 := by
    intro hz
    apply hnot
    simp [parameterRamificationSection, hz]
  refine ⟨hi, ?_⟩
  let q := polynomialParameterOrder (D.rightSection i) hi
  have hqdiv : Polynomial.X ^ q ∣ D.rightSection i := by
    simpa [q] using polynomialParameterOrder_dvd (D.rightSection i) hi
  have hramdiv :
      Polynomial.X ^ (directClosingCanonicalSquareRamification * q) ∣
        parameterRamificationHom (K := K)
          directClosingCanonicalSquareRamification (D.rightSection i) := by
    exact parameterRamification_pow_dvd
      directClosingCanonicalSquareRamification q (D.rightSection i) hqdiv
  change
    directClosingCanonicalSquareRamification * q <
      directClosingCanonicalSquareWeight B.aligned.endpoint.defect D.index i
  by_contra hlt
  have hle :
      directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index i ≤
        directClosingCanonicalSquareRamification * q :=
    Nat.le_of_not_gt hlt
  have hpow :
      Polynomial.X ^
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index i) ∣
        (Polynomial.X : Polynomial K) ^
          (directClosingCanonicalSquareRamification * q) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (directClosingCanonicalSquareWeight
        B.aligned.endpoint.defect D.index i)
      (directClosingCanonicalSquareRamification * q) hle
  apply hnot
  simpa [parameterRamificationSection, q] using dvd_trans hpow hramdiv

/-- Every raw canonical integrality obstruction has a strictly-earlier-wall
interpretation. -/
theorem DirectClosingCanonicalSquareIntegralityObstruction.toEarlierWall
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (h : DirectClosingCanonicalSquareIntegralityObstruction D) :
    DirectClosingCanonicalSquareEarlierWall D := by
  cases h with
  | family d hd hnot =>
      exact .family d hd
        (familyIntegralityObstruction_to_earlierWall D d hd hnot)
  | sectionObstruction i hnot =>
      rcases sectionIntegralityObstruction_to_earlierWall D i hnot with
        ⟨hi, hlt⟩
      exact .sectionWall i hi hlt

/-- The canonical square candidate therefore gives an exact dichotomy:
either an honest terminal first-contact fibre is already available, or the
same ray exhibits a concrete earlier coefficient/section wall. -/
theorem directClosingCanonicalSquare_terminal_or_earlierWall
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (∃ G : DirectClosingCanonicalSquareIntegralityData D,
      Nonempty (DirectClosingSquareFirstContactTerminalData
        (G.toFirstContactLattice heq))) ∨
      DirectClosingCanonicalSquareEarlierWall D := by
  rcases directClosingCanonicalSquare_integral_or_obstruction D with
    hG | hobs
  · rcases hG with ⟨G⟩
    left
    exact ⟨G, ⟨G.toTerminalData heq⟩⟩
  · right
    exact hobs.toEarlierWall

/-- **Canonical terminal-square frontier at direct closing.**

At `j = Delta`, choose the already-green aligned fresh-square source.  Either
its canonical square lattice is honestly integral, in which case we obtain a
terminal first-contact fibre immediately, or one explicit finite
coefficient/section divisibility obstruction remains.  There is no longer an
unbounded search over supporting lattices. -/
theorem directClosing_canonicalTerminalSquare_or_integralityObstruction
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (∃ (D : DirectClosingAlignedSquareSourceData C)
        (G : DirectClosingCanonicalSquareIntegralityData D),
      Nonempty (DirectClosingSquareFirstContactTerminalData
        (G.toFirstContactLattice heq))) ∨
      (∃ D : DirectClosingAlignedSquareSourceData C,
        DirectClosingCanonicalSquareIntegralityObstruction D) := by
  let D := Classical.choice (C.directClosing_exists_alignedSquareSource heq)
  rcases directClosingCanonicalSquare_integral_or_obstruction D with
    hG | hobs
  · rcases hG with ⟨G⟩
    left
    refine ⟨D, G, ?_⟩
    exact ⟨G.toTerminalData heq⟩
  · right
    exact ⟨D, hobs⟩



/-- **Canonical terminal-or-earlier-wall frontier at direct closing.**

At `j = Delta`, the fresh-square source therefore either reaches an honest
terminal first-contact fibre on the canonical ray or produces an explicit
strictly earlier coefficient/section wall on that same ray. -/
theorem directClosing_canonicalTerminalSquare_or_earlierWall
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (∃ (D : DirectClosingAlignedSquareSourceData C)
        (G : DirectClosingCanonicalSquareIntegralityData D),
      Nonempty (DirectClosingSquareFirstContactTerminalData
        (G.toFirstContactLattice heq))) ∨
      (∃ D : DirectClosingAlignedSquareSourceData C,
        DirectClosingCanonicalSquareEarlierWall D) := by
  let D := Classical.choice (C.directClosing_exists_alignedSquareSource heq)
  rcases directClosingCanonicalSquare_terminal_or_earlierWall D heq with
    hterm | hwall
  · left
    rcases hterm with ⟨G, hT⟩
    exact ⟨D, G, hT⟩
  · right
    exact ⟨D, hwall⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
