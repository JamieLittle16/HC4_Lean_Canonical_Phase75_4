import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalImpossible
import Mathlib.Tactic

/-!
# Strict source clock carried by a canonical direct-closing earlier wall

The direct-closing equality branch has already ruled out every terminal
`j = Delta` square.  Its only remaining equality output is a concrete
canonical coefficient/section wall.  This file records the numerical fact
needed by the scale-sound restart assembly: every such wall occurs at an
exact parameter clock strictly below `Delta`, and therefore strictly below
`j` once the equality witness `j = Delta` is retained.

This is pure arithmetic/provenance.  No new geometric hypothesis and no JC2
input are introduced.
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

/-- Every coordinate of the canonical square weight is bounded by `3*Delta`. -/
theorem directClosingCanonicalSquareWeight_le_three_mul
    (Delta : ℕ) (i k : Fin 4) :
    directClosingCanonicalSquareWeight Delta i k ≤ 3 * Delta := by
  fin_cases i <;> fin_cases k <;>
    simp [directClosingCanonicalSquareWeight] <;> omega

/-- A family-side canonical wall has parameter order strictly below the
canonical defect clock.  The nonnegative source weight can only make the
wall earlier. -/
theorem canonicalEarlierWall_family_order_lt_defect
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ D.family.support)
    (hlt :
      directClosingCanonicalSquareRamification *
            smithFamilyCoefficientParameterOrder D.family d hd +
          Finsupp.weight
            (directClosingCanonicalSquareWeight
              B.aligned.endpoint.defect D.index) d <
        directClosingCanonicalSquareCommonLevel
          B.aligned.endpoint.defect) :
    smithFamilyCoefficientParameterOrder D.family d hd <
      B.aligned.endpoint.defect := by
  have hw :
      0 ≤ Finsupp.weight
        (directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index) d := Nat.zero_le _
  simp [directClosingCanonicalSquareRamification,
    directClosingCanonicalSquareCommonLevel] at hlt
  omega

/-- A moving-section canonical wall also has parameter order strictly below
`Delta`.  Here the sharper pointwise bound `W_i ≤ 3*Delta` is enough. -/
theorem canonicalEarlierWall_section_order_lt_defect
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hlt :
      directClosingCanonicalSquareRamification *
            polynomialParameterOrder (D.rightSection i) hi <
        directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index i) :
    polynomialParameterOrder (D.rightSection i) hi <
      B.aligned.endpoint.defect := by
  have hw := directClosingCanonicalSquareWeight_le_three_mul
    B.aligned.endpoint.defect D.index i
  simp [directClosingCanonicalSquareRamification] at hlt
  omega

/-- A section wall cannot be the marked longitudinal coordinate: its
canonical source weight there is zero. -/
theorem canonicalEarlierWall_section_index_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hlt :
      directClosingCanonicalSquareRamification *
            polynomialParameterOrder (D.rightSection i) hi <
        directClosingCanonicalSquareWeight
          B.aligned.endpoint.defect D.index i) :
    i ≠ (0 : Fin 4) := by
  intro hi0
  subst i
  simp at hlt

/-- Every non-longitudinal coordinate of a marked `-e₀` right section has
zero special value.  Hence a nonzero such coordinate has genuinely positive
exact parameter order. -/
theorem canonicalEarlierWall_section_order_pos
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hi0 : i ≠ (0 : Fin 4)) :
    0 < polynomialParameterOrder (D.rightSection i) hi := by
  have hspecial := congrFun D.rightSpecialPoint i
  have hconst : Polynomial.constantCoeff (D.rightSection i) = 0 := by
    change
      Polynomial.constantCoeff (D.rightSection i) =
        - coordinateAxisPoint (K := K) (0 : Fin 4) i at hspecial
    simpa [coordinateAxisPoint, hi0] using hspecial
  have hX : Polynomial.X ∣ D.rightSection i := by
    rw [Polynomial.X_dvd_iff]
    exact hconst
  have hle := polynomial_X_pow_dvd_le_parameterOrder
    (D.rightSection i) hi 1 (by simpa using hX)
  omega

/-- Refined numerical form of a canonical earlier wall at the equality
branch.  Whichever wall constructor occurs, it exposes an honest clock
`q < j`; the original wall evidence is retained verbatim for the subsequent
restart construction. -/
inductive DirectClosingCanonicalSquareStrictEarlierClock
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop
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
      (hclock :
        smithFamilyCoefficientParameterOrder D.family d hd <
          C.firstActualLayerOrder)
  | sectionWall
      (i : Fin 4)
      (hi : D.rightSection i ≠ 0)
      (hlt :
        directClosingCanonicalSquareRamification *
              polynomialParameterOrder (D.rightSection i) hi <
          directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index i)
      (hi0 : i ≠ (0 : Fin 4))
      (hclock :
        polynomialParameterOrder (D.rightSection i) hi <
          C.firstActualLayerOrder)

/-- Every canonical wall produced by the destroyed `j = Delta` terminal
branch carries a strictly smaller exact source/section clock. -/
theorem DirectClosingCanonicalSquareEarlierWall.toStrictEarlierClock
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (hwall : DirectClosingCanonicalSquareEarlierWall D)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingCanonicalSquareStrictEarlierClock D heq := by
  cases hwall with
  | family d hd hlt =>
      apply DirectClosingCanonicalSquareStrictEarlierClock.family d hd hlt
      rw [heq]
      exact canonicalEarlierWall_family_order_lt_defect D d hd hlt
  | sectionWall i hi hlt =>
      apply DirectClosingCanonicalSquareStrictEarlierClock.sectionWall i hi hlt
      · exact canonicalEarlierWall_section_index_ne_zero D i hi hlt
      · rw [heq]
        exact canonicalEarlierWall_section_order_lt_defect D i hi hlt




/-! ## Constant transverse shears preserve the first-actual-layer gap -/

/-- The same elementary transverse source transvection, now over the residue
field rather than over `Polynomial K`.  It is used only to identify the
parameter-constant part of a sheared polynomial family. -/
def transverseSourceShearVariableBase
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    MvPolynomial (Fin 4) K :=
  if i = k then
    MvPolynomial.X k + MvPolynomial.C a * MvPolynomial.X ell
  else
    MvPolynomial.X i

noncomputable def transverseSourceShearHomBase
    (k ell : Fin 4) (a : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (transverseSourceShearVariableBase k ell a)

/-- The parameter-constant embedding sends the residue-field shear variable
exactly to the polynomial-family shear variable. -/
theorem constantPolynomialFamily_transverseSourceShearVariableBase
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    constantPolynomialFamily
        (transverseSourceShearVariableBase k ell a i) =
      transverseSourceShearVariable (K := K) k ell (Polynomial.C a) i := by
  by_cases hi : i = k
  · subst i
    simp [constantPolynomialFamily, transverseSourceShearVariableBase,
      transverseSourceShearVariable]
  · simp [constantPolynomialFamily, transverseSourceShearVariableBase,
      transverseSourceShearVariable, hi]

/-- Embedding a field-valued source as a parameter-constant family commutes
with a parameter-constant transverse source shear. -/
theorem transverseSourceShearHom_constantPolynomialFamily
    (k ell : Fin 4) (a : K)
    (F : MvPolynomial (Fin 4) K) :
    transverseSourceShearHom (K := K) k ell (Polynomial.C a)
        (constantPolynomialFamily F) =
      constantPolynomialFamily
        (transverseSourceShearHomBase k ell a F) := by
  apply MvPolynomial.induction_on F
  · intro r
    simp [constantPolynomialFamily, transverseSourceShearHomBase]
  · intro P Q hP hQ
    have hadd := congrArg₂ (fun x y => x + y) hP hQ
    simpa [constantPolynomialFamily, map_add] using hadd
  · intro P i hP
    have hvar :=
      constantPolynomialFamily_transverseSourceShearVariableBase
        (K := K) k ell a i
    have hmul := congrArg₂ (fun x y => x * y) hP hvar.symm
    simpa [constantPolynomialFamily, map_mul, transverseSourceShearHomBase]
      using hmul

/-- Residue-field version of the canonical three transverse shears. -/
noncomputable def tripleTransverseSourceShearFamilyBase
    (k₁ k₂ k₃ ell : Fin 4) (a₁ a₂ a₃ : K)
    (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  transverseSourceShearHomBase k₃ ell a₃
    (transverseSourceShearHomBase k₂ ell a₂
      (transverseSourceShearHomBase k₁ ell a₁ F))

/-- Hence the canonical three-shear also preserves parameter-constant
families exactly. -/
theorem tripleTransverseSourceShearFamily_constantPolynomialFamily
    (k₁ k₂ k₃ ell : Fin 4) (a₁ a₂ a₃ : K)
    (F : MvPolynomial (Fin 4) K) :
    tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ (constantPolynomialFamily F) =
      constantPolynomialFamily
        (tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃ F) := by
  simp [tripleTransverseSourceShearFamily,
    tripleTransverseSourceShearFamilyBase,
    transverseSourceShearHom_constantPolynomialFamily]

/-- A polynomial of the form `C(a) + X^j r` cannot have a positive
`X`-adic valuation strictly below `j`. -/
theorem polynomialParameterOrder_eq_zero_of_constant_add_X_pow
    (p : Polynomial K) (hp : p ≠ 0)
    (j : ℕ)
    (hgap : ∃ a : K, ∃ r : Polynomial K,
      p = Polynomial.C a + Polynomial.X ^ j * r)
    (hlt : polynomialParameterOrder p hp < j) :
    polynomialParameterOrder p hp = 0 := by
  let q := polynomialParameterOrder p hp
  change q = 0
  by_contra hq0
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hqcoeff : p.coeff q ≠ 0 := by
    simpa [q] using polynomialParameterOrder_coeff_ne_zero p hp
  rcases hgap with ⟨a, r, hgap⟩
  have hlt' : q < j := by simpa [q] using hlt
  rw [hgap, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_X_pow_mul'] at hqcoeff
  simp [hq0, Nat.not_le_of_gt hlt'] at hqcoeff

namespace DirectClosingTransverseAlignedSquareData

/-- Exact `P_0 + X^j R` factorisation survives the canonical constant
three-shear.  This is the source-level reason the transverse alignment cannot
manufacture a new positive parameter layer below the original first actual
clock. -/
theorem family_firstActual_gap_factorisation
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C) :
    A.family =
      constantPolynomialFamily
        (tripleTransverseSourceShearFamilyBase
          A.k₁ A.k₂ A.k₃ A.ell A.a₁ A.a₂ A.a₃
          (polynomialFamilySpecialFiber C.family)) +
      MvPolynomial.C (Polynomial.X ^ C.firstActualLayerOrder) *
        tripleTransverseSourceShearFamily
          A.k₁ A.k₂ A.k₃ A.ell A.a₁ A.a₂ A.a₃
          C.relativeFirstActualDeformationFamily := by
  rw [DirectClosingTransverseAlignedSquareData.family]
  nth_rewrite 1 [C.relativeFirstActualDeformation_factorisation]
  simp only [tripleTransverseSourceShearFamily, map_add, map_mul,
    transverseSourceShearHom_C,
    transverseSourceShearHom_constantPolynomialFamily]
  rfl

/-- Every coefficient of the transversely aligned family still has no
positive parameter term below `j`: coefficientwise it is `C(a)+X^j r`. -/
theorem family_coefficient_firstActual_gap
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    (d : Fin 4 →₀ ℕ) :
    ∃ a : K, ∃ r : Polynomial K,
      MvPolynomial.coeff d A.family =
        Polynomial.C a + Polynomial.X ^ C.firstActualLayerOrder * r := by
  have h := congrArg (MvPolynomial.coeff d)
    A.family_firstActual_gap_factorisation
  rw [MvPolynomial.coeff_add, coeff_constantPolynomialFamily,
    MvPolynomial.coeff_C_mul] at h
  exact ⟨MvPolynomial.coeff d
      (tripleTransverseSourceShearFamilyBase
        A.k₁ A.k₂ A.k₃ A.ell A.a₁ A.a₂ A.a₃
        (polynomialFamilySpecialFiber C.family)),
    MvPolynomial.coeff d
      (tripleTransverseSourceShearFamily
        A.k₁ A.k₂ A.k₃ A.ell A.a₁ A.a₂ A.a₃
        C.relativeFirstActualDeformationFamily), h⟩

/-- **No spurious lower positive family clock under transverse alignment.**
If a supported coefficient of the honest three-shear has parameter order
strictly below the original first actual layer, that order is exactly zero. -/
theorem sourceCoefficientOrder_eq_zero_of_lt_firstActual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : DirectClosingTransverseAlignedSquareData C)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ A.family.support)
    (hlt : smithFamilyCoefficientParameterOrder A.family d hd <
      C.firstActualLayerOrder) :
    smithFamilyCoefficientParameterOrder A.family d hd = 0 := by
  have hp : MvPolynomial.coeff d A.family ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  exact polynomialParameterOrder_eq_zero_of_constant_add_X_pow
    (MvPolynomial.coeff d A.family) hp C.firstActualLayerOrder
    (A.family_coefficient_firstActual_gap d) (by
      simpa [smithFamilyCoefficientParameterOrder] using hlt)

end DirectClosingTransverseAlignedSquareData

/-! ## Source provenance of the equality spill -/

/-- The earlier wall produced after destroying the `j = Δ` terminal branch,
with the *actual source equivalence that produced it* retained.

The old existential `DirectClosingAlignedSquareSourceData` deliberately hid
whether the canonical square came from the original longitudinal source or
from the marked-axis-preserving transverse three-transvection.  That was fine
for terminal elimination, but it is too lossy for a source-honest restart. -/
inductive DirectClosingCanonicalSquareEarlierWallProvenance
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop
  | longitudinal
      (fresh : C.HasFreshDirectClosingSquareAt (0 : Fin 4))
      (hwall : DirectClosingCanonicalSquareEarlierWall
        (C.directClosingLongitudinalSquareSource fresh))
  | transverse
      (A : DirectClosingTransverseAlignedSquareData C)
      (hwall : DirectClosingCanonicalSquareEarlierWall
        A.toAlignedSquareSource)

/-- Equality `j = Δ` forces an earlier wall while retaining exactly which
honest source presentation generated that wall.  The terminal alternatives
are discharged by the already-green longitudinal and transverse terminal
contradictions. -/
theorem directClosing_equality_forces_provenancedEarlierWall
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingCanonicalSquareEarlierWallProvenance C := by
  rcases C.directClosing_freshLongitudinalSquare_or_transverseAlignedSquare heq with
    hlong | htrans
  · let D := C.directClosingLongitudinalSquareSource hlong
    rcases directClosingCanonicalSquare_terminal_or_earlierWall D heq with
      hterminal | hwall
    · rcases hterminal with ⟨G, hT⟩
      let S : DirectClosingLongitudinalCanonicalTerminalData C heq := {
        fresh := hlong
        integrality := G
        terminal := hT
      }
      exact False.elim S.impossible
    · exact .longitudinal hlong hwall
  · rcases htrans with ⟨A⟩
    let D := A.toAlignedSquareSource
    rcases directClosingCanonicalSquare_terminal_or_earlierWall D heq with
      hterminal | hwall
    · rcases hterminal with ⟨G, hT⟩
      rcases hT with ⟨T⟩
      exact False.elim (A.canonicalTerminal_impossible heq G T)
    · exact .transverse A hwall

/-- Provenance-preserving strict/equality frontier. -/
theorem firstActualLayer_strict_or_eq_and_provenancedEarlierWall
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.firstActualLayerOrder < B.aligned.endpoint.defect ∨
      (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
        DirectClosingCanonicalSquareEarlierWallProvenance C) := by
  rcases Nat.lt_or_eq_of_le C.firstActualLayerOrder_le_defect with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, C.directClosing_equality_forces_provenancedEarlierWall heq⟩

/-! ## Sharp wall normal form -/

/-- The equality spill, with the exact source clock normalised as far as the
currently proved source geometry permits.

For the original longitudinal source a family wall is *necessarily an old
special-fibre wall*: its exact parameter order is zero.  A section wall is a
genuine transverse moving-section departure with `0 < q < j`.

For the transverse-aligned source we retain the three-transvection data.  Its
section wall again has `0 < q < j`; a family wall already has `q < j`, and the
remaining transport lemma is precisely to show that a constant source
transvection cannot manufacture a positive parameter layer below the original
first actual layer. -/
inductive DirectClosingCanonicalSquareEarlierWallNormalForm
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop
  | longitudinalFamily
      (fresh : C.HasFreshDirectClosingSquareAt (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ (C.directClosingLongitudinalSquareSource fresh).family.support)
      (hlt :
        directClosingCanonicalSquareRamification *
              smithFamilyCoefficientParameterOrder
                (C.directClosingLongitudinalSquareSource fresh).family d hd +
            Finsupp.weight
              (directClosingCanonicalSquareWeight
                B.aligned.endpoint.defect
                (C.directClosingLongitudinalSquareSource fresh).index) d <
          directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      (horder0 :
        smithFamilyCoefficientParameterOrder
          (C.directClosingLongitudinalSquareSource fresh).family d hd = 0)
  | longitudinalSection
      (fresh : C.HasFreshDirectClosingSquareAt (0 : Fin 4))
      (i : Fin 4)
      (hi : (C.directClosingLongitudinalSquareSource fresh).rightSection i ≠ 0)
      (hlt :
        directClosingCanonicalSquareRamification *
              polynomialParameterOrder
                ((C.directClosingLongitudinalSquareSource fresh).rightSection i) hi <
          directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect
            (C.directClosingLongitudinalSquareSource fresh).index i)
      (hi0 : i ≠ (0 : Fin 4))
      (hpos :
        0 < polynomialParameterOrder
          ((C.directClosingLongitudinalSquareSource fresh).rightSection i) hi)
      (hclock :
        polynomialParameterOrder
            ((C.directClosingLongitudinalSquareSource fresh).rightSection i) hi <
          C.firstActualLayerOrder)
  | transverseFamily
      (A : DirectClosingTransverseAlignedSquareData C)
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ A.toAlignedSquareSource.family.support)
      (hlt :
        directClosingCanonicalSquareRamification *
              smithFamilyCoefficientParameterOrder
                A.toAlignedSquareSource.family d hd +
            Finsupp.weight
              (directClosingCanonicalSquareWeight
                B.aligned.endpoint.defect A.toAlignedSquareSource.index) d <
          directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      (hclock :
        smithFamilyCoefficientParameterOrder A.toAlignedSquareSource.family d hd <
          C.firstActualLayerOrder)
      (horder0 :
        smithFamilyCoefficientParameterOrder A.toAlignedSquareSource.family d hd = 0)
  | transverseSection
      (A : DirectClosingTransverseAlignedSquareData C)
      (i : Fin 4)
      (hi : A.toAlignedSquareSource.rightSection i ≠ 0)
      (hlt :
        directClosingCanonicalSquareRamification *
              polynomialParameterOrder (A.toAlignedSquareSource.rightSection i) hi <
          directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect A.toAlignedSquareSource.index i)
      (hi0 : i ≠ (0 : Fin 4))
      (hpos :
        0 < polynomialParameterOrder (A.toAlignedSquareSource.rightSection i) hi)
      (hclock :
        polynomialParameterOrder (A.toAlignedSquareSource.rightSection i) hi <
          C.firstActualLayerOrder)

/-- A provenance-carrying equality spill has the sharp four-way clock normal
form above. -/
theorem DirectClosingCanonicalSquareEarlierWallProvenance.toNormalForm
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (P : DirectClosingCanonicalSquareEarlierWallProvenance C)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingCanonicalSquareEarlierWallNormalForm C heq := by
  cases P with
  | longitudinal fresh hwall =>
      cases hwall with
      | family d hd hlt =>
          have hclock :
              smithFamilyCoefficientParameterOrder
                  (C.directClosingLongitudinalSquareSource fresh).family d hd <
                C.firstActualLayerOrder := by
            rw [heq]
            exact canonicalEarlierWall_family_order_lt_defect
              (C.directClosingLongitudinalSquareSource fresh) d hd hlt
          have hdC : d ∈ C.family.support := by
            simpa [directClosingLongitudinalSquareSource] using hd
          have hcases := C.sourceCoefficientOrder_eq_zero_or_firstActual_le hdC
          have horder0 :
              smithFamilyCoefficientParameterOrder
                  (C.directClosingLongitudinalSquareSource fresh).family d hd = 0 := by
            rcases hcases with hzero | hge
            · simpa [directClosingLongitudinalSquareSource] using hzero
            · have hge' :
                  C.firstActualLayerOrder ≤
                    smithFamilyCoefficientParameterOrder
                      (C.directClosingLongitudinalSquareSource fresh).family d hd := by
                simpa [directClosingLongitudinalSquareSource] using hge
              omega
          exact .longitudinalFamily fresh d hd hlt horder0
      | sectionWall i hi hlt =>
          have hi0 := canonicalEarlierWall_section_index_ne_zero
            (C.directClosingLongitudinalSquareSource fresh) i hi hlt
          have hpos := canonicalEarlierWall_section_order_pos
            (C.directClosingLongitudinalSquareSource fresh) i hi hi0
          have hclock :
              polynomialParameterOrder
                  ((C.directClosingLongitudinalSquareSource fresh).rightSection i) hi <
                C.firstActualLayerOrder := by
            rw [heq]
            exact canonicalEarlierWall_section_order_lt_defect
              (C.directClosingLongitudinalSquareSource fresh) i hi hlt
          exact .longitudinalSection fresh i hi hlt hi0 hpos hclock
  | transverse A hwall =>
      cases hwall with
      | family d hd hlt =>
          have hclock :
              smithFamilyCoefficientParameterOrder
                  A.toAlignedSquareSource.family d hd <
                C.firstActualLayerOrder := by
            rw [heq]
            exact canonicalEarlierWall_family_order_lt_defect
              A.toAlignedSquareSource d hd hlt
          have hdA : d ∈ A.family.support := by
            simpa [DirectClosingTransverseAlignedSquareData.toAlignedSquareSource] using hd
          have hclockA :
              smithFamilyCoefficientParameterOrder A.family d hdA <
                C.firstActualLayerOrder := by
            simpa [DirectClosingTransverseAlignedSquareData.toAlignedSquareSource] using hclock
          have horder0A :=
            A.sourceCoefficientOrder_eq_zero_of_lt_firstActual d hdA hclockA
          have horder0 :
              smithFamilyCoefficientParameterOrder
                A.toAlignedSquareSource.family d hd = 0 := by
            simpa [DirectClosingTransverseAlignedSquareData.toAlignedSquareSource] using horder0A
          exact .transverseFamily A d hd hlt hclock horder0
      | sectionWall i hi hlt =>
          have hi0 := canonicalEarlierWall_section_index_ne_zero
            A.toAlignedSquareSource i hi hlt
          have hpos := canonicalEarlierWall_section_order_pos
            A.toAlignedSquareSource i hi hi0
          have hclock :
              polynomialParameterOrder (A.toAlignedSquareSource.rightSection i) hi <
                C.firstActualLayerOrder := by
            rw [heq]
            exact canonicalEarlierWall_section_order_lt_defect
              A.toAlignedSquareSource i hi hlt
          exact .transverseSection A i hi hlt hi0 hpos hclock

end AdaptiveAlignedSmithRankOneClosingSourceCarrier


end

end HC4.Valuation
