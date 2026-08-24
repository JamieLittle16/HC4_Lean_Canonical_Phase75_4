import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingEarlierWallClock
import HC4.Valuation.PointedShearContinuation
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Positive direct-closing section walls are pointed source gauge

After the terminal `j = Δ` square has been eliminated, every positive
section-side earlier wall has an exact order `q` with

    0 < q < j.

Such a wall is an earlier motion of the marked right section.  Because the
longitudinal special coordinate of every direct-closing square source is
exactly `-1`, one determinant-one pointed shear

    X_i ↦ X_i + c X_0

with `c` a single parameter monomial of order `q` kills the leading
coefficient of that transverse section coordinate.

This file proves the step source-honestly:

* the shear coefficient has zero special value;
* the special fibre is therefore unchanged;
* the exact Hessian determinant clock is unchanged;
* the exact zero-left gradient collision is unchanged;
* the marked special point stays `-e₀`;
* the offending coefficient at order `q` is killed;
* all lower coefficients stay zero, so if the transformed coordinate is
  nonzero its exact parameter order is strictly larger than `q`.

Thus a positive section wall carries an honest pointed gauge-normalisation
step, not a new Keller/terminal branch.

Important: a parameter-dependent source shear can create a positive *family*
layer at the same order `q`.  This file deliberately does **not** claim that
the literal `firstActualLayerOrder` of the transformed family remains `j`.
The next reduced-deformation layer must identify that new order-`q` term as
pure source gauge before quotienting/iterating it.  Keeping this distinction
explicit avoids reintroducing the false invariant that motivated the earlier
wall audit.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Generic zero-special-value shear facts -/

/-- An elementary inverse shear with coefficient of zero special value does
not move the special point of a polynomial section. -/
theorem polynomialSectionSpecialPoint_elementaryUnshear_of_constantCoeff_zero
    (k : Fin 4)
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K)
    (hc0 : Polynomial.constantCoeff c = 0) :
    polynomialSectionSpecialPoint (elementaryUnshearSection k c a) =
      polynomialSectionSpecialPoint a := by
  have hc0' : c.coeff 0 = 0 := by
    change c.coeff 0 = 0 at hc0
    exact hc0
  funext i
  by_cases hik : i = k
  · subst i
    simp [polynomialSectionSpecialPoint, elementaryUnshearSection, hc0']
  · simp [polynomialSectionSpecialPoint, elementaryUnshearSection, hik]

/-- A source shear whose coefficient vanishes at the parameter origin acts
trivially on the polynomial-family special fibre. -/
theorem polynomialFamilySpecialFiber_elementaryShear_of_constantCoeff_zero
    (k : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hc0 : Polynomial.constantCoeff c = 0) :
    polynomialFamilySpecialFiber (elementaryShearHom (K := K) k c P) =
      polynomialFamilySpecialFiber P := by
  apply MvPolynomial.induction_on P
  · intro r
    simp [polynomialFamilySpecialFiber, elementaryShearHom]
  · intro p q hp hq
    simpa [polynomialFamilySpecialFiber] using
      congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    have hvar :
        polynomialFamilySpecialFiber
            (elementaryShearVariable (K := K) k c i) =
          MvPolynomial.X i := by
      by_cases hik : i = k
      · subst i
        simp [polynomialFamilySpecialFiber, elementaryShearVariable, hc0]
      · simp [polynomialFamilySpecialFiber, elementaryShearVariable, hik]
    have hmul := congrArg₂ (fun x y => x * y) hp hvar
    simpa [polynomialFamilySpecialFiber, map_mul,
      elementaryShearHom_X] using hmul

/-! ## One leading-coefficient gauge cancellation -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

namespace DirectClosingAlignedSquareSourceData

/-- Exact parameter order of one nonzero moving-section coordinate. -/
noncomputable def sectionGaugeOrder
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) : ℕ :=
  polynomialParameterOrder (D.rightSection i) hi

/-- Pointed shear coefficient which kills the leading coefficient of the
chosen moving-section coordinate.  The minus sign is forced by the fact that
the longitudinal special coordinate is `-1`. -/
noncomputable def sectionGaugeCoefficient
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) : Polynomial K :=
  Polynomial.C
      (- (D.rightSection i).coeff (D.sectionGaugeOrder i hi)) *
    Polynomial.X ^ (D.sectionGaugeOrder i hi)

/-- Family after the one-step pointed gauge correction. -/
noncomputable def sectionGaugeFamily
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  elementaryShearHom (K := K) i (D.sectionGaugeCoefficient i hi) D.family

/-- Right moving section after the inverse action of the same gauge shear. -/
noncomputable def sectionGaugeRightSection
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) : Fin 4 → Polynomial K :=
  elementaryUnshearSection i (D.sectionGaugeCoefficient i hi) D.rightSection

/-- The gauge coefficient has zero special value whenever the wall order is
positive. -/
theorem sectionGaugeCoefficient_constantCoeff_zero
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hpos : 0 < D.sectionGaugeOrder i hi) :
    Polynomial.constantCoeff (D.sectionGaugeCoefficient i hi) = 0 := by
  change (D.sectionGaugeCoefficient i hi).coeff 0 = 0
  have h0q : 0 ≠ D.sectionGaugeOrder i hi := Ne.symm (Nat.ne_of_gt hpos)
  simp [sectionGaugeCoefficient, Polynomial.coeff_C_mul_X_pow, h0q]

/-- The direct-closing marked point has longitudinal coefficient `-1`. -/
theorem rightSection_zero_coeff_zero
    (D : DirectClosingAlignedSquareSourceData C) :
    (D.rightSection (0 : Fin 4)).coeff 0 = -1 := by
  have h0 := congrFun D.rightSpecialPoint (0 : Fin 4)
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using h0

/-- The selected section coordinate has no coefficient below its exact
parameter order. -/
theorem rightSection_coeff_eq_zero_of_lt_sectionGaugeOrder
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    {n : ℕ}
    (hn : n < D.sectionGaugeOrder i hi) :
    (D.rightSection i).coeff n = 0 := by
  have hdiv := polynomialParameterOrder_dvd (D.rightSection i) hi
  rw [Polynomial.X_pow_dvd_iff] at hdiv
  exact hdiv n (by simpa [sectionGaugeOrder] using hn)

/-- At the chosen order, multiplying the gauge monomial by the longitudinal
section recovers exactly the coefficient that we want to cancel. -/
theorem sectionGaugeCoefficient_mul_zeroSection_coeff_order
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) :
    (D.sectionGaugeCoefficient i hi * D.rightSection (0 : Fin 4)).coeff
        (D.sectionGaugeOrder i hi) =
      (D.rightSection i).coeff (D.sectionGaugeOrder i hi) := by
  let q := D.sectionGaugeOrder i hi
  let a := (D.rightSection i).coeff q
  have hzero := D.rightSection_zero_coeff_zero
  change
    ((Polynomial.C (-a) * Polynomial.X ^ q) *
        D.rightSection (0 : Fin 4)).coeff q = a
  rw [show
      (Polynomial.C (-a) * Polynomial.X ^ q) *
          D.rightSection (0 : Fin 4) =
        Polynomial.C (-a) *
          (Polynomial.X ^ q * D.rightSection (0 : Fin 4)) by ring]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  simp [hzero]

/-- The pointed gauge kills the offending leading section coefficient. -/
theorem sectionGaugeRightSection_coeff_order_eq_zero
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0) :
    (D.sectionGaugeRightSection i hi i).coeff
        (D.sectionGaugeOrder i hi) = 0 := by
  simp only [sectionGaugeRightSection, elementaryUnshearSection, if_pos]
  rw [Polynomial.coeff_sub,
    D.sectionGaugeCoefficient_mul_zeroSection_coeff_order i hi]
  ring

/-- Below the old exact order, the gauge correction contributes nothing. -/
theorem sectionGaugeRightSection_coeff_eq_zero_of_lt
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    {n : ℕ}
    (hn : n < D.sectionGaugeOrder i hi) :
    (D.sectionGaugeRightSection i hi i).coeff n = 0 := by
  have hold := D.rightSection_coeff_eq_zero_of_lt_sectionGaugeOrder i hi hn
  simp only [sectionGaugeRightSection, elementaryUnshearSection, if_pos,
    Polynomial.coeff_sub]
  rw [hold]
  have hprod :
      (D.sectionGaugeCoefficient i hi * D.rightSection (0 : Fin 4)).coeff n = 0 := by
    let q := D.sectionGaugeOrder i hi
    let a := (D.rightSection i).coeff q
    change
      ((Polynomial.C (-a) * Polynomial.X ^ q) *
          D.rightSection (0 : Fin 4)).coeff n = 0
    rw [show
        (Polynomial.C (-a) * Polynomial.X ^ q) *
            D.rightSection (0 : Fin 4) =
          Polynomial.C (-a) *
            (Polynomial.X ^ q * D.rightSection (0 : Fin 4)) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hnq : ¬ q ≤ n := by
      simpa [q] using (Nat.not_le_of_gt hn)
    simp [hnq]
  rw [hprod]
  simp

/-- Hence, unless the corrected coordinate vanishes identically, its exact
parameter order strictly increases. -/
theorem sectionGaugeRightSection_order_strict
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hnew : D.sectionGaugeRightSection i hi i ≠ 0) :
    D.sectionGaugeOrder i hi <
      polynomialParameterOrder (D.sectionGaugeRightSection i hi i) hnew := by
  by_contra hnot
  have hle :
      polynomialParameterOrder (D.sectionGaugeRightSection i hi i) hnew ≤
        D.sectionGaugeOrder i hi :=
    Nat.le_of_not_gt hnot
  have hcoeffne :
      (D.sectionGaugeRightSection i hi i).coeff
          (polynomialParameterOrder (D.sectionGaugeRightSection i hi i) hnew) ≠ 0 :=
    polynomialParameterOrder_coeff_ne_zero
      (D.sectionGaugeRightSection i hi i) hnew
  have hcoeffzero :
      (D.sectionGaugeRightSection i hi i).coeff
          (polynomialParameterOrder (D.sectionGaugeRightSection i hi i) hnew) = 0 := by
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact D.sectionGaugeRightSection_coeff_eq_zero_of_lt i hi hlt
    · rw [heq]
      exact D.sectionGaugeRightSection_coeff_order_eq_zero i hi
  exact hcoeffne hcoeffzero

/-- The gauge does not change the special fibre of the family. -/
theorem sectionGaugeFamily_specialFiber
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hpos : 0 < D.sectionGaugeOrder i hi) :
    polynomialFamilySpecialFiber (D.sectionGaugeFamily i hi) =
      polynomialFamilySpecialFiber D.family := by
  unfold sectionGaugeFamily
  exact polynomialFamilySpecialFiber_elementaryShear_of_constantCoeff_zero
    i (D.sectionGaugeCoefficient i hi) D.family
    (D.sectionGaugeCoefficient_constantCoeff_zero i hi hpos)

/-- The marked special point remains exactly `-e₀`. -/
theorem sectionGaugeRightSection_specialPoint
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hpos : 0 < D.sectionGaugeOrder i hi) :
    polynomialSectionSpecialPoint (D.sectionGaugeRightSection i hi) =
      (fun k => - coordinateAxisPoint (K := K) (0 : Fin 4) k) := by
  calc
    polynomialSectionSpecialPoint (D.sectionGaugeRightSection i hi) =
        polynomialSectionSpecialPoint D.rightSection := by
      unfold sectionGaugeRightSection
      exact polynomialSectionSpecialPoint_elementaryUnshear_of_constantCoeff_zero
        i (D.sectionGaugeCoefficient i hi) D.rightSection
        (D.sectionGaugeCoefficient_constantCoeff_zero i hi hpos)
    _ = (fun k => - coordinateAxisPoint (K := K) (0 : Fin 4) k) :=
      D.rightSpecialPoint

/-- The determinant clock is exactly preserved by the pointed gauge. -/
theorem sectionGaugeFamily_hessianDefect
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hi0 : i ≠ (0 : Fin 4)) :
    HasPolynomialFamilyHessianDefect (K := K)
      (D.sectionGaugeFamily i hi) B.aligned.endpoint.defect := by
  unfold sectionGaugeFamily
  exact elementaryShearHom_preservesHessianDefect
    i hi0 (D.sectionGaugeCoefficient i hi) D.family D.hessianDefect

/-- The exact zero-left moving collision is exactly preserved. -/
theorem sectionGaugeFamily_exactCollision
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    (hi0 : i ≠ (0 : Fin 4)) :
    HasPolynomialFamilyExactGradientCollision
      (D.sectionGaugeFamily i hi)
      (zeroPolynomialSection (K := K))
      (D.sectionGaugeRightSection i hi) := by
  have h :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K) i hi0 (D.sectionGaugeCoefficient i hi)
      D.family (zeroPolynomialSection (K := K)) D.rightSection D.exactCollision
  simpa [sectionGaugeFamily, sectionGaugeRightSection] using h

/-- Every existing nonlinear source-degree cap survives the gauge step. -/
theorem sectionGaugeFamily_degreeBound
    (D : DirectClosingAlignedSquareSourceData C)
    (i : Fin 4)
    (hi : D.rightSection i ≠ 0)
    {m : ℕ}
    (hbound : NonlinearDegreeBound m D.family) :
    NonlinearDegreeBound m (D.sectionGaugeFamily i hi) := by
  unfold sectionGaugeFamily
  exact nonlinearDegreeBound_elementaryShear
    m i (D.sectionGaugeCoefficient i hi) D.family hbound

end DirectClosingAlignedSquareSourceData

/-! ## Package the positive-section cases of the equality spill -/

/-- Source-honest data for one positive section-wall gauge step below the
old first actual source layer.  The step is an exact source equivalence; no
claim is made here about the first actual layer of the transformed family. -/
structure DirectClosingPositiveSectionGaugeStep
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  source : DirectClosingAlignedSquareSourceData C
  index : Fin 4
  section_ne : source.rightSection index ≠ 0
  index_ne_zero : index ≠ (0 : Fin 4)
  order_pos : 0 < source.sectionGaugeOrder index section_ne
  order_lt_firstActual :
    source.sectionGaugeOrder index section_ne < C.firstActualLayerOrder

namespace DirectClosingPositiveSectionGaugeStep

/-- The corrected coordinate is either killed completely or its exact order
strictly increases. -/
theorem killed_or_order_strict
    (G : DirectClosingPositiveSectionGaugeStep C) :
    G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0 ∨
      ∃ hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0,
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew := by
  by_cases hzero :
      G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0
  · exact Or.inl hzero
  · exact Or.inr ⟨hzero,
      G.source.sectionGaugeRightSection_order_strict
        G.index G.section_ne hzero⟩

end DirectClosingPositiveSectionGaugeStep

/-- After the sharp equality-wall normal form, the only positive-clock
section cases carry honest pointed gauge steps.  Family-side residue remains
at clock zero and is deliberately kept separate for the next special-fibre
classifier.  A gauge step is source-equivalent geometry, not yet a claim that
the transformed literal source clock is unchanged. -/
inductive DirectClosingCanonicalSquareEqualityGaugeFrontier
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
      (horder0 :
        smithFamilyCoefficientParameterOrder A.toAlignedSquareSource.family d hd = 0)
  | sectionGauge
      (G : DirectClosingPositiveSectionGaugeStep C)

/-- Every equality spill is therefore either a zero-clock family wall or a
positive pointed gauge step. -/
theorem DirectClosingCanonicalSquareEarlierWallNormalForm.toGaugeFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (N : DirectClosingCanonicalSquareEarlierWallNormalForm C heq) :
    DirectClosingCanonicalSquareEqualityGaugeFrontier C heq := by
  cases N with
  | longitudinalFamily fresh d hd hlt horder0 =>
      exact .longitudinalFamily fresh d hd hlt horder0
  | longitudinalSection fresh i hi _hlt hi0 hpos hclock =>
      exact .sectionGauge {
        source := C.directClosingLongitudinalSquareSource fresh
        index := i
        section_ne := hi
        index_ne_zero := hi0
        order_pos := by simpa [DirectClosingAlignedSquareSourceData.sectionGaugeOrder] using hpos
        order_lt_firstActual := by
          simpa [DirectClosingAlignedSquareSourceData.sectionGaugeOrder] using hclock
      }
  | transverseFamily A d hd hlt _hclock horder0 =>
      exact .transverseFamily A d hd hlt horder0
  | transverseSection A i hi _hlt hi0 hpos hclock =>
      exact .sectionGauge {
        source := A.toAlignedSquareSource
        index := i
        section_ne := hi
        index_ne_zero := hi0
        order_pos := by simpa [DirectClosingAlignedSquareSourceData.sectionGaugeOrder] using hpos
        order_lt_firstActual := by
          simpa [DirectClosingAlignedSquareSourceData.sectionGaugeOrder] using hclock
      }

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
