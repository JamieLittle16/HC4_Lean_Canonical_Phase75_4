import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.CanonicalSmithReesSpecialFiber
import HC4.Newton.MixedDepartureAdapter
import HC4.Newton.FirstSchurLayerLinearization
import HC4.Newton.RankOneSchurSeriesAlignment
import Mathlib.Tactic

/-!
# First Schur departure bridge

This module isolates the last determinant-coefficient calculation from the
already-green preterminal repair algebra.

For a departure-ready family with

    det Hess(P) = X^Delta,

every exact parameter layer of the Hessian determinant below `Delta` is
zero.  Therefore, once the geometric Schur calculation identifies the
first transverse determinant layer with

    b * (P_j)_{VV},

that source vanishes automatically and the existing mixed-departure adapter
immediately gives strict rank promotion or the affine/separated channel.

The definition `IsPreterminalSchurLayerModel` deliberately records only the
single geometric identity still to be established from the Smith packet.
Everything after that identity is proved here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Below the exact determinant-closing exponent, the corresponding actual
parameter layer of the Hessian determinant is zero. -/
theorem hessianDefect_parameterLayer_eq_zero_of_lt
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta j : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hj : j < Delta) :
    familyParameterLayer
        (HC4.Polynomial.hessianDeterminant P) j = 0 := by
  ext d
  rw [familyParameterLayer_coeff]
  rw [hdef]
  have hne : j ≠ Delta := Nat.ne_of_lt hj
  by_cases hd : d = 0
  · subst d
    rw [MvPolynomial.coeff_C]
    simp only [if_pos]
    rw [Polynomial.coeff_X_pow]
    simp [hne]
  · rw [MvPolynomial.coeff_C]
    simp [Ne.symm hd]

/-- The exact local identity expected at a first preterminal Schur
departure.  The left side is the *actual* `j`th determinant layer; the right
side is the already formalised rank-one Schur linear source of the actual
coefficient potential `P_j`.

Keeping this as a named predicate prevents the final exhaustion proof from
silently assuming the crucial layer-identification calculation. -/
def IsPreterminalSchurLayerModel
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity)
    (j : ℕ)
    (b : K)
    (V : Fin 4) : Prop :=
  familyParameterLayer
      (HC4.Polynomial.hessianDeterminant f.lossless.family) j =
    preterminalSchurLinearSource
      b V (familyParameterLayer f.lossless.family j)

/-- Once the first Schur layer has been identified with the local rank-one
model, exact Hessian defect forces its linear source to vanish below
closure. -/
theorem preterminalSchurLayer_source_zero
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity)
    {j : ℕ}
    {b : K}
    {V : Fin 4}
    (hj : j < f.defect)
    (hmodel :
      IsPreterminalSchurLayerModel f j b V) :
    preterminalSchurLinearSource
        b V (familyParameterLayer f.lossless.family j) = 0 := by
  rw [IsPreterminalSchurLayerModel] at hmodel
  rw [← hmodel]
  exact
    hessianDefect_parameterLayer_eq_zero_of_lt
      f.lossless.family f.hessianDefect hj

/-- Full handoff from the first-layer geometric identity to the existing
canonical repair-state API.  No determinant bookkeeping remains after
`hmodel`. -/
theorem preterminalSchurLayer_canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity)
    {j : ℕ}
    {b : K}
    (hb : b ≠ 0)
    (U V : Fin 4)
    (hj : j < f.defect)
    (hmodel :
      IsPreterminalSchurLayerModel f j b V) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet U V
          (familyParameterLayer f.lossless.family j) =
        -(directionalMixedDerivative U V
          (familyParameterLayer f.lossless.family j))^2 ∧
      binaryDirectionalHessianDet U V
          (familyParameterLayer f.lossless.family j) ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V
        (familyParameterLayer f.lossless.family j) := by
  apply
    preterminal_departure_canonicalStrictRepair_with_source_or_affineSeparated
      b hb U V
      (familyParameterLayer f.lossless.family j)
      complexity
  exact preterminalSchurLayer_source_zero f hj hmodel

/-- Specialisation to the exact first positive actual family layer. -/
theorem firstActualLayer_canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity)
    (h : HasPositiveActualParameterLayer f.lossless.family)
    {b : K}
    (hb : b ≠ 0)
    (U V : Fin 4)
    (hpre :
      firstPositiveActualParameterOrder f.lossless.family h <
        f.defect)
    (hmodel :
      IsPreterminalSchurLayerModel
        f
        (firstPositiveActualParameterOrder f.lossless.family h)
        b V) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet U V
          (familyParameterLayer f.lossless.family
            (firstPositiveActualParameterOrder f.lossless.family h)) =
        -(directionalMixedDerivative U V
          (familyParameterLayer f.lossless.family
            (firstPositiveActualParameterOrder f.lossless.family h)))^2 ∧
      binaryDirectionalHessianDet U V
          (familyParameterLayer f.lossless.family
            (firstPositiveActualParameterOrder f.lossless.family h)) ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V
        (familyParameterLayer f.lossless.family
          (firstPositiveActualParameterOrder f.lossless.family h)) := by
  exact
    preterminalSchurLayer_canonicalStrictRepair_or_affineSeparated
      f hb U V hpre hmodel


/-! -----------------------------------------------------------------------
  Geometric certificate -> proved Schur model
------------------------------------------------------------------------ -/

/-- Concrete data sufficient to prove the formerly abstract
`IsPreterminalSchurLayerModel` identity.

The only frontier-specific field is `determinantLayer`: it says that the
chosen binary Schur determinant really computes the relevant layer of the
full Hessian determinant.  The delicate first-order cancellation inside the
Schur determinant is no longer assumed; it is supplied unconditionally by
`PreterminalSchurDepartureData.determinant_coeff_order_eq_linearSource`. -/
structure FrontierPreterminalSchurCertificate
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  schur : PreterminalSchurDepartureData (Fin 4) K
  order_lt_defect : schur.order < f.defect
  potential_eq_layer :
    schur.potential =
      familyParameterLayer f.lossless.family schur.order
  determinantLayer :
    familyParameterLayer
        (HC4.Polynomial.hessianDeterminant f.lossless.family)
        schur.order =
      schur.determinant.coeff schur.order

namespace FrontierPreterminalSchurCertificate

/-- A concrete first-Schur certificate proves the exact local model identity
that was previously an external hypothesis. -/
theorem isPreterminalSchurLayerModel
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (c : FrontierPreterminalSchurCertificate f) :
    IsPreterminalSchurLayerModel
      f c.schur.order c.schur.leadingScalar c.schur.V := by
  unfold IsPreterminalSchurLayerModel
  calc
    familyParameterLayer
        (HC4.Polynomial.hessianDeterminant f.lossless.family)
        c.schur.order =
      c.schur.determinant.coeff c.schur.order :=
        c.determinantLayer
    _ =
      preterminalSchurLinearSource
        c.schur.leadingScalar c.schur.V c.schur.potential :=
        c.schur.determinant_coeff_order_eq_linearSource
    _ =
      preterminalSchurLinearSource
        c.schur.leadingScalar c.schur.V
        (familyParameterLayer f.lossless.family c.schur.order) := by
        rw [c.potential_eq_layer]

/-- **Concrete preterminal handoff.**

Once the geometric Smith analysis constructs a first-Schur certificate, the
whole preterminal branch is already closed: exact determinant defect kills
the linear source and the existing mixed-departure theorem gives strict rank
promotion or the affine/separated channel. -/
theorem canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (c : FrontierPreterminalSchurCertificate f) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order) =
        -(directionalMixedDerivative c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order))^2 ∧
      binaryDirectionalHessianDet c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order) ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel c.schur.U c.schur.V
        (familyParameterLayer f.lossless.family c.schur.order) := by
  exact
    preterminalSchurLayer_canonicalStrictRepair_or_affineSeparated
      f
      c.schur.leadingScalar_ne_zero
      c.schur.U c.schur.V
      c.order_lt_defect
      c.isPreterminalSchurLayerModel

end FrontierPreterminalSchurCertificate

/-! -----------------------------------------------------------------------
  Denominator-cleared frontier certificate
------------------------------------------------------------------------ -/

/-- A preterminal Schur certificate in the form actually supplied by a
cleared Schur complement.

Instead of asking the Schur determinant layer to *equal* the full Hessian
determinant layer, we retain a full determinant parameter series and the
exact cleared identity

    det(Schur) = factor * fullDet.

This is the natural polynomial identity produced by denominator-cleared
Schur complements.  Since the Hessian defect makes every coefficient of
`fullDet` below closure vanish, multiplication by an arbitrary factor cannot
create a preterminal coefficient. -/
structure FrontierClearedPreterminalSchurCertificate
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  schur : PreterminalSchurDepartureData (Fin 4) K
  fullDetSeries : Polynomial (MvPolynomial (Fin 4) K)
  clearedFactor : Polynomial (MvPolynomial (Fin 4) K)
  order_lt_defect : schur.order < f.defect
  potential_eq_layer :
    schur.potential =
      familyParameterLayer f.lossless.family schur.order
  fullDet_coeff :
    ∀ n : ℕ,
      fullDetSeries.coeff n =
        familyParameterLayer
          (HC4.Polynomial.hessianDeterminant f.lossless.family) n
  schurFactor :
    schur.determinant = clearedFactor * fullDetSeries

namespace FrontierClearedPreterminalSchurCertificate

/-- Every full determinant coefficient up through the preterminal Schur
order vanishes. -/
theorem fullDet_zero_through_order
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (c : FrontierClearedPreterminalSchurCertificate f) :
    ∀ n : ℕ, n ≤ c.schur.order → c.fullDetSeries.coeff n = 0 := by
  intro n hn
  rw [c.fullDet_coeff n]
  exact
    hessianDefect_parameterLayer_eq_zero_of_lt
      f.lossless.family f.hessianDefect
      (lt_of_le_of_lt hn c.order_lt_defect)

/-- **Cleared first-Schur source vanishing.**
The true denominator-cleared Schur identity is enough to force the same
preterminal linear source to vanish; the old layer-equality hypothesis is
unnecessary. -/
theorem source_zero
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (c : FrontierClearedPreterminalSchurCertificate f) :
    preterminalSchurLinearSource
      c.schur.leadingScalar c.schur.V
      (familyParameterLayer f.lossless.family c.schur.order) = 0 := by
  rw [← c.potential_eq_layer]
  exact
    c.schur.linearSource_eq_zero_of_clearedFactor
      c.clearedFactor c.fullDetSeries
      c.schurFactor c.fullDet_zero_through_order

/-- **Denominator-cleared preterminal handoff.**
Once the Smith geometry supplies the genuine cleared Schur series, the
preterminal branch closes immediately through the already-green mixed
departure adapter. -/
theorem canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (c : FrontierClearedPreterminalSchurCertificate f) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order) =
        -(directionalMixedDerivative c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order))^2 ∧
      binaryDirectionalHessianDet c.schur.U c.schur.V
          (familyParameterLayer f.lossless.family c.schur.order) ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel c.schur.U c.schur.V
        (familyParameterLayer f.lossless.family c.schur.order) := by
  apply
    preterminal_departure_canonicalStrictRepair_with_source_or_affineSeparated
      c.schur.leadingScalar
      c.schur.leadingScalar_ne_zero
      c.schur.U c.schur.V
      (familyParameterLayer f.lossless.family c.schur.order)
      complexity
  exact c.source_zero

end FrontierClearedPreterminalSchurCertificate

/-! -----------------------------------------------------------------------
  Automatic first-transverse extraction from a cleared Schur series
------------------------------------------------------------------------ -/

/-- The remaining geometric data in its most economical form.

The Smith/frontier analysis supplies one polynomial binary Schur series with
a rank-one constant term, the denominator-cleared determinant identity, and
the compatibility of the kernel entry with the actual coefficient
potentials.  Finiteness then chooses the first transverse order
automatically. -/
structure FrontierClearedRankOneSchurSeries
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  series : RankOneSchurSeries (MvPolynomial (Fin 4) K)
  leadingScalar : K
  leadingScalar_ne_zero : leadingScalar ≠ 0
  U : Fin 4
  V : Fin 4
  leading_eq : series.leading = MvPolynomial.C leadingScalar
  hasTransverse : series.HasPositiveTransverseLayer
  fullDetSeries : Polynomial (MvPolynomial (Fin 4) K)
  clearedFactor : Polynomial (MvPolynomial (Fin 4) K)
  kernel_coeff :
    ∀ n : ℕ,
      series.kernel.coeff n =
        directionalSecondDerivative V
          (familyParameterLayer f.lossless.family n)
  fullDet_coeff :
    ∀ n : ℕ,
      fullDetSeries.coeff n =
        familyParameterLayer
          (HC4.Polynomial.hessianDeterminant f.lossless.family) n
  schurFactor :
    series.determinant = clearedFactor * fullDetSeries

namespace FrontierClearedRankOneSchurSeries

/-- Canonical first transverse order of the retained Schur series. -/
noncomputable def firstOrder
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f) : ℕ :=
  S.series.firstPositiveTransverseOrder S.hasTransverse

theorem firstOrder_pos
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f) :
    0 < S.firstOrder := by
  exact S.series.firstPositiveTransverseOrder_pos S.hasTransverse

/-- The actual coefficient potential at the first transverse order. -/
noncomputable def firstPotential
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f) :
    MvPolynomial (Fin 4) K :=
  familyParameterLayer f.lossless.family S.firstOrder

/-- The automatically selected first transverse order gives precisely the
`PreterminalSchurDepartureData` expected by the linearisation theorem. -/
noncomputable def firstSchurData
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f) :
    PreterminalSchurDepartureData (Fin 4) K where
  order := S.firstOrder
  leadingScalar := S.leadingScalar
  U := S.U
  V := S.V
  potential := S.firstPotential
  active := S.series.active
  offDiag := S.series.offDiag
  kernel := S.series.kernel
  order_pos := S.firstOrder_pos
  leadingScalar_ne_zero := S.leadingScalar_ne_zero
  active_coeff_zero := by
    rw [S.series.active_coeff_zero, S.leading_eq]
  offDiag_lower_zero := by
    intro n hn
    exact
      S.series.offDiag_coeff_eq_zero_of_lt_first
        S.hasTransverse hn
  kernel_lower_zero := by
    intro n hn
    exact
      S.series.kernel_coeff_eq_zero_of_lt_first
        S.hasTransverse hn
  kernel_coeff_order := by
    exact S.kernel_coeff S.firstOrder

/-- If the automatically selected first transverse order is preterminal,
all fields of the cleared preterminal certificate are forced. -/
noncomputable def preterminalCertificate
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f)
    (hpre : S.firstOrder < f.defect) :
    FrontierClearedPreterminalSchurCertificate f where
  schur := S.firstSchurData
  fullDetSeries := S.fullDetSeries
  clearedFactor := S.clearedFactor
  order_lt_defect := hpre
  potential_eq_layer := rfl
  fullDet_coeff := S.fullDet_coeff
  schurFactor := by
    simpa [PreterminalSchurDepartureData.determinant,
      RankOneSchurSeries.determinant, firstSchurData] using
      S.schurFactor

/-- **Automatic preterminal exhaustion from the genuine Schur series.**
No manual choice of departure order and no lower-layer bookkeeping remain. -/
theorem preterminal_canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierClearedRankOneSchurSeries f)
    (hpre : S.firstOrder < f.defect) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential =
        -(directionalMixedDerivative S.U S.V S.firstPotential)^2 ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel S.U S.V S.firstPotential := by
  exact
    (S.preterminalCertificate hpre).canonicalStrictRepair_or_affineSeparated

end FrontierClearedRankOneSchurSeries

/-! -----------------------------------------------------------------------
  Exact closing-clock Schur frontier
------------------------------------------------------------------------ -/

/-- A stronger and more economical rank-one Schur frontier.

The exact Hessian defect has already identified the full determinant with
`X^defect`.  Hence the genuinely useful cleared identity is simply

    det(Schur) = clearedFactor * X^defect.

A nonzero constant coefficient of `clearedFactor` is the algebraic
expression of the fact that the already-active block remains invertible at
the special fibre.  From these two facts the first positive transverse
Schur order exists automatically and can occur no later than `defect`.
Thus the local rank-one branch has only the intended alternatives:
preterminal departure or determinant-closing departure. -/
structure FrontierExactRankOneSchurSeries
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  series : RankOneSchurSeries (MvPolynomial (Fin 4) K)
  leadingScalar : K
  leadingScalar_ne_zero : leadingScalar ≠ 0
  U : Fin 4
  V : Fin 4
  leading_eq : series.leading = MvPolynomial.C leadingScalar
  clearedFactor : Polynomial (MvPolynomial (Fin 4) K)
  clearedFactor_coeff_zero_ne_zero :
    clearedFactor.coeff 0 ≠ 0
  kernel_coeff :
    ∀ n : ℕ,
      series.kernel.coeff n =
        directionalSecondDerivative V
          (familyParameterLayer f.lossless.family n)
  schurFactor :
    series.determinant =
      clearedFactor * Polynomial.X ^ f.defect

namespace FrontierExactRankOneSchurSeries

/-- The exact cleared identity forces the existence of a later transverse
Schur layer; no separate existence hypothesis is needed. -/
theorem hasTransverse
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    S.series.HasPositiveTransverseLayer := by
  exact
    S.series.hasPositiveTransverseLayer_of_determinant_eq_factor_mul_X_pow
      S.clearedFactor f.defect S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- Canonical first transverse order of the exact Schur frontier. -/
noncomputable def firstOrder
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) : ℕ :=
  S.series.firstPositiveTransverseOrder S.hasTransverse

/-- The first transverse order is strictly positive. -/
theorem firstOrder_pos
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    0 < S.firstOrder := by
  exact S.series.firstPositiveTransverseOrder_pos S.hasTransverse

/-- **No post-closing first departure.**
The nonzero constant clearing factor forces the first transverse Schur
order to occur at or before the exact Hessian defect. -/
theorem firstOrder_le_defect
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    S.firstOrder ≤ f.defect := by
  exact
    S.series.firstPositiveTransverseOrder_le_of_determinant_eq_factor_mul_X_pow
      S.hasTransverse S.clearedFactor S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- Consequently the first transverse order has the exact two-way split
used by the handwritten proof: preterminal or closing, with no third case. -/
theorem firstOrder_preterminal_or_closing
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    S.firstOrder < f.defect ∨ S.firstOrder = f.defect := by
  exact lt_or_eq_of_le S.firstOrder_le_defect

/-- The actual coefficient potential at the first exact transverse order. -/
noncomputable def firstPotential
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    MvPolynomial (Fin 4) K :=
  familyParameterLayer f.lossless.family S.firstOrder

/-- Package the automatically selected order into the green preterminal
linearisation API. -/
noncomputable def firstSchurData
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    PreterminalSchurDepartureData (Fin 4) K where
  order := S.firstOrder
  leadingScalar := S.leadingScalar
  U := S.U
  V := S.V
  potential := S.firstPotential
  active := S.series.active
  offDiag := S.series.offDiag
  kernel := S.series.kernel
  order_pos := S.firstOrder_pos
  leadingScalar_ne_zero := S.leadingScalar_ne_zero
  active_coeff_zero := by
    rw [S.series.active_coeff_zero, S.leading_eq]
  offDiag_lower_zero := by
    intro n hn
    exact
      S.series.offDiag_coeff_eq_zero_of_lt_first
        S.hasTransverse hn
  kernel_lower_zero := by
    intro n hn
    exact
      S.series.kernel_coeff_eq_zero_of_lt_first
        S.hasTransverse hn
  kernel_coeff_order := by
    exact S.kernel_coeff S.firstOrder

/-- Below determinant closure, the exact factorisation itself kills the
first Schur determinant coefficient. -/
theorem determinant_coeff_firstOrder_eq_zero_of_preterminal
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f)
    (hpre : S.firstOrder < f.defect) :
    S.series.determinant.coeff S.firstOrder = 0 := by
  rw [S.schurFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_lt hpre]

/-- **Exact preterminal source vanishing.**
The full first-departure identity is now automatic from the exact cleared
Schur frontier. -/
theorem preterminal_source_zero
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f)
    (hpre : S.firstOrder < f.defect) :
    preterminalSchurLinearSource
      S.leadingScalar S.V S.firstPotential = 0 := by
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        preterminalSchurLinearSource
          S.leadingScalar S.V S.firstPotential := by
    simpa [PreterminalSchurDepartureData.determinant,
      RankOneSchurSeries.determinant, firstSchurData, firstPotential] using
      (S.firstSchurData).determinant_coeff_order_eq_linearSource
  calc
    preterminalSchurLinearSource
        S.leadingScalar S.V S.firstPotential =
      S.series.determinant.coeff S.firstOrder := hlin.symm
    _ = 0 :=
      S.determinant_coeff_firstOrder_eq_zero_of_preterminal hpre

/-- The complete preterminal branch therefore dispatches immediately to the
already-green strict-repair/affine-separated dichotomy. -/
theorem preterminal_canonicalStrictRepair_or_affineSeparated
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f)
    (hpre : S.firstOrder < f.defect) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential =
        -(directionalMixedDerivative S.U S.V S.firstPotential)^2 ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel S.U S.V S.firstPotential := by
  apply
    preterminal_departure_canonicalStrictRepair_with_source_or_affineSeparated
      S.leadingScalar S.leadingScalar_ne_zero
      S.U S.V S.firstPotential complexity
  exact S.preterminal_source_zero hpre

/-- At determinant closure the selected coefficient is genuinely
transverse, giving concrete nonzero data to the terminal adapter. -/
theorem closing_transverse_nonzero
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f)
    (hclose : S.firstOrder = f.defect) :
    S.series.offDiag.coeff f.defect ≠ 0 ∨
      S.series.kernel.coeff f.defect ≠ 0 := by
  have h :
      S.series.offDiag.coeff S.firstOrder ≠ 0 ∨
        S.series.kernel.coeff S.firstOrder ≠ 0 := by
    simpa [firstOrder] using
      S.series.transverse_nonzero_at_first S.hasTransverse
  simpa [hclose] using h

/-- **Rank-one frontier exhaustion up to the terminal closing adapter.**
Once the genuine exact cleared Schur series has been constructed, there are
only two outcomes: the whole preterminal branch is discharged, or a
nonzero transverse coefficient occurs exactly at determinant closure. -/
theorem preterminalRepair_or_closing
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurSeries f) :
    ((RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential =
        -(directionalMixedDerivative S.U S.V S.firstPotential)^2 ∧
      binaryDirectionalHessianDet S.U S.V S.firstPotential ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel S.U S.V S.firstPotential) ∨
    (S.firstOrder = f.defect ∧
      (S.series.offDiag.coeff f.defect ≠ 0 ∨
       S.series.kernel.coeff f.defect ≠ 0)) := by
  rcases S.firstOrder_preterminal_or_closing with hpre | hclose
  · left
    exact S.preterminal_canonicalStrictRepair_or_affineSeparated hpre
  · right
    exact ⟨hclose, S.closing_transverse_nonzero hclose⟩

end FrontierExactRankOneSchurSeries


/-! -----------------------------------------------------------------------
  Matrix-level exact Schur clock

The potential-valued frontier above is convenient when one wants the exact
mixed-Hessian source.  For global exhaustion, however, the first transverse
Schur *matrix* already carries enough information to force rank promotion.
At the first positive transverse order `j < defect`, the linearisation gives

    coeff_j(det S) = leading * kernel_j.

The exact determinant clock kills the left side, so `kernel_j = 0`.  Since
`j` was selected as the first order where `offDiag_j` or `kernel_j` is
nonzero, necessarily `offDiag_j != 0`.  Thus the preterminal branch is a
genuine rank promotion before any partial-Legendre potential is reconstructed.

This is strictly weaker data than `FrontierExactRankOneSchurSeries` and is
therefore the preferred target of the actual four-block Smith construction.
------------------------------------------------------------------------ -/

/-- Exact denominator-cleared rank-one Schur clock with no potential-level
integrability hypothesis. -/
structure FrontierExactRankOneSchurClock
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  series : RankOneSchurSeries (MvPolynomial (Fin 4) K)
  leading_ne_zero : series.leading ≠ 0
  clearedFactor : Polynomial (MvPolynomial (Fin 4) K)
  clearedFactor_coeff_zero_ne_zero :
    clearedFactor.coeff 0 ≠ 0
  schurFactor :
    series.determinant =
      clearedFactor * Polynomial.X ^ f.defect

namespace FrontierExactRankOneSchurClock

/-- The exact determinant clock forces a genuine positive transverse layer. -/
theorem hasTransverse
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) :
    S.series.HasPositiveTransverseLayer := by
  exact
    S.series.hasPositiveTransverseLayer_of_determinant_eq_factor_mul_X_pow
      S.clearedFactor f.defect S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- First positive transverse Schur order. -/
noncomputable def firstOrder
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) : ℕ :=
  S.series.firstPositiveTransverseOrder S.hasTransverse

/-- The first transverse order is positive. -/
theorem firstOrder_pos
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) :
    0 < S.firstOrder := by
  exact S.series.firstPositiveTransverseOrder_pos S.hasTransverse

/-- The first transverse order occurs no later than determinant closure. -/
theorem firstOrder_le_defect
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) :
    S.firstOrder ≤ f.defect := by
  exact
    S.series.firstPositiveTransverseOrder_le_of_determinant_eq_factor_mul_X_pow
      S.hasTransverse S.clearedFactor S.schurFactor
      S.clearedFactor_coeff_zero_ne_zero

/-- Package the selected order into the purely matrix-valued first-departure
linearisation theorem. -/
noncomputable def firstDeparture
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) :
    FirstRankOneSchurDeparture (MvPolynomial (Fin 4) K) where
  order := S.firstOrder
  leading := S.series.leading
  active := S.series.active
  offDiag := S.series.offDiag
  kernel := S.series.kernel
  order_pos := S.firstOrder_pos
  active_coeff_zero := S.series.active_coeff_zero
  offDiag_lower_zero := by
    intro n hn
    exact S.series.offDiag_coeff_eq_zero_of_lt_first S.hasTransverse hn
  kernel_lower_zero := by
    intro n hn
    exact S.series.kernel_coeff_eq_zero_of_lt_first S.hasTransverse hn

/-- Below determinant closure the exact factorisation kills the selected
Schur determinant coefficient. -/
theorem determinant_coeff_firstOrder_eq_zero_of_preterminal
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f)
    (hpre : S.firstOrder < f.defect) :
    S.series.determinant.coeff S.firstOrder = 0 := by
  rw [S.schurFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_lt hpre]

/-- At a preterminal first transverse order the kernel entry itself must
vanish.  This uses only the matrix linearisation and the nonzero leading
rank-one coefficient. -/
theorem kernel_coeff_firstOrder_eq_zero_of_preterminal
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f)
    (hpre : S.firstOrder < f.defect) :
    S.series.kernel.coeff S.firstOrder = 0 := by
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, firstDeparture] using
      S.firstDeparture.coeff_order_determinant
  have hprod :
      S.series.leading * S.series.kernel.coeff S.firstOrder = 0 := by
    rw [← hlin]
    exact S.determinant_coeff_firstOrder_eq_zero_of_preterminal hpre
  exact (mul_eq_zero.mp hprod).resolve_left S.leading_ne_zero

/-- **Direct preterminal mixed pivot.**
Because the selected order is genuinely transverse and its kernel entry has
just been forced to zero, its off-diagonal entry is necessarily nonzero. -/
theorem offDiag_coeff_firstOrder_ne_zero_of_preterminal
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f)
    (hpre : S.firstOrder < f.defect) :
    S.series.offDiag.coeff S.firstOrder ≠ 0 := by
  rcases S.series.transverse_nonzero_at_first S.hasTransverse with hB | hC
  · exact hB
  · exact False.elim (hC (S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre))

/-- The matrix-level preterminal departure is already a strict rank-one to
rank-two repair step in the existing well-founded repair relation. -/
theorem preterminal_rankTwoProgress
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f)
    (hpre : S.firstOrder < f.defect) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity) ∧
    S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure := by
  have hprogress := rankOne_to_rankTwo_repairProgress complexity
  exact
    ⟨hprogress,
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre,
      repairState_measure_lt_of_progress hprogress⟩

/-- The exact clock has only the two intended outcomes: direct preterminal
rank promotion, or a genuinely transverse coefficient exactly at determinant
closure. -/
theorem rankTwoProgress_or_closing
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (S : FrontierExactRankOneSchurClock f) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
    (S.firstOrder = f.defect ∧
      (S.series.offDiag.coeff f.defect ≠ 0 ∨
       S.series.kernel.coeff f.defect ≠ 0)) := by
  rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
  · exact Or.inl (S.preterminal_rankTwoProgress hpre)
  · right
    refine ⟨hclose, ?_⟩
    have h := S.series.transverse_nonzero_at_first S.hasTransverse
    have hfirst :
        S.series.firstPositiveTransverseOrder S.hasTransverse = f.defect := by
      simpa only [firstOrder] using hclose
    rw [hfirst] at h
    exact h

end FrontierExactRankOneSchurClock

/-! -----------------------------------------------------------------------
  General four-block constructor for the matrix-level clock
------------------------------------------------------------------------ -/

/-- Exact four-block data at a rigid Smith frontier.

This is now a thin, concrete extraction target: supply the actual symmetric
`2+2` Hessian parameter series, prove its full determinant is the exact
closing monomial, prove the active minor remains a unit at the special
fibre, and identify the constant cleared binary Schur block as rank one.
Everything from that point onward is automatic. -/
structure FrontierExactFourBlockSchurData
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) where
  block : GeneralFourBlock
    (Polynomial (MvPolynomial (Fin 4) K))
  fullDet : block.determinantCore = Polynomial.X ^ f.defect
  activeDet_coeff_zero_ne_zero : block.activeDet.coeff 0 ≠ 0
  rigid :
    block.polynomialSchurSeries.LeftPivot ∨
      block.polynomialSchurSeries.RightAxisPivot

namespace FrontierExactFourBlockSchurData

/-- Left-pivot four-block data produces the exact matrix Schur clock. -/
noncomputable def toClockLeft
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (B : FrontierExactFourBlockSchurData f)
    (hleft : B.block.polynomialSchurSeries.LeftPivot) :
    FrontierExactRankOneSchurClock f where
  series := B.block.polynomialSchurSeries.alignLeft hleft
  leading_ne_zero :=
    B.block.polynomialSchurSeries.alignLeft_leading_ne_zero hleft
  clearedFactor :=
    (Polynomial.C (B.block.polynomialSchurSeries.active.coeff 0))^2 *
      B.block.activeDet
  clearedFactor_coeff_zero_ne_zero := by
    have ha :
        B.block.polynomialSchurSeries.active.coeff 0 ≠ 0 := hleft.1
    have hprod :
        (B.block.polynomialSchurSeries.active.coeff 0) ^ 2 *
            B.block.activeDet.coeff 0 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 ha) B.activeDet_coeff_zero_ne_zero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hprod
  schurFactor := by
    calc
      (B.block.polynomialSchurSeries.alignLeft hleft).determinant =
          (Polynomial.C (B.block.polynomialSchurSeries.active.coeff 0))^2 *
            B.block.polynomialSchurSeries.determinant :=
        B.block.polynomialSchurSeries.alignLeft_determinant hleft
      _ =
          (Polynomial.C (B.block.polynomialSchurSeries.active.coeff 0))^2 *
            (B.block.activeDet * B.block.determinantCore) := by
        rw [B.block.polynomialSchurSeries_determinant]
      _ =
          ((Polynomial.C (B.block.polynomialSchurSeries.active.coeff 0))^2 *
            B.block.activeDet) * Polynomial.X ^ f.defect := by
        rw [B.fullDet]
        ring

/-- Right-axis four-block data produces the exact matrix Schur clock. -/
noncomputable def toClockRight
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (B : FrontierExactFourBlockSchurData f)
    (hright : B.block.polynomialSchurSeries.RightAxisPivot) :
    FrontierExactRankOneSchurClock f where
  series := B.block.polynomialSchurSeries.alignRight hright
  leading_ne_zero :=
    B.block.polynomialSchurSeries.alignRight_leading_ne_zero hright
  clearedFactor := B.block.activeDet
  clearedFactor_coeff_zero_ne_zero := B.activeDet_coeff_zero_ne_zero
  schurFactor := by
    calc
      (B.block.polynomialSchurSeries.alignRight hright).determinant =
          B.block.polynomialSchurSeries.determinant :=
        B.block.polynomialSchurSeries.alignRight_determinant hright
      _ = B.block.activeDet * B.block.determinantCore :=
        B.block.polynomialSchurSeries_determinant
      _ = B.block.activeDet * Polynomial.X ^ f.defect := by
        rw [B.fullDet]

/-- Every rigid general four-block frontier therefore has the exact two-way
local outcome: strict rank promotion before closure, or transverse closing
data exactly at the determinant clock. -/
theorem rankTwoProgress_or_closing
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier
      (K := K) D complexity}
    (B : FrontierExactFourBlockSchurData f) :
    (∃ S : FrontierExactRankOneSchurClock f,
      (RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity) ∧
        S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure) ∨
      (S.firstOrder = f.defect ∧
        (S.series.offDiag.coeff f.defect ≠ 0 ∨
         S.series.kernel.coeff f.defect ≠ 0))) := by
  rcases B.rigid with hleft | hright
  · refine ⟨B.toClockLeft hleft, ?_⟩
    exact (B.toClockLeft hleft).rankTwoProgress_or_closing
  · refine ⟨B.toClockRight hright, ?_⟩
    exact (B.toClockRight hright).rankTwoProgress_or_closing

end FrontierExactFourBlockSchurData

end

end HC4.Valuation
