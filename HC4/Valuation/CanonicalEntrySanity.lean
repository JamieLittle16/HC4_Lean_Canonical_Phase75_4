import HC4.Valuation.FinalRestartAssembly
import HC4.Valuation.DefectRetainingDepartureFrontier
import HC4.Valuation.QuadraticFamilyCollision
import Mathlib.Tactic

/-!
# Sanity audit for the current canonical exact-collision entry

The current canonical restart API places ordinary source homogeneity on the
*entire* polynomial-parameter potential while simultaneously requiring its
Hessian determinant to be the nonzero source-constant `X^Delta`.

For degree at least three these two requirements are incompatible: every
second source derivative has positive source degree, so the source-constant
Hessian matrix is zero, whereas the pure Hessian-defect equation forces its
determinant to be `X^Delta != 0`.

Degree two is already excluded by the exact-collision theorem in
`QuadraticFamilyCollision`: a nondegenerate quadratic gradient is injective,
so the canonical sections `0` and `e_0` cannot collide.

The theorems below deliberately record this as a machine-checkable sanity
barrier.  In particular, the *current* `CanonicalExactCollisionEntry` is empty
for every degree `D >= 2`.  Consequently any proposition-level reduction that
assumes construction of such an entry is vacuous and must not be presented as
a concrete HC4 implication until the entry is weakened to the intended
"fixed quadratic base + higher-degree/nonlinear part" formulation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Positive-degree second derivatives have zero source constant term
------------------------------------------------------------------------ -/

/-- If the whole source polynomial is homogeneous of degree at least three,
then its source-constant Hessian matrix vanishes. -/
theorem homogeneous_ge_three_quadraticFamilyHessianMatrix_eq_zero
    {D : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hhom : P.IsHomogeneous D)
    (hD : 3 ≤ D) :
    quadraticFamilyHessianMatrix P = 0 := by
  funext i j
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) = 0
  have hfirst :
      (MvPolynomial.pderiv i P).IsHomogeneous (D - 1) := by
    exact hhom.pderiv
  have hsecondRaw :
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)).IsHomogeneous
        ((D - 1) - 1) := by
    exact hfirst.pderiv
  have hsecond :
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)).IsHomogeneous
        (D - 2) := by
    convert hsecondRaw using 1 <;> omega
  have hpositive : 0 < D - 2 := by
    omega
  have hdegree :
      Finsupp.degree (0 : Fin 4 →₀ ℕ) ≠ D - 2 := by
    simpa using (ne_of_lt hpositive)
  have hcoeff :
      MvPolynomial.coeff 0
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) = 0 :=
    hsecond.coeff_eq_zero hdegree
  calc
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) =
        MvPolynomial.coeff 0
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) := by
      exact
        congrArg
          (fun g : MvPolynomial (Fin 4) (Polynomial K) → Polynomial K =>
            g (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)))
          MvPolynomial.constantCoeff_eq
    _ = 0 := hcoeff

/-- A genuinely source-homogeneous family of degree at least three cannot
have pure nonzero Hessian clock `X^Delta`. -/
theorem homogeneous_ge_three_polynomialFamilyHessianDefect_impossible
    {D Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hhom : P.IsHomogeneous D)
    (hD : 3 ≤ D)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    False := by
  have hmatrix : quadraticFamilyHessianMatrix P = 0 :=
    homogeneous_ge_three_quadraticFamilyHessianMatrix_eq_zero
      (K := K) hhom hD
  have hdet0 : (quadraticFamilyHessianMatrix P).det = 0 := by
    rw [hmatrix]
    simp
  have hdetEq :
      (quadraticFamilyHessianMatrix P).det = Polynomial.X ^ Delta := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [hdef]
    simp
  have hxzero : (Polynomial.X ^ Delta : Polynomial K) = 0 :=
    hdetEq.symm.trans hdet0
  exact (pow_ne_zero _ Polynomial.X_ne_zero) hxzero

/-! -----------------------------------------------------------------------
  The current full-state entry is empty in every relevant degree
------------------------------------------------------------------------ -/

/-- The current `CanonicalExactCollisionEntry` cannot exist for `D >= 2`.

* `D = 2`: exact quadratic collision forces the two sections equal, contrary
  to their special points `0` and `e_0`;
* `D >= 3`: full source homogeneity contradicts the nonzero pure Hessian
  clock before collision geometry is even used. -/
theorem CanonicalExactCollisionEntry.impossible_of_two_le_degree
    [CharZero K]
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (hD : 2 ≤ D) :
    False := by
  by_cases h2 : D = 2
  · subst D
    have hsections :
        zeroPolynomialSection (K := K) = e.movingSection :=
      quadraticPolynomialFamily_exactCollision_sections_eq
        e.family
        e.homogeneous
        (zeroPolynomialSection (K := K))
        e.movingSection
        e.hessianDefect
        e.exactCollision
    have hspecial :=
      congrArg polynomialSectionSpecialPoint hsections
    rw [polynomialSectionSpecialPoint_zeroPolynomialSection,
      e.sectionSpecial] at hspecial
    exact
      coordinateAxisPoint_zero_ne_zeroPoint (K := K) hspecial.symm
  · have h3 : 3 ≤ D := by
      omega
    exact
      homogeneous_ge_three_polynomialFamilyHessianDefect_impossible
        (K := K)
        e.homogeneous
        h3
        e.hessianDefect

/-- The same sanity contradiction is inherited by every current full
geometric restart state. -/
theorem CanonicalGeometricRestartState.impossible_of_two_le_degree
    [CharZero K]
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D)
    (hD : 2 ≤ D) :
    False := by
  by_cases h2 : D = 2
  · subst D
    have hsections :
        zeroPolynomialSection (K := K) = s.movingSection :=
      quadraticPolynomialFamily_exactCollision_sections_eq
        s.family
        s.homogeneous
        (zeroPolynomialSection (K := K))
        s.movingSection
        s.hessianDefect
        s.exactCollision
    have hspecial :=
      congrArg polynomialSectionSpecialPoint hsections
    rw [polynomialSectionSpecialPoint_zeroPolynomialSection,
      s.sectionSpecial] at hspecial
    exact
      coordinateAxisPoint_zero_ne_zeroPoint (K := K) hspecial.symm
  · have h3 : 3 ≤ D := by
      omega
    exact
      homogeneous_ge_three_polynomialFamilyHessianDefect_impossible
        (K := K)
        s.homogeneous
        h3
        s.hessianDefect

/-- The exact departure frontier is likewise empty for every `D >= 2` under
its current full-family homogeneity field. -/
theorem CanonicalSmithDepartureFrontier.impossible_of_two_le_degree
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    False := by
  by_cases h2 : D = 2
  · subst D
    have hsections :
        f.lossless.leftSection = f.lossless.rightSection :=
      quadraticPolynomialFamily_exactCollision_sections_eq
        f.lossless.family
        f.homogeneous
        f.lossless.leftSection
        f.lossless.rightSection
        f.hessianDefect
        f.lossless.exactCollision
    have hspecial :=
      congrArg polynomialSectionSpecialPoint hsections
    rw [f.lossless.leftSpecial, f.lossless.rightSpecial] at hspecial
    exact
      coordinateAxisPoint_zero_ne_zeroPoint (K := K) hspecial.symm
  · have h3 : 3 ≤ D := by
      omega
    exact
      homogeneous_ge_three_polynomialFamilyHessianDefect_impossible
        (K := K)
        f.homogeneous
        h3
        f.hessianDefect

/-! -----------------------------------------------------------------------
  Diagnostic consequences for the existing final interfaces
------------------------------------------------------------------------ -/

/-- The current Smith-frontier exhaustion interface is provable without JC2
or local Smith analysis, precisely because the full geometric state is already
inconsistent for `D >= 2`.  This theorem is intentionally named as a sanity
diagnostic rather than as the desired final reduction. -/
theorem canonicalSmithFrontierExhaustionUnderJC2_currentInterface_vacuous
    [CharZero K] :
    CanonicalSmithFrontierExhaustionUnderJC2 (K := K) := by
  intro _hJC2 D hD s _hfrontier
  exact s.impossible_of_two_le_degree hD

/-- The sharper departure-frontier exhaustion interface is vacuous for the
same reason. -/
theorem canonicalDepartureFrontierExhaustionUnderJC2_currentInterface_vacuous
    [CharZero K] :
    CanonicalDepartureFrontierExhaustionUnderJC2 (K := K) := by
  intro _hJC2 D hD f
  exact f.impossible_of_two_le_degree hD

/-- Most importantly, the current counterexample-entry interface alone rules
out its source proposition, with no use of JC2.  Therefore a future concrete
HC4 entry theorem into this exact structure would prove HC4 outright and is a
red flag: the structure is stronger than the intended HC4 counterexample
normal form. -/
theorem noCounterexample_of_currentCanonicalEntry
    [CharZero K]
    (Counterexample : Prop)
    (hentry :
      HasCanonicalExactCollisionEntryFrom
        (K := K) Counterexample) :
    ¬ Counterexample := by
  intro hcounter
  rcases hentry hcounter with ⟨D, e, hD⟩
  exact e.impossible_of_two_le_degree hD

end

end HC4.Valuation
