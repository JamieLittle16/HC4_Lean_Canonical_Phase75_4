import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCoupledPointedClosure
import HC4.Valuation.StrictSmithConstantResidualRigidity
import HC4.Polynomial.WeightBounds
import Mathlib.Tactic

/-!
# A18.4.60: coupled pointed normalisation preserves symmetric Smith minimality

The only remaining ramified raw-defect edge in the aligned-boundary closure
came from re-testing Smith minimality after the determinant-one pointed shear
of a genuinely coupled first wall.

A18.4.18 retained more geometry than that old branch used: every monomial on
the unpointed coupled first-wall special fibre has *negative* canonical
symmetric Smith derivative.  For the symmetric separator this is exactly the
strict transverse weight bound

    wt_(0,1,1,2) < 2.

The pointed source change is triangular:

    X_k |-> X_k + c X_0,  k = 1,2,3.

Since `X_0` has transverse weight zero, this substitution cannot increase the
transverse weight of any monomial.  Hence the strict bound survives all three
shears.  The shears are polynomial automorphisms, so the pointed special fibre
is still nonzero.  Any surviving pointed monomial therefore has negative
symmetric Smith derivative and supplies the witness required by
`IsSymmetricSmithPoleMinimal` at base/level zero.

Consequently the `notMinimal` branch of A18.4.20 is impossible for the actual
coupled presentation.  No ramification or rational defect spend is needed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Scalar special-fibre shear -/

/-- The field-valued special-fibre version of one elementary pointed shear. -/
def scalarElementaryShearVariable
    (k : Fin 4) (c : K) (i : Fin 4) : MvPolynomial (Fin 4) K :=
  if i = k then
    MvPolynomial.X k + MvPolynomial.C c * MvPolynomial.X (0 : Fin 4)
  else
    MvPolynomial.X i

/-- Ring homomorphism implementing the scalar elementary shear. -/
noncomputable def scalarElementaryShearHom
    (k : Fin 4) (c : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (scalarElementaryShearVariable k c)

@[simp] theorem scalarElementaryShearHom_C
    (k : Fin 4) (c r : K) :
    scalarElementaryShearHom k c (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [scalarElementaryShearHom]

@[simp] theorem scalarElementaryShearHom_X
    (k : Fin 4) (c : K) (i : Fin 4) :
    scalarElementaryShearHom k c (MvPolynomial.X i) =
      scalarElementaryShearVariable k c i := by
  simp [scalarElementaryShearHom]

/-- Passing to the parameter special fibre commutes with an elementary shear,
with the shear coefficient replaced by its constant term. -/
theorem polynomialFamilySpecialFiber_elementaryShearHom_eq_scalar
    (k : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber (elementaryShearHom (K := K) k c P) =
      scalarElementaryShearHom k (Polynomial.constantCoeff c)
        (polynomialFamilySpecialFiber P) := by
  apply MvPolynomial.induction_on P
  · intro r
    simp [polynomialFamilySpecialFiber, elementaryShearHom,
      scalarElementaryShearHom]
  · intro p q hp hq
    simpa [polynomialFamilySpecialFiber] using
      congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    have hvar :
        polynomialFamilySpecialFiber
            (elementaryShearVariable (K := K) k c i) =
          scalarElementaryShearVariable k (Polynomial.constantCoeff c) i := by
      by_cases hik : i = k
      · subst i
        simp [polynomialFamilySpecialFiber, elementaryShearVariable,
          scalarElementaryShearVariable]
      · simp [polynomialFamilySpecialFiber, elementaryShearVariable,
          scalarElementaryShearVariable, hik]
    have hmul := congrArg₂ (fun x y => x * y) hp hvar
    simpa [polynomialFamilySpecialFiber, map_mul,
      elementaryShearHom_X, scalarElementaryShearHom_X] using hmul

/-! ## The triangular shear preserves the canonical transverse filtration -/

/-- Weak weight bounds can be enlarged. -/
theorem HC4.Polynomial.IsWeightLE.mono
    {σ R : Type*} [CommRing R]
    {w : σ → ℤ} {m n : ℤ} {P : MvPolynomial σ R}
    (hP : IsWeightLE w m P) (hmn : m ≤ n) :
    IsWeightLE w n P := by
  intro d hd
  exact (hP hd).trans hmn

/-- Powers multiply a weak weight bound by the natural exponent. -/
theorem HC4.Polynomial.IsWeightLE.pow_nsmul
    {σ R : Type*} [CommRing R] [DecidableEq σ]
    {w : σ → ℤ} {m : ℤ} {P : MvPolynomial σ R}
    (hP : IsWeightLE w m P) (n : ℕ) :
    IsWeightLE w (n • m) (P ^ n) := by
  induction n with
  | zero =>
      simpa using
        (isWeightLE_of_isWeightedHomogeneous
          (MvPolynomial.isWeightedHomogeneous_one R w))
  | succ n ih =>
      simpa [pow_succ, succ_nsmul, add_mul] using ih.mul hP

/-- A finite product inherits the sum of the individual weak bounds. -/
theorem isWeightLE_finset_prod
    {ι σ R : Type*} [CommRing R] [DecidableEq σ]
    (w : σ → ℤ)
    (s : Finset ι)
    (P : ι → MvPolynomial σ R)
    (m : ι → ℤ)
    (hP : ∀ i ∈ s, IsWeightLE w (m i) (P i)) :
    IsWeightLE w (∑ i ∈ s, m i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (isWeightLE_of_isWeightedHomogeneous
          (MvPolynomial.isWeightedHomogeneous_one R w))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (hP a (by simp)).mul
        (ih (fun i hi => hP i (by simp [hi])))

/-- Every coordinate of the canonical transverse weight is nonnegative. -/
theorem canonicalSmithTransverseWeight_nonnegative
    (i : Fin 4) :
    0 ≤ canonicalSmithTransverseWeight i := by
  fin_cases i <;> simp [canonicalSmithTransverseWeight]

/-- A scalar elementary shear variable has weight at most the weight of the
variable it replaces. -/
theorem scalarElementaryShearVariable_isWeightLE
    (k : Fin 4) (c : K) (i : Fin 4) :
    IsWeightLE canonicalSmithTransverseWeight
      (canonicalSmithTransverseWeight i)
      (scalarElementaryShearVariable k c i) := by
  by_cases hik : i = k
  · subst i
    unfold scalarElementaryShearVariable
    simp only [if_pos]
    apply HC4.Polynomial.IsWeightLE.add
    · exact isWeightLE_of_isWeightedHomogeneous
        (MvPolynomial.isWeightedHomogeneous_X K
          canonicalSmithTransverseWeight k)
    · have hcx0 :
          IsWeightLE canonicalSmithTransverseWeight
            (canonicalSmithTransverseWeight (0 : Fin 4))
            (MvPolynomial.C c * MvPolynomial.X (0 : Fin 4)) := by
        exact isWeightLE_of_isWeightedHomogeneous
          ((MvPolynomial.isWeightedHomogeneous_C
              canonicalSmithTransverseWeight c).mul
            (MvPolynomial.isWeightedHomogeneous_X K
              canonicalSmithTransverseWeight (0 : Fin 4)))
      exact HC4.Polynomial.IsWeightLE.mono hcx0 (by
        simpa [canonicalSmithTransverseWeight] using
          canonicalSmithTransverseWeight_nonnegative k)
  · unfold scalarElementaryShearVariable
    rw [if_neg hik]
    exact isWeightLE_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_X K
        canonicalSmithTransverseWeight i)

/-- The image of one source monomial under a scalar triangular shear has
canonical transverse weight no larger than the source monomial. -/
theorem scalarElementaryShearHom_monomial_isWeightLE
    (k : Fin 4) (c : K)
    (n : Fin 4 →₀ ℕ) (r : K) :
    IsWeightLE canonicalSmithTransverseWeight
      (Finsupp.weight canonicalSmithTransverseWeight n)
      (scalarElementaryShearHom k c (MvPolynomial.monomial n r)) := by
  rw [scalarElementaryShearHom]
  rw [MvPolynomial.eval₂Hom_monomial]
  have hC :
      IsWeightLE canonicalSmithTransverseWeight 0 (MvPolynomial.C r) :=
    isWeightLE_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C
        canonicalSmithTransverseWeight r)
  have hprod :
      IsWeightLE canonicalSmithTransverseWeight
        (∑ i ∈ n.support,
          n i • canonicalSmithTransverseWeight i)
        (n.prod fun i q => (scalarElementaryShearVariable k c i) ^ q) := by
    simpa [Finsupp.prod] using
      isWeightLE_finset_prod canonicalSmithTransverseWeight n.support
        (fun i => (scalarElementaryShearVariable k c i) ^ n i)
        (fun i => n i • canonicalSmithTransverseWeight i)
        (fun i hi =>
          HC4.Polynomial.IsWeightLE.pow_nsmul
            (scalarElementaryShearVariable_isWeightLE (K := K) k c i) (n i))
  have hmul := hC.mul hprod
  rw [zero_add] at hmul
  simpa [Finsupp.weight_apply, Finsupp.prod] using hmul

/-- Therefore a scalar pointed shear preserves every strict upper bound for
the canonical transverse weight. -/
theorem scalarElementaryShearHom_isWeightLT
    (k : Fin 4) (c : K)
    {m : ℤ} {P : MvPolynomial (Fin 4) K}
    (hP : IsWeightLT canonicalSmithTransverseWeight m P) :
    IsWeightLT canonicalSmithTransverseWeight m
      (scalarElementaryShearHom k c P) := by
  classical
  intro d hd
  have hsum :
      scalarElementaryShearHom k c P =
        ∑ n ∈ P.support,
          scalarElementaryShearHom k c
            (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
    calc
      scalarElementaryShearHom k c P =
          scalarElementaryShearHom k c
            (∑ n ∈ P.support,
              MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
                exact congrArg (scalarElementaryShearHom k c) (MvPolynomial.as_sum P)
      _ = ∑ n ∈ P.support,
          scalarElementaryShearHom k c
            (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            simp only [map_sum]
  have hdSum :
      d ∈ (∑ n ∈ P.support,
        scalarElementaryShearHom k c
          (MvPolynomial.monomial n (MvPolynomial.coeff n P))).support := by
    rwa [← hsum]
  have hdUnion :
      d ∈ P.support.biUnion
        (fun n =>
          (scalarElementaryShearHom k c
            (MvPolynomial.monomial n (MvPolynomial.coeff n P))).support) :=
    MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨n, hnP, hdn⟩
  exact lt_of_le_of_lt
    (scalarElementaryShearHom_monomial_isWeightLE (K := K) k c n
      (MvPolynomial.coeff n P) hdn)
    (hP hnP)

/-! ## Scalar shears are automorphisms -/

/-- Applying the opposite scalar shear undoes one transverse shear. -/
theorem scalarElementaryShearHom_neg_comp
    (k : Fin 4) (hk0 : k ≠ (0 : Fin 4))
    (c : K) (P : MvPolynomial (Fin 4) K) :
    scalarElementaryShearHom k (-c) (scalarElementaryShearHom k c P) = P := by
  apply MvPolynomial.induction_on P
  · intro r
    simp
  · intro p q hp hq
    simpa using congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    simp only [map_mul, hp]
    by_cases hik : i = k
    · subst i
      simp [scalarElementaryShearVariable, hk0]
      ring
    · simp [scalarElementaryShearVariable, hik]

/-- In particular a transverse scalar elementary shear cannot kill a
nonzero polynomial. -/
theorem scalarElementaryShearHom_ne_zero
    (k : Fin 4) (hk0 : k ≠ (0 : Fin 4))
    (c : K) {P : MvPolynomial (Fin 4) K}
    (hP : P ≠ 0) :
    scalarElementaryShearHom k c P ≠ 0 := by
  intro hzero
  have h := congrArg (scalarElementaryShearHom k (-c)) hzero
  rw [scalarElementaryShearHom_neg_comp k hk0 c P] at h
  simpa using hP h

/-! ## The actual coupled pointed special fibre -/

/-- Scalar three-shear induced on a parameter special fibre. -/
noncomputable def scalarPointedBoundaryShear
    (b0 : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  scalarElementaryShearHom (3 : Fin 4) (b0 3)
    (scalarElementaryShearHom (2 : Fin 4) (b0 2)
      (scalarElementaryShearHom (1 : Fin 4) (b0 1) F))

/-- The special fibre of the polynomial-family pointed shear is exactly the
corresponding scalar three-shear. -/
theorem polynomialFamilySpecialFiber_pointedBoundaryShearFamily
    (b : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber (pointedBoundaryShearFamily b P) =
      scalarPointedBoundaryShear (polynomialSectionSpecialPoint b)
        (polynomialFamilySpecialFiber P) := by
  unfold pointedBoundaryShearFamily scalarPointedBoundaryShear
  rw [polynomialFamilySpecialFiber_elementaryShearHom_eq_scalar]
  rw [polynomialFamilySpecialFiber_elementaryShearHom_eq_scalar]
  rw [polynomialFamilySpecialFiber_elementaryShearHom_eq_scalar]
  simp [pointedBoundaryShearPolynomialCoefficient,
    polynomialSectionSpecialPoint]

/-- A negative symmetric Smith derivative is exactly a transverse-weight
value below `2`. -/
theorem canonicalSmithTransverseWeight_lt_two_of_smithNegative
    (d : Fin 4 →₀ ℕ)
    (hneg : smithSeparatorDelta 1 1 (smithAxisProjection d) < 0) :
    Finsupp.weight canonicalSmithTransverseWeight d < 2 := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [canonicalSmithTransverseWeight, Fin.sum_univ_four]
    rw [smithSeparatorDelta_one_one_formula] at hneg
    simp [smithAxisProjection] at hneg
    omega
  · intro i
    simp

/-- Conversely the strict transverse-weight bound makes the symmetric Smith
derivative negative. -/
theorem smithNegative_of_canonicalSmithTransverseWeight_lt_two
    (d : Fin 4 →₀ ℕ)
    (hwt : Finsupp.weight canonicalSmithTransverseWeight d < 2) :
    smithSeparatorDelta 1 1 (smithAxisProjection d) < 0 := by
  rw [smithSeparatorDelta_one_one_formula]
  rw [Finsupp.weight_apply] at hwt
  rw [Finsupp.sum_fintype] at hwt
  · simp [canonicalSmithTransverseWeight, Fin.sum_univ_four] at hwt
    simp [smithAxisProjection]
    omega
  · intro i
    simp

/-- The A18.4.18 negative-support invariant is precisely a strict weight
bound on the unpointed coupled special fibre. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallSpecialFiber_isWeightLT_two
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    IsWeightLT canonicalSmithTransverseWeight 2
      (polynomialFamilySpecialFiber P.firstWallFamily) := by
  intro d hd
  exact canonicalSmithTransverseWeight_lt_two_of_smithNegative d
    (P.allSpecialFiberNegative hd)

/-- Point normalisation preserves the same strict transverse support bound. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSpecialFiber_isWeightLT_two
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    IsWeightLT canonicalSmithTransverseWeight 2
      (polynomialFamilySpecialFiber P.pointedFamily) := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
  rw [polynomialFamilySpecialFiber_pointedBoundaryShearFamily]
  unfold scalarPointedBoundaryShear
  apply scalarElementaryShearHom_isWeightLT
  apply scalarElementaryShearHom_isWeightLT
  apply scalarElementaryShearHom_isWeightLT
  exact P.firstWallSpecialFiber_isWeightLT_two

/-- The unpointed first-wall special fibre is nonzero, already witnessed by
its symmetric-minimal projected support. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallSpecialFiber_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    polynomialFamilySpecialFiber P.firstWallFamily ≠ 0 := by
  rcases P.symmetricMinimal with ⟨e, he, _⟩
  unfold smithProjectedSupport at he
  rcases Finset.mem_image.mp he with ⟨d, hd, _⟩
  intro hzero
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallFamily at hzero
  rw [hzero] at hd
  simp at hd

/-- Hence the pointed special fibre is also nonzero. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSpecialFiber_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    polynomialFamilySpecialFiber P.pointedFamily ≠ 0 := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
  rw [polynomialFamilySpecialFiber_pointedBoundaryShearFamily]
  unfold scalarPointedBoundaryShear
  apply scalarElementaryShearHom_ne_zero (K := K) (3 : Fin 4) (by decide)
  apply scalarElementaryShearHom_ne_zero (K := K) (2 : Fin 4) (by decide)
  apply scalarElementaryShearHom_ne_zero (K := K) (1 : Fin 4) (by decide)
  exact P.firstWallSpecialFiber_ne_zero

/-- **Coupled pointing cannot destroy symmetric Smith minimality.** -/
theorem AdaptiveAlignedSmithCanonicalCoupledPointedPresentation.pointedSpecialFiber_symmetricMinimal
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s) :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P.source.pointedFamily))
      0
      (fun _ => (0 : ℤ)) := by
  have hne := P.source.pointedSpecialFiber_ne_zero
  have hsupp :
      (polynomialFamilySpecialFiber P.source.pointedFamily).support.Nonempty := by
    exact MvPolynomial.support_nonempty.mpr hne
  rcases hsupp with ⟨d, hd⟩
  let e := smithAxisProjection d
  refine ⟨e, ?_, ?_⟩
  · unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  · have hwt := P.source.pointedSpecialFiber_isWeightLT_two hd
    have hneg := smithNegative_of_canonicalSmithTransverseWeight_lt_two d hwt
    simpa [smithIntegralSeparatorTilt, smithRescaledOldMinimum,
      finiteIntegralRescaledTilt] using (le_of_lt hneg)

/-- The formerly recursive nonminimal case is therefore contradictory. -/
theorem AdaptiveAlignedSmithCanonicalCoupledPointedPresentation.not_notMinimal
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s) :
    ¬ ¬ IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P.source.pointedFamily))
      0
      (fun _ => (0 : ℤ)) := by
  exact not_not_intro P.pointedSpecialFiber_symmetricMinimal

end

end HC4.Valuation
