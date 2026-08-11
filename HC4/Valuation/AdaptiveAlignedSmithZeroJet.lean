import HC4.Valuation.AdaptiveAlignedSmithMinimalWall
import HC4.Valuation.ZeroGradientNormalization
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# Zero-source-jet provenance for the adaptive aligned-Smith macro

The mixed-degree aligned-Smith endpoint already retains the exact collision,
Hessian clock, nonlinear degree cap and symmetric-minimal special fibre.
For the state-neutral canonical wall classifier we also need the normalized
axis data on that *same* raw special fibre.

It is not safe to obtain this by normalizing the endpoint a second time:
doing so can remove an attained zero-level Smith monomial.  Instead we retain
the actual invariant possessed by the input family.

A family has zero source jet when its source-constant coefficient and all
four source-linear coefficients vanish.  Every operation used by the aligned
Smith macro is coefficientwise in the source exponents and introduces no new
source monomials.  Hence this condition is inherited by the genuine first
wall and by the no-wall primitive normalization.

The final theorem converts zero-source-jet provenance, the exact zero-left
collision and the canonical right special point directly into
`HasNormalizedSmithAxisData` for the raw special fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## The source-jet invariant -/

/-- Vanishing of the source constant term and all four source-linear terms.

This is the coefficientwise form of zero-jet normalization that is stable
under every support-decreasing aligned-Smith transformation. -/
structure HasZeroSourceJet
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop where
  constantCoeff_zero :
    MvPolynomial.coeff 0 P = 0
  linearCoeff_zero :
    ∀ i : Fin 4,
      MvPolynomial.coeff (Finsupp.single i 1) P = 0

/-- A support-decreasing source transformation preserves a zero source jet. -/
theorem HasZeroSourceJet.of_support_subset
    {P Q : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P)
    (hsub : Q.support ⊆ P.support) :
    HasZeroSourceJet Q := by
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hQmem : (0 : Fin 4 →₀ ℕ) ∈ Q.support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hPmem : (0 : Fin 4 →₀ ℕ) ∈ P.support := hsub hQmem
    exact
      (MvPolynomial.mem_support_iff.mp hPmem)
        hP.constantCoeff_zero
  · intro i
    by_contra hne
    have hQmem :
        Finsupp.single i 1 ∈ Q.support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hPmem :
        Finsupp.single i 1 ∈ P.support := hsub hQmem
    exact
      (MvPolynomial.mem_support_iff.mp hPmem)
        (hP.linearCoeff_zero i)

/-- The coefficientwise zero source jet implies vanishing of the family
value at the literal zero section. -/
theorem HasZeroSourceJet.valueAtZero
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P) :
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K)) P = 0 := by
  rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
  exact hP.constantCoeff_zero

/-- The coefficientwise zero source jet implies vanishing of every family
gradient component at the literal zero section. -/
theorem HasZeroSourceJet.gradientAtZero
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P)
    (i : Fin 4) :
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i P) = 0 := by
  rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
  rw [coeff_pderiv_mixedDegree
    (K := Polynomial K) i P (0 : Fin 4 →₀ ℕ)]
  simpa using hP.linearCoeff_zero i

/-- The project's zero-jet-normalized family really has zero source jet in
the coefficientwise sense used by the aligned macro. -/
theorem zeroJetNormalizedFamily_hasZeroSourceJet
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasZeroSourceJet (zeroJetNormalizedFamily P) := by
  refine ⟨?_, ?_⟩
  · have h := zeroJetNormalizedFamily_valueAtZero P
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at h
    exact h
  · intro i
    have h := zeroJetNormalizedFamily_gradientAtZero P i
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at h
    rw [coeff_pderiv_mixedDegree
      (K := Polynomial K) i
      (zeroJetNormalizedFamily P)
      (0 : Fin 4 →₀ ℕ)] at h
    simpa using h

/-! ## Support preservation through the aligned macro -/

/-- A genuine aligned first-wall family introduces no new source exponent. -/
theorem support_alignedSmithGenuineFirstWallFamily_subset_source
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall).support ⊆
      P.support := by
  intro d hd
  let N := alignedSmithGenuineFirstWall P a b hwall
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  have hdSmith :
      d ∈
        (integralSmithConformalFamily
          (2 * N) (2 * N) Pram
          (alignedSmithGenuineFirstWall_integralCoefficients
            P a b hwall)).support := by
    simpa [alignedSmithGenuineFirstWallFamily, N, Pram] using hd
  have hdRam :
      d ∈ Pram.support :=
    support_integralSmithConformalFamily_subset
      (2 * N) (2 * N) Pram
      (alignedSmithGenuineFirstWall_integralCoefficients
        P a b hwall)
      hdSmith
  exact
    (MvPolynomial.support_map_subset
      (parameterRamificationHom
        (K := K) alignedSmithRamificationIndex) P)
      (by simpa [Pram] using hdRam)

/-- Hence a genuine aligned first wall preserves the zero source jet. -/
theorem HasZeroSourceJet.alignedSmithGenuineFirstWallFamily
    (hP : HasZeroSourceJet P)
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    HasZeroSourceJet
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall) :=
  hP.of_support_subset
    (support_alignedSmithGenuineFirstWallFamily_subset_source
      (K := K) P a b hwall)

/-- The no-wall primitive aligned-Smith normalization introduces no new
source exponent. -/
theorem support_noWallPrimitiveSmithFamily_subset_source
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone).support ⊆
      P.support := by
  intro d hd
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P a b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ e ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P e)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection e)) :=
    fun e he =>
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone m he
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  have hdFinal :
      d ∈
        (commonParameterFactorFamily
          (alignedSmithRamificationIndex * m)
          Q hcommon).support := by
    simpa [noWallPrimitiveSmithFamily,
      hne, m, N, hlegal, Pram, hsmith, Q, hcommon] using hd
  have hdQ :
      d ∈ Q.support :=
    support_commonParameterFactorFamily_subset
      (alignedSmithRamificationIndex * m)
      Q hcommon hdFinal
  have hdRam :
      d ∈ Pram.support := by
    dsimp [Q] at hdQ
    exact
      support_integralSmithConformalFamily_subset
        (2 * N) (2 * N) Pram hsmith hdQ
  exact
    (MvPolynomial.support_map_subset
      (parameterRamificationHom
        (K := K) alignedSmithRamificationIndex) P)
      (by simpa [Pram] using hdRam)

/-- Hence the no-wall primitive endpoint also preserves the zero source jet. -/
theorem HasZeroSourceJet.noWallPrimitiveSmithFamily
    (hP : HasZeroSourceJet P)
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b) :
    HasZeroSourceJet
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone) :=
  hP.of_support_subset
    (support_noWallPrimitiveSmithFamily_subset_source
      (K := K) P a b Delta hdef hnone)

/-! ## Raw special-fibre axis data -/

/-- A zero-source-jet family with a canonical zero-left exact collision has
normalized axis data on its *raw* special fibre.

This is the exact adapter needed by the canonical Smith-wall classifier.
No second zero-jet normalization is performed. -/
theorem HasZeroSourceJet.specialFiber_axisData
    (hP : HasZeroSourceJet P)
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasNormalizedSmithAxisData
      (polynomialFamilySpecialFiber P) := by
  let F := polynomialFamilySpecialFiber P
  have hspecial :=
    polynomialFamilyExactGradientCollision_specialFiber
      P (zeroPolynomialSection (K := K)) b hcoll
  have hleft :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        Fin.cons (0 : K) (fun _ : Fin 3 => 0) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [polynomialSectionSpecialPoint]
    · simp [polynomialSectionSpecialPoint]
  have hright :
      polynomialSectionSpecialPoint b =
        Fin.cons (1 : K) (fun _ : Fin 3 => 0) := by
    rw [hb]
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [coordinateAxisPoint]
    · simp [coordinateAxisPoint]
  have haxisCollision :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [F, hleft, hright] using hspecial
  have hfamilyZero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i P) = 0 :=
    hP.gradientAtZero
  have hspecialZero :=
    polynomialFamilyGradientZero_specialFiber
      P (zeroPolynomialSection (K := K)) hfamilyZero
  refine ⟨haxisCollision, ?_, ?_⟩
  · intro i
    have hi := hspecialZero i
    simpa [mvGradientComponentAt, F, hleft] using hi
  · have hv :=
      polynomialFamilySpecialFiber_valueAt
        P (zeroPolynomialSection (K := K))
    calc
      MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F =
        Polynomial.constantCoeff
          (MvPolynomial.eval
            (zeroPolynomialSection (K := K)) P) := by
              simpa [F, hleft] using hv
      _ = 0 := by
        change 
          Polynomial.constantCoeff
            (MvPolynomial.eval
              (fun _ : Fin 4 => (0 : Polynomial K)) P) = 0
        rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq,
          hP.constantCoeff_zero]
        simp

end

end HC4.Valuation
