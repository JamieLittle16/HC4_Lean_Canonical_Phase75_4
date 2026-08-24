import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyRS2ReadyFrontier
import Mathlib.Tactic

/-!
# Stage 4B26: elimination of the lone pure-transverse-linear corner

Stage 4B25 sharpened the generalized `x₀^e L^m` RS2 algebra to the exact
numerical condition `2 ≤ e + m`.  Since the first transverse degree is
positive, the only non-RS2-ready normal form is

    e = 0,  m = 1.

That corner is impossible for a much simpler reason than any Hessian
classification.  The honest right-recentered family is centred at the old
right collision section.  The original aligned family has zero source jet at
the old left section, and the exact gradient collision therefore says that
the gradient also vanishes at the old right section.  Translation carries
this to zero gradient of the right-recentered family at its literal origin,
and hence to zero gradient of its special fibre at the origin.

But `e = 0, m = 1` says that the nonzero maximal homogeneous first-key slice
has total source degree one and is purely transverse.  Since that slice is an
actual coefficient subpacket of the first weighted initial form, and that
initial form is coefficientwise inherited from the honest special fibre, it
would give a nonzero source-linear coefficient of the special fibre.  This
contradicts the zero gradient just proved.

Thus every non-repair B24 normal form is genuinely RS2-ready.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The honest right-recentered closing family has zero source gradient at
its literal zero section.  This is just zero-jet provenance transported
through the retained exact collision and the actual source translation. -/
theorem family_gradientAtZero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i : Fin 4) :
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i C.family) = 0 := by
  let E := B.aligned.endpoint

  have horigin :
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i E.family) = 0 := by
    simpa [E] using B.aligned.zeroSourceJet.gradientAtZero i

  have hright :
      MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) = 0 := by
    calc
      MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) =
          MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i E.family) := by
              exact (E.exactCollision i).symm
      _ = 0 := horigin

  change
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i E.rightRecenteredFamily) = 0
  unfold AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily
  rw [pderiv_polynomialFamilyTranslationHom]
  calc
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (polynomialFamilyTranslationHom (K := K) E.movingSection
          (MvPolynomial.pderiv i E.family)) =
        MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) := by
            simpa using
              (eval_polynomialFamilyTranslationHom_difference
                (K := K) E.movingSection E.movingSection
                (MvPolynomial.pderiv i E.family))
    _ = 0 := hright

/-- Consequently every source-linear coefficient of the honest
right-recentered special fibre vanishes. -/
theorem specialFiber_linearCoeff_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (polynomialFamilySpecialFiber C.family) = 0 := by
  have hspecial :=
    polynomialFamilySpecialFiber_gradientComponent
      C.family (zeroPolynomialSection (K := K)) i
  have hfamily := C.family_gradientAtZero i
  have hfamily' :
      MvPolynomial.eval (zeroPolynomialSection (K := K))
          (MvPolynomial.pderiv i C.family) = 0 := by
    simpa only [zeroPolynomialSection] using hfamily
  have hconst :
      Polynomial.constantCoeff
          (MvPolynomial.eval (zeroPolynomialSection (K := K))
            (MvPolynomial.pderiv i C.family)) = 0 := by
    simpa using congrArg Polynomial.constantCoeff hfamily'
  have hgrad :
      mvGradientComponentAt
          (fun _ : Fin 4 => (0 : K))
          (polynomialFamilySpecialFiber C.family) i = 0 := by
    calc
      mvGradientComponentAt
          (fun _ : Fin 4 => (0 : K))
          (polynomialFamilySpecialFiber C.family) i =
          Polynomial.constantCoeff
            (MvPolynomial.eval (zeroPolynomialSection (K := K))
              (MvPolynomial.pderiv i C.family)) := by
                simpa [zeroPolynomialSection, polynomialSectionSpecialPoint]
                  using hspecial
      _ = 0 := hconst
  unfold mvGradientComponentAt at hgrad
  rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at hgrad
  rw [coeff_pderiv_mixedDegree
    (K := K) i (polynomialFamilySpecialFiber C.family)
    (0 : Fin 4 →₀ ℕ)] at hgrad
  simpa using hgrad

/-- A nonzero coefficient of a homogeneous first-key slice is an actual
nonzero coefficient of the honest special fibre. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.slice_coeff_ne_zero_of_specialFiber
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    {d : Fin 4 →₀ ℕ}
    (hd : MvPolynomial.coeff d D.sliceData.sliceData.slice ≠ 0) :
    MvPolynomial.coeff d (polynomialFamilySpecialFiber C.family) ≠ 0 := by
  have hQ := (D.sliceData.sliceData.slice_source d hd).1
  have hQ' := hQ
  change
    MvPolynomial.coeff d
      (initialForm pureLongitudinalTransverseWeight
        (-(firstPositiveTransverseSourceDegree
          (polynomialFamilySpecialFiber C.family) L.hpos : ℤ))
        (polynomialFamilySpecialFiber C.family)) ≠ 0 at hQ'
  rw [coeff_initialForm] at hQ'
  intro hzero
  simp [hzero] at hQ'

/-- The unique non-RS2-ready numerical corner from B25 cannot occur. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.not_linearCorner
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    ¬ (D.sourceExponent = 0 ∧ D.transverseDegree = 1) := by
  rintro ⟨he, hm⟩

  rcases MvPolynomial.support_nonempty.mpr
      D.sliceData.sliceData.slice_ne_zero with ⟨d, hdmem⟩
  have hd : MvPolynomial.coeff d D.sliceData.sliceData.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdmem
  have hdF := D.slice_coeff_ne_zero_of_specialFiber hd

  have hd0eq : d (0 : Fin 4) = D.sourceExponent := by
    have hlong := D.sliceData.sliceData.slice_longitudinalExponent d hd
    simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent]
      using hlong
  have hd0 : d (0 : Fin 4) = 0 := by
    rw [hd0eq, he]

  have htransD :
      pureLongitudinalTransverseDegree d = D.transverseDegree := by
    have htrans := D.sliceData.sliceData.slice_exactTransverseDegree d hd
    simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree]
      using htrans
  have hsum :
      d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) = 1 := by
    unfold pureLongitudinalTransverseDegree at htransD
    rw [hm] at htransD
    exact htransD

  have hcases :
      (d (1 : Fin 4) = 1 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) ∨
      (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 1 ∧ d (3 : Fin 4) = 0) ∨
      (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 1) := by
    omega

  rcases hcases with h1 | h2 | h3
  · have hdeq : d = Finsupp.single (1 : Fin 4) 1 := by
      apply Finsupp.ext
      intro j
      fin_cases j <;> simp [hd0, h1.1, h1.2.1, h1.2.2]
    rw [hdeq] at hdF
    exact hdF (C.specialFiber_linearCoeff_zero (1 : Fin 4))
  · have hdeq : d = Finsupp.single (2 : Fin 4) 1 := by
      apply Finsupp.ext
      intro j
      fin_cases j <;> simp [hd0, h2.1, h2.2.1, h2.2.2]
    rw [hdeq] at hdF
    exact hdF (C.specialFiber_linearCoeff_zero (2 : Fin 4))
  · have hdeq : d = Finsupp.single (3 : Fin 4) 1 := by
      apply Finsupp.ext
      intro j
      fin_cases j <;> simp [hd0, h3.1, h3.2.1, h3.2.2]
    rw [hdeq] at hdF
    exact hdF (C.specialFiber_linearCoeff_zero (3 : Fin 4))

/-- **Stage 4B26 exact first-key frontier.**

The exceptional linear corner from B25 is impossible.  Therefore every
surviving non-repair first-key normal form is already numerically eligible
for the sharp generalized RS2 rigidity theorem. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.rankTwoRepair_or_rs2Ready
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyXeLmRS2ReadyData D) := by
  rcases D.rankTwoRepair_or_linearCorner_or_rs2Ready F complexity with
    hrepair | hcorner | hrs2
  · exact Or.inl hrepair
  · exact False.elim (D.not_linearCorner hcorner)
  · exact Or.inr hrs2

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
