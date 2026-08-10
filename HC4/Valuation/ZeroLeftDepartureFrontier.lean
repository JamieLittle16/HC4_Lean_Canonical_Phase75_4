import HC4.Valuation.DefectRetainingDepartureFrontier
import HC4.Valuation.PointedShearContinuation
import HC4.Valuation.SeparatedRightWallScaleDescent
import HC4.Valuation.RigidClosingRecenteredSource
import Mathlib.Tactic

/-!
# Zero-left provenance at the canonical Smith departure frontier

The global geometric restart state always carries its marked collision as

    0 ~ b(tau).

The departure-ready Smith frontier retained the transformed left section only
through the weaker fact that its special point is zero.  That is sufficient for
special-fibre collision arguments, but it is too weak for the final rigid
closing assembly: recentering by a merely *special-zero* moving section destroys
ordinary source homogeneity.

This file retains the stronger provenance that is actually present along the
global zero-section dispatcher.  The three local branches preserve the
identically-zero left section:

* the primitive branch does not move it;
* the pure coefficient wall sends zero to zero under the integral Smith section
  transform;
* the no-wall primitive normalization likewise sends zero to zero through
  ramification, the integral Smith transform, and common-factor extraction.

Consequently every globally reached departure frontier can be chosen with a
literal zero left section.  On such a frontier the defect-preserving rigid Smith
exposure also has zero left section, so its nominal ``recentring'' is the
identity.  The rigid source family therefore retains the ordinary source
homogeneity already proved for the exposure family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## A departure frontier retaining literal zero-left provenance -/

/-- A departure-ready Smith frontier that genuinely comes from the canonical
zero-left global collision, not merely from a section whose special point is
zero. -/
structure CanonicalZeroLeftSmithDepartureFrontier
    (D complexity : ℕ) where
  frontier : CanonicalSmithDepartureFrontier (K := K) D complexity
  leftSection_eq_zero :
    frontier.lossless.leftSection = zeroPolynomialSection (K := K)

/-- Proposition-level wrapper for the zero-left departure frontier. -/
def HasCanonicalZeroLeftSmithDepartureFrontier
    (D complexity : ℕ) : Prop :=
  Nonempty
    (CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity)

/-- Forgetting literal zero-left provenance recovers the former departure
frontier. -/
theorem CanonicalZeroLeftSmithDepartureFrontier.toDeparture
    {D complexity : ℕ}
    (f : CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity) :
    HasCanonicalSmithDepartureFrontier (K := K) D complexity :=
  ⟨f.frontier⟩

/-! ## A provenance-retaining symmetric-minimal constructor -/

/-- The generic symmetric-minimal constructor with the retained equality of
its left section.  This is the same mathematical construction as
`canonicalSymmetricMinimal_departureFrontier`; the extra conclusion merely
prevents the section field from being hidden behind `Nonempty`. -/
theorem canonicalSymmetricMinimal_departureFrontier_with_leftSection
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D Delta : ℕ}
    (hfull : P.IsHomogeneous D)
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    (complexity : ℕ) :
    ∃ f : CanonicalSmithDepartureFrontier (K := K) D complexity,
      f.lossless.leftSection = a := by
  have hprojected :
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P)).Nonempty := by
    rcases hminimal with ⟨e, he, _hle⟩
    exact ⟨e, he⟩
  have hspecial :=
    polynomialFamilyCollision_specialFiber_zero_axisZero
      P a b hcoll ha hb
  have hmin :=
    canonicalSpecialFiberSmith_minimum
      (polynomialFamilySpecialFiber P)
  have hattain :=
    canonicalSpecialFiberSmith_attainment
      (polynomialFamilySpecialFiber P)
      hprojected
  have hout :=
    homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair
      (K := K)
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      hhom hD hspecial
      0
      (fun _ => (0 : ℤ))
      hminimal hmin hattain
      complexity
  let lossless :
      CanonicalSmithLosslessFrontier
        (K := K) D complexity :=
    { family := P
      leftSection := a
      rightSection := b
      specialHomogeneous := hhom
      exactCollision := hcoll
      leftSpecial := ha
      rightSpecial := hb
      symmetricMinimal := hminimal
      subfaceNonempty := by
        simpa [canonicalSpecialFiberSmithSubface] using hout.1
      persistentPacket := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.1
      packet_ne_zero := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.2.1
      canonicalOutcome := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.2.2 }
  let f : CanonicalSmithDepartureFrontier
      (K := K) D complexity :=
    { defect := Delta
      lossless := lossless
      homogeneous := by
        simpa [lossless] using hfull
      hessianDefect := by
        simpa [lossless] using hdef }
  refine ⟨f, ?_⟩
  rfl

/-- Primitive zero-Smith source with literal zero-left provenance. -/
theorem primitiveZeroSmithSource_zeroLeftDepartureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hprimitive : HasPrimitiveZeroSmithSource P)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity := by
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  have hhom := polynomialFamilySpecialFiber_isHomogeneous P hP
  have hminimal :=
    primitiveZeroSmithSource_specialFiber_symmetricMinimal P hprimitive
  rcases
      canonicalSymmetricMinimal_departureFrontier_with_leftSection
        P (zeroPolynomialSection (K := K)) b
        hP hhom hD hdef hcoll ha hb hminimal complexity with
    ⟨f, hf⟩
  exact ⟨{ frontier := f, leftSection_eq_zero := hf }⟩

/-- Pure coefficient first wall with literal zero-left provenance. -/
theorem pureCoefficientWall_zeroLeftDepartureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hcoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithCoefficientWalls P)
    (hnotB :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithSectionWalls b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity := by
  let a := zeroPolynomialSection (K := K)
  let Q := alignedSmithGenuineFirstWallFamily (K := K) P a b hwall
  let a' := alignedSmithGenuineFirstWallSectionLeft (K := K) P a b hwall
  let b' := alignedSmithGenuineFirstWallSectionRight (K := K) P a b hwall
  have hnotA :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls a := by
    dsimp [a]
    exact
      not_mem_alignedSmithSectionWalls_zeroPolynomialSection
        (K := K)
        (alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall)
  have hQhom : Q.IsHomogeneous D := by
    dsimp [Q]
    exact alignedSmithGenuineFirstWallFamily_isHomogeneous P hP a b hwall
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D := by
    dsimp [Q]
    exact genuineFirstWall_specialFiber_isHomogeneous P hP a b hwall
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWall_preservesHessianDefect
        P a b hwall Delta hdef
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision Q a' b' := by
    dsimp [Q, a', b']
    exact alignedSmithGenuineFirstWall_preservesExactCollision P a b hwall hcoll
  have ha :
      polynomialSectionSpecialPoint a = (fun _ => (0 : K)) := by
    dsimp [a]
    exact polynomialSectionSpecialPoint_zeroPolynomialSection
  have hpoints :=
    pureCoefficientWall_specialPoints_canonical
      P a b hwall hnotA hnotB ha hb
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber Q))
        0
        (fun _ => (0 : ℤ)) := by
    dsimp [Q]
    exact genuineCoefficientWall_specialFiber_symmetricMinimal P a b hwall hcoeff
  rcases
      canonicalSymmetricMinimal_departureFrontier_with_leftSection
        Q a' b' hQhom hhom hD hQdef hQcoll
        (by simpa [a'] using hpoints.1)
        (by simpa [b'] using hpoints.2)
        hminimal complexity with
    ⟨f, hf⟩
  have ha' : a' = zeroPolynomialSection (K := K) := by
    dsimp [a']
    simpa [a] using
      (alignedSmithGenuineFirstWallSectionLeft_zero
        (K := K) P b hwall)
  exact
    ⟨{ frontier := f
       leftSection_eq_zero := hf.trans ha' }⟩

/-! ## No-wall zero-left collision -/

/-- Parameter ramification sends the identically-zero moving section to
itself. -/
@[simp] theorem parameterRamificationSection_zeroPolynomialSection
    (N : ℕ) :
    parameterRamificationSection
        (K := K) N (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  simp [parameterRamificationSection, zeroPolynomialSection]

/-- In the no-wall primitive normalization, a literal zero left section
remains literal zero.  We retain an explicit transformed right section rather
than hiding both sections behind an existential. -/
theorem noWallPrimitiveSmithFamily_zeroLeft_canonicalCollision
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∃ b' : Fin 4 → Polynomial K,
      HasPolynomialFamilyExactGradientCollision
        (noWallPrimitiveSmithFamily
          P (zeroPolynomialSection (K := K)) b Delta hdef hnone)
        (zeroPolynomialSection (K := K)) b' ∧
      polynomialSectionSpecialPoint b' =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
  let a := zeroPolynomialSection (K := K)
  let hne := zeroSmithSourceSupport_nonempty_of_noGenuineWall P a b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ d ∈ P.support,
        0 ≤ alignedSmithCoefficientValue
          (smithFamilyCoefficientOrder P d) N
          (smithSeparatorDelta 1 1 (smithAxisProjection d)) :=
    fun d hd => noWallPrimitiveSmithStep_coefficient_nonnegative P a b hnone m hd
  let Pram := parameterRamificationFamily (K := K) alignedSmithRamificationIndex P
  let hsmith := alignedSmith_coefficientDivisibility_of_nonnegative (K := K) P N hlegal
  have haDiv :
      HasIntegralSmithConformalSectionDivisibility
        (K := K) (2 * N) (2 * N)
        (zeroPolynomialSection (K := K)) :=
    zeroPolynomialSection_smithDivisibility (K := K) (2 * N)
  have hbdiv :
      HasIntegralSmithConformalSectionDivisibility
        (2 * N) (2 * N)
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex b) := by
    intro i
    fin_cases i
    · simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection]
    · have hz := rightTransverse_zero_of_noGenuineWall P a b hnone (1 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz := rightTransverse_zero_of_noGenuineWall P a b hnone (2 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
    · have hz := rightTransverse_zero_of_noGenuineWall P a b hnone (3 : Fin 4) (by decide)
      simp [smithConformalDerivativeCoefficient,
        smithConformalSourceExponent,
        parameterRamificationSection, hz]
  let bram := parameterRamificationSection (K := K) alignedSmithRamificationIndex b
  let b' := integralSmithConformalSection (2 * N) (2 * N) bram hbdiv
  have hramColl :
      HasPolynomialFamilyExactGradientCollision
        Pram (zeroPolynomialSection (K := K)) bram := by
    have h :=
      polynomialFamilyExactGradientCollision_parameterRamification
        alignedSmithRamificationIndex P a b hcoll
    simpa [a, Pram, bram] using h
  have hsmithCollRaw :
      HasPolynomialFamilyExactGradientCollision
        (integralSmithConformalFamily
          (2 * N) (2 * N) Pram hsmith)
        (integralSmithConformalSection
          (2 * N) (2 * N)
          (zeroPolynomialSection (K := K)) haDiv)
        b' := by
    dsimp [b']
    exact
      polynomialFamilyExactGradientCollision_integralSmithConformal
        (2 * N) (2 * N) Pram hsmith
        (zeroPolynomialSection (K := K)) bram
        haDiv hbdiv hramColl
  have haSmith :
      integralSmithConformalSection
          (2 * N) (2 * N)
          (zeroPolynomialSection (K := K)) haDiv =
        zeroPolynomialSection (K := K) :=
    integralSmithConformalSection_zeroPolynomialSection (2 * N) haDiv
  have hsmithColl :
      HasPolynomialFamilyExactGradientCollision
        (integralSmithConformalFamily
          (2 * N) (2 * N) Pram hsmith)
        (zeroPolynomialSection (K := K)) b' := by
    rw [← haSmith]
    exact hsmithCollRaw
  let Q := integralSmithConformalFamily (2 * N) (2 * N) Pram hsmith
  let hcommon := noWallPrimitiveSmithStep_commonFactor P a b Delta hdef hnone hne
  have hfinal :
      HasPolynomialFamilyExactGradientCollision
        (commonParameterFactorFamily
          (alignedSmithRamificationIndex * m) Q hcommon)
        (zeroPolynomialSection (K := K)) b' :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      (alignedSmithRamificationIndex * m) Q hcommon
      (zeroPolynomialSection (K := K)) b' hsmithColl
  have hbSpecial :
      polynomialSectionSpecialPoint b' =
        polynomialSectionSpecialPoint b := by
    dsimp [b', bram]
    exact
      alignedSmithSection_specialPoint_eq_of_transverse_zero
        b (rightTransverse_zero_of_noGenuineWall P a b hnone) N hbdiv
  refine ⟨b', ?_, hbSpecial.trans hb⟩
  simpa [noWallPrimitiveSmithFamily,
    a, hne, m, N, hlegal, Pram, hsmith, Q, hcommon] using hfinal

/-- No genuine wall with literal zero-left provenance. -/
theorem noWallPrimitiveSmithFamily_zeroLeftDepartureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity := by
  rcases
      noWallPrimitiveSmithFamily_zeroLeft_canonicalCollision
        P b Delta hdef hnone hcoll hb with
    ⟨b', hcoll', hb'⟩
  let Q := noWallPrimitiveSmithFamily
    P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  let hne := zeroSmithSourceSupport_nonempty_of_noGenuineWall
    P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let Delta' := alignedSmithRamificationIndex * Delta -
      4 * (alignedSmithRamificationIndex * m)
  have hhomFull : Q.IsHomogeneous D := by
    dsimp [Q]
    exact noWallPrimitiveSmithFamily_isHomogeneous
      P hP (zeroPolynomialSection (K := K)) b Delta hdef hnone
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D :=
    polynomialFamilySpecialFiber_isHomogeneous Q hhomFull
  have hQdef :
      HasPolynomialFamilyHessianDefect (K := K) Q Delta' := by
    dsimp [Q, Delta', hne, m]
    exact noWallPrimitiveSmithFamily_hasHessianDefect
      P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber Q))
        0 (fun _ => (0 : ℤ)) := by
    dsimp [Q]
    exact noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
      P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  rcases
      canonicalSymmetricMinimal_departureFrontier_with_leftSection
        Q (zeroPolynomialSection (K := K)) b'
        hhomFull hhom hD hQdef hcoll' ha hb' hminimal complexity with
    ⟨f, hf⟩
  exact ⟨{ frontier := f, leftSection_eq_zero := hf }⟩

/-! ## Zero-left local dispatcher and global defect induction -/

/-- The zero-section dispatcher with literal zero-left provenance retained in
all local frontier branches. -/
theorem alignedSmith_zeroSection_geometricDispatcher_zeroLeftDeparture
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalZeroLeftSmithDepartureFrontier (K := K) D complexity ∨
      HasSeparatedRightSmithSectionWall P b := by
  classical
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  by_cases hprimitive : HasPrimitiveZeroSmithSource P
  · exact Or.inl
      (primitiveZeroSmithSource_zeroLeftDepartureFrontier
        P hP b hdef hprimitive hD hcoll hb complexity)
  · by_cases hwall :
      HasAlignedSmithGenuineWall P (zeroPolynomialSection (K := K)) b
    · let N := alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
      by_cases hcoeff : N ∈ alignedSmithCoefficientWalls P
      · by_cases hB : N ∈ alignedSmithSectionWalls b
        · have hcoupled :
            HasCoupledAlignedSmithWall
              P (zeroPolynomialSection (K := K)) b := by
            refine ⟨hwall, ?_, ?_⟩
            · simpa [N] using hcoeff
            · exact Or.inr (by simpa [N] using hB)
          exact False.elim
            (coupledAlignedSmithWall_impossible_of_noPrimitive
              P hP (zeroPolynomialSection (K := K)) b hD hcoll
              ha hb hprimitive hcoupled)
        · exact Or.inl
            (pureCoefficientWall_zeroLeftDepartureFrontier
              P hP b hdef hwall
              (by simpa [N] using hcoeff)
              (by simpa [N] using hB)
              hD hcoll hb complexity)
      · have hcases := alignedSmithGenuineFirstWall_cases
          P (zeroPolynomialSection (K := K)) b hwall
        have hB : N ∈ alignedSmithSectionWalls b := by
          rcases hcases with hc | hA | hB
          · exact False.elim (hcoeff (by simpa [N] using hc))
          · have hnotA :
                N ∉ alignedSmithSectionWalls
                  (zeroPolynomialSection (K := K)) :=
              not_mem_alignedSmithSectionWalls_zeroPolynomialSection
                (K := K) N
            exact False.elim (hnotA (by simpa [N] using hA))
          · simpa [N] using hB
        exact Or.inr
          ⟨hwall, hprimitive,
            by simpa [N] using hcoeff,
            by simpa [N] using hB⟩
    · exact Or.inl
        (noWallPrimitiveSmithFamily_zeroLeftDepartureFrontier
          P hP b Delta hdef hwall hD hcoll hb complexity)

/-- Closed zero-left geometric step. -/
theorem alignedSmith_zeroSection_closedGeometricStep_zeroLeftDeparture
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalZeroLeftSmithDepartureFrontier (K := K) D complexity ∨
      HasCanonicalStrictGeometricDefectRestart (K := K) D Delta := by
  rcases
      alignedSmith_zeroSection_geometricDispatcher_zeroLeftDeparture
        P hP b hdef hD hcoll hb complexity with
    hlocal | hwall
  · exact Or.inl hlocal
  · exact Or.inr
      (separatedRightSmithWall_strictCanonicalGeometricRestart
        P hP b hwall hdef hcoll hb)

/-- One canonical state reaches a zero-left departure frontier or has a
strictly lower-defect canonical successor. -/
theorem canonicalGeometricState_closedStep_zeroLeftDeparture
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    HasCanonicalZeroLeftSmithDepartureFrontier (K := K) D complexity ∨
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        t.defect < s.defect ∧
        GlobalRestartProgress s.toGlobal t.toGlobal := by
  rcases
      alignedSmith_zeroSection_closedGeometricStep_zeroLeftDeparture
        s.family s.homogeneous s.movingSection s.hessianDefect
        hD s.exactCollision s.sectionSpecial complexity with
    hlocal | hrestart
  · exact Or.inl hlocal
  · exact Or.inr (canonicalState_of_strictGeometricDefectRestart s hrestart)

/-- Strong induction retaining literal zero-left provenance at the local
frontier. -/
theorem canonicalGeometricRestart_reachesZeroLeftDepartureFrontier_aux
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (n : ℕ) :
    ∀ s : CanonicalGeometricRestartState (K := K) D,
      s.defect = n →
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        CanonicalGeometricReachable (K := K) D s t ∧
        HasCanonicalZeroLeftSmithDepartureFrontier
          (K := K) D complexity := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hs
      rcases
          canonicalGeometricState_closedStep_zeroLeftDeparture
            (K := K) hD complexity s with
        hlocal | hnext
      · exact ⟨s, CanonicalGeometricReachable.refl s, hlocal⟩
      · rcases hnext with ⟨u, huDefect, huProgress⟩
        have huN : u.defect < n := by omega
        rcases ih u.defect huN u rfl with ⟨t, hut, hlocal⟩
        exact
          ⟨t,
            CanonicalGeometricReachable.step huProgress hut,
            hlocal⟩

/-- Every canonical exact-collision state reaches a departure frontier whose
retained left section is literally zero. -/
theorem canonicalGeometricRestart_reachesZeroLeftDepartureFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable (K := K) D s t ∧
      HasCanonicalZeroLeftSmithDepartureFrontier
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesZeroLeftDepartureFrontier_aux
      (K := K) hD complexity s.defect s rfl

/-! ## The rigid exposure no longer needs a genuine recentering -/

/-- Translation by the identically-zero source section is the identity on
polynomial families. -/
@[simp] theorem polynomialFamilyTranslationHom_zeroPolynomialSection
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilyTranslationHom
        (K := K) (zeroPolynomialSection (K := K)) P = P := by
  apply MvPolynomial.induction_on P
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    simp [hp, polynomialFamilyTranslationVariable, zeroPolynomialSection]

/-- A literal zero left section stays literal zero under the canonical
one-step defect-preserving Smith exposure. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposureLeftSection_eq_zero
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    (hleft : f.leftSection = zeroPolynomialSection (K := K)) :
    f.defectSmithExposureLeftSection = zeroPolynomialSection (K := K) := by
  unfold CanonicalSmithLosslessFrontier.defectSmithExposureLeftSection
  funext i
  have hreinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K)
        2 2
        (parameterRamificationSection
          (K := K) alignedSmithRamificationIndex f.leftSection)
        f.oneStepSmith_leftSectionDivisibility)
      i
  have hram_i :
      parameterRamificationSection
          (K := K) alignedSmithRamificationIndex f.leftSection i = 0 := by
    rw [hleft]
    simp [zeroPolynomialSection]
  let q :=
    integralSmithConformalSection
      2 2
      (parameterRamificationSection
        (K := K) alignedSmithRamificationIndex f.leftSection)
      f.oneStepSmith_leftSectionDivisibility i
  let e := smithConformalSourceExponent 2 2 i
  have heq :
      Polynomial.X ^ e * q = Polynomial.X ^ e * 0 := by
    rw [hram_i] at hreinflate
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient,
      zeroPolynomialSection, e, q] using hreinflate
  have hcancel :=
    polynomial_X_pow_mul_cancel
      (K := K) e heq
  simpa [q, zeroPolynomialSection] using hcancel

/-- On a zero-left departure frontier, the exposure left section is exactly
zero. -/
theorem CanonicalZeroLeftSmithDepartureFrontier.exposureLeftSection_eq_zero
    [CharZero K]
    {D complexity : ℕ}
    (Z : CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity) :
    Z.frontier.defectSmithExposureLeftSection =
      zeroPolynomialSection (K := K) := by
  exact
    Z.frontier.lossless.defectSmithExposureLeftSection_eq_zero
      Z.leftSection_eq_zero

/-- Hence the exact rigid source recentering is definitionally an identity
up to the retained zero-left equality. -/
theorem CanonicalZeroLeftSmithDepartureFrontier.recenteredFamily_eq_exposure
    [CharZero K]
    {D complexity : ℕ}
    (Z : CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity)
    (S : Z.frontier.RigidClosingExactCollisionSourceData) :
    S.recenteredFamily = Z.frontier.defectSmithExposureFamily := by
  unfold CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData.recenteredFamily
  have hleft :
      Z.frontier.defectSmithExposureLeftSection =
        zeroPolynomialSection (K := K) :=
    Z.exposureLeftSection_eq_zero
  rw [hleft]
  exact polynomialFamilyTranslationHom_zeroPolynomialSection _

/-- The nominally recentered rigid source therefore retains ordinary degree
`D` homogeneity whenever it comes from the globally reached zero-left
frontier. -/
theorem CanonicalZeroLeftSmithDepartureFrontier.recenteredFamily_isHomogeneous
    [CharZero K]
    {D complexity : ℕ}
    (Z : CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity)
    (S : Z.frontier.RigidClosingExactCollisionSourceData) :
    S.recenteredFamily.IsHomogeneous D := by
  rw [Z.recenteredFamily_eq_exposure S]
  exact Z.frontier.defectSmithExposure_isHomogeneous

/-- The packaged recentered source family itself is homogeneous on a
zero-left frontier. -/
theorem CanonicalZeroLeftSmithDepartureFrontier.recenteredSourceFamily_isHomogeneous
    [CharZero K]
    {D complexity : ℕ}
    (Z : CanonicalZeroLeftSmithDepartureFrontier
      (K := K) D complexity)
    (S : Z.frontier.RigidClosingRecenteredSourceData) :
    S.family.IsHomogeneous D := by
  rw [S.family_eq_recentered]
  exact Z.recenteredFamily_isHomogeneous S.original

end

end HC4.Valuation
