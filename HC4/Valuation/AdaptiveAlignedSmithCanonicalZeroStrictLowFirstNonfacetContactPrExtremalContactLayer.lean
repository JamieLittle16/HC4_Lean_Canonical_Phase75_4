import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalOrders
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLayerGrading
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# A19.R18.29--31: exact honest-contact layers of the two exposed PR slices

The qNN/qNM coefficient calculation should not manipulate coefficient-ring
parameter derivatives and transverse source grading at the same time.  The
honest contact Rees already separates them exactly.

For longitudinal index `n`, contact parameter order `q`, and transverse degree
`t` satisfying

    q + profileWeight * n + t = D,

the longitudinal coefficient of the exact contact parameter layer `q` is
literally the transverse weight-`t` component of the raw longitudinal profile
coefficient.  This file records that dictionary once and specializes it to the
leading and next-highest slices retained by `prExtremalDegreeData`.

R18.30 records the corresponding dictionary after applying the first and
falling second parameter-Euler operators.  R18.31 records the spatial
longitudinal Euler companion: exact parameter-layer extraction commutes with
`x₀∂₀`, and after longitudinal coefficient extraction that operator is simply
multiplication by the retained longitudinal index.

Thus the remaining extremal coefficient calculation can replace every
parameter/source Euler occurrence by its literal finite scalar before doing
any Schur or residual algebra.

No determinant, Schur identity, pivot cancellation, or terminal vanishing is
used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- Exact parameter layer `q` of the honest contact family, followed by the
longitudinal coefficient `n`.  The result retains only the three transverse
source variables. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (familyParameterLayer P.contactFamily q)).coeff n

/-- **R18.29 exact contact-layer dictionary.**  At a fixed honest contact
grade, parameter-layer extraction and longitudinal coefficient extraction leave
exactly the matching transverse homogeneous component of the raw profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer_eq_initialForm
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n t : ℕ)
    (hgrade : q + P.profileWeight * n + t = T.topFace.degree) :
    R.contactLongitudinalParameterLayer q n =
      HC4.Polynomial.initialForm
        qsContactTransverseIntegerWeight (t : ℤ) (R.profile.coeff n) := by
  classical
  apply MvPolynomial.ext
  intro m
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [P.contactFamily_longitudinal_transverse_coeff q n m]
  rw [← R.profile_eq]
  rw [HC4.Polynomial.coeff_initialForm,
    weight_qsContactTransverseIntegerWeight]
  by_cases hm : MvPolynomial.coeff m (R.profile.coeff n) = 0
  · split <;> simp [hm]
  · have hmne : MvPolynomial.coeff m (R.profile.coeff n) ≠ 0 := hm
    have hmSupport : m ∈ (R.profile.coeff n).support :=
      MvPolynomial.mem_support_iff.mpr hmne
    have hsourceCoeff := hmne
    rw [R.profile_eq, qsContactRawLongitudinalProfile,
      MvPolynomial.finSuccEquiv_coeff_coeff] at hsourceCoeff
    have hsource :
        m.cons n ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support :=
      MvPolynomial.mem_support_iff.mpr hsourceCoeff
    have hbound := R.transverseDegree_add_profileWeight_mul_le hmSupport
    by_cases hmt : qsContactTransverseDegree m = t
    · have hweight :
          (qsContactTransverseDegree m : ℤ) = (t : ℤ) := by
        exact_mod_cast hmt
      have hq :
          T.topFace.degree -
              (qsContactTransverseDegree m + P.profileWeight * n) = q := by
        rw [hmt]
        omega
      rw [if_pos ⟨hsource, hq⟩, if_pos hweight]
    · have hweight :
          (qsContactTransverseDegree m : ℤ) ≠ (t : ℤ) := by
        exact_mod_cast hmt
      have hqne :
          T.topFace.degree -
              (qsContactTransverseDegree m + P.profileWeight * n) ≠ q := by
        intro hq
        omega
      rw [if_neg, if_neg hweight]
      intro hcond
      exact hqne hcond.2

/-- **R18.30 first parameter-Euler dictionary.**  Longitudinal extraction
commutes with taking an exact contact parameter layer, and `τ∂τ` acts on that
layer by the literal scalar `q`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterEulerLayer_eq
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterEuler P.contactFamily) q)).coeff n =
      MvPolynomial.C (q : K) * R.contactLongitudinalParameterLayer q n := by
  rw [familyParameterLayer_familyParameterEuler]
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  simpa [mul_comm]

/-- **R18.30 falling second parameter-Euler dictionary.**  The same exact
contact layer sees `τ²∂τ²` as the literal falling scalar `q(q-1)`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterSecondEulerLayer_eq
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterSecondEuler P.contactFamily) q)).coeff n =
      MvPolynomial.C (q : K) * (MvPolynomial.C (q : K) - 1) *
        R.contactLongitudinalParameterLayer q n := by
  rw [familyParameterLayer_familyParameterSecondEuler]
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  change
    MvPolynomial.coeff (m.cons n)
        (MvPolynomial.C (q : K) * (MvPolynomial.C (q : K) - 1) *
          familyParameterLayer P.contactFamily q) =
      MvPolynomial.coeff m
        (MvPolynomial.C (q : K) * (MvPolynomial.C (q : K) - 1) *
          (MvPolynomial.finSuccEquiv K 3
            (familyParameterLayer P.contactFamily q)).coeff n)
  have hscalar4 :
      (MvPolynomial.C (q : K) * (MvPolynomial.C (q : K) - 1) :
          MvPolynomial (Fin 4) K) =
        MvPolynomial.C ((q : K) * ((q : K) - 1)) := by
    rw [map_mul, map_sub, map_one]
  have hscalar3 :
      (MvPolynomial.C (q : K) * (MvPolynomial.C (q : K) - 1) :
          MvPolynomial (Fin 3) K) =
        MvPolynomial.C ((q : K) * ((q : K) - 1)) := by
    rw [map_mul, map_sub, map_one]
  rw [hscalar4, hscalar3]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]

/-- **R18.31 spatial Euler commutation.**  Exact coefficient-parameter layer
extraction commutes with every source Euler operator.  This is linear in the
family parameter; unlike a generic product-layer statement it introduces no
convolution clock. -/
theorem familyParameterLayer_mvEuler
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i : Fin 4) :
    familyParameterLayer (HC4.Polynomial.mvEuler i F) q =
      HC4.Polynomial.mvEuler i (familyParameterLayer F q) := by
  apply MvPolynomial.ext
  intro d
  simp only [familyParameterLayer_coeff, coeff_mvEuler]
  have h := Polynomial.coeff_mul_natCast
    (R := K) (p := MvPolynomial.coeff d F) (a := d i) (k := q)
  simpa [mul_comm] using h

/-- **R18.31 longitudinal source-Euler dictionary.**  After exact parameter
layer extraction, `x₀∂₀` acts on longitudinal coefficient `n` by the scalar
`n`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSourceEulerLayer_eq
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) q)).coeff n =
      MvPolynomial.C (n : K) * R.contactLongitudinalParameterLayer q n := by
  rw [familyParameterLayer_mvEuler]
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [coeff_mvEuler]
  simp

/-- The first exposed contact layer is literally the retained nonzero leading
transverse slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    R.contactLongitudinalParameterLayer E.qN E.next.N = E.leading.slice := by
  calc
    R.contactLongitudinalParameterLayer E.qN E.next.N =
        HC4.Polynomial.initialForm
          qsContactTransverseIntegerWeight
          (E.leading.transverseDegree : ℤ)
          (R.profile.coeff E.next.N) :=
      R.contactLongitudinalParameterLayer_eq_initialForm
        E.qN E.next.N E.leading.transverseDegree E.leading_grade
    _ = E.leading.slice := by
      rw [E.next.N_eq]
      exact E.leading.slice_eq.symm

/-- The second exposed contact layer is literally the retained nonzero
next-highest transverse slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactNextParameterLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    R.contactLongitudinalParameterLayer E.qM E.next.M = E.next.slice := by
  calc
    R.contactLongitudinalParameterLayer E.qM E.next.M =
        HC4.Polynomial.initialForm
          qsContactTransverseIntegerWeight
          (E.next.transverseDegree : ℤ)
          (R.profile.coeff E.next.M) :=
      R.contactLongitudinalParameterLayer_eq_initialForm
        E.qM E.next.M E.next.transverseDegree E.next_grade
    _ = E.next.slice := E.next.slice_eq.symm

/-- On the leading exposed source slice, the first parameter Euler is exactly
multiplication by the retained contact deficit `qN`. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterEuler P.contactFamily) E.qN)).coeff
        E.next.N =
      MvPolynomial.C (E.qN : K) * E.leading.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterEuler P.contactFamily) E.qN)).coeff
        E.next.N =
        MvPolynomial.C (E.qN : K) *
          R.contactLongitudinalParameterLayer E.qN E.next.N :=
      R.contactLongitudinalParameterEulerLayer_eq E.qN E.next.N
    _ = MvPolynomial.C (E.qN : K) * E.leading.slice := by
      rw [E.contactLeadingParameterLayer_eq]

/-- On the leading exposed source slice, the falling second parameter Euler is
exactly multiplication by `qN(qN-1)`. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterSecondEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterSecondEuler P.contactFamily) E.qN)).coeff
        E.next.N =
      MvPolynomial.C (E.qN : K) * (MvPolynomial.C (E.qN : K) - 1) *
        E.leading.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterSecondEuler P.contactFamily) E.qN)).coeff
        E.next.N =
        MvPolynomial.C (E.qN : K) * (MvPolynomial.C (E.qN : K) - 1) *
          R.contactLongitudinalParameterLayer E.qN E.next.N :=
      R.contactLongitudinalParameterSecondEulerLayer_eq E.qN E.next.N
    _ = MvPolynomial.C (E.qN : K) * (MvPolynomial.C (E.qN : K) - 1) *
        E.leading.slice := by
      rw [E.contactLeadingParameterLayer_eq]

/-- The corresponding first parameter-Euler formula on the next-highest
exposed slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactNextParameterEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterEuler P.contactFamily) E.qM)).coeff
        E.next.M =
      MvPolynomial.C (E.qM : K) * E.next.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterEuler P.contactFamily) E.qM)).coeff
        E.next.M =
        MvPolynomial.C (E.qM : K) *
          R.contactLongitudinalParameterLayer E.qM E.next.M :=
      R.contactLongitudinalParameterEulerLayer_eq E.qM E.next.M
    _ = MvPolynomial.C (E.qM : K) * E.next.slice := by
      rw [E.contactNextParameterLayer_eq]

/-- The corresponding falling second parameter-Euler formula on the
next-highest exposed slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactNextParameterSecondEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterSecondEuler P.contactFamily) E.qM)).coeff
        E.next.M =
      MvPolynomial.C (E.qM : K) * (MvPolynomial.C (E.qM : K) - 1) *
        E.next.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer (familyParameterSecondEuler P.contactFamily) E.qM)).coeff
        E.next.M =
        MvPolynomial.C (E.qM : K) * (MvPolynomial.C (E.qM : K) - 1) *
          R.contactLongitudinalParameterLayer E.qM E.next.M :=
      R.contactLongitudinalParameterSecondEulerLayer_eq E.qM E.next.M
    _ = MvPolynomial.C (E.qM : K) * (MvPolynomial.C (E.qM : K) - 1) *
        E.next.slice := by
      rw [E.contactNextParameterLayer_eq]

/-- On the leading exposed slice, the longitudinal source Euler contributes the
literal leading index `N`. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingSourceEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qN)).coeff
        E.next.N =
      MvPolynomial.C (E.next.N : K) * E.leading.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qN)).coeff
        E.next.N =
        MvPolynomial.C (E.next.N : K) *
          R.contactLongitudinalParameterLayer E.qN E.next.N :=
      R.contactLongitudinalSourceEulerLayer_eq E.qN E.next.N
    _ = MvPolynomial.C (E.next.N : K) * E.leading.slice := by
      rw [E.contactLeadingParameterLayer_eq]

/-- On the next exposed slice, the longitudinal source Euler contributes the
literal next index `M`. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactNextSourceEulerLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qM)).coeff
        E.next.M =
      MvPolynomial.C (E.next.M : K) * E.next.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qM)).coeff
        E.next.M =
        MvPolynomial.C (E.next.M : K) *
          R.contactLongitudinalParameterLayer E.qM E.next.M :=
      R.contactLongitudinalSourceEulerLayer_eq E.qM E.next.M
    _ = MvPolynomial.C (E.next.M : K) * E.next.slice := by
      rw [E.contactNextParameterLayer_eq]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
