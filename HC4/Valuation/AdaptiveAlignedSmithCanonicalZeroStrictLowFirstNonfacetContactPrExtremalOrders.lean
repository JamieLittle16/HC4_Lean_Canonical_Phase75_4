import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalSlices
import Mathlib.Tactic

/-!
# A19.R18.26--28: exact parameter orders and scalar consequences of the two exposed PR pairs

The contact and binary filtrations are deliberately not identified.  For the
two extremal longitudinal pairs we only need their exact arithmetic relation.
If the leading slice has contact deficit `qN` and transverse degree `t`, then

    qNN = 2D - r(2N) = qN + qN + t + t.

For the leading/next pair, with next deficit `qM` and transverse degree `u`,

    qNM = 2D - r(N+M) = qN + qM + t + u.

These are consequences only of the two honest contact grading equations
retained by `QsOtherFacetContactPrExtremalDegreeData`.  They are the exact
bookkeeping needed by the coefficientwise transverse-inflation transport.

The same finite package is also the natural owner for the two scalar
consequences: a zero leading self scalar forces `t = 0`; after that, a zero
leading/next cross scalar forces `u ≤ 1`.  R18.28 additionally records the
precise nonzero-slice cancellation needed by the forthcoming coefficient
calculation: if the scalar times the retained nonzero slice product vanishes,
then the scalar itself vanishes and the R18.27 degree collapse applies.
No geometric vanishing is assumed in these wrappers.
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
variable {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}

/-- **R18.26 leading-pair order.** -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNN_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.N) =
      E.qN + E.qN +
        E.leading.transverseDegree + E.leading.transverseDegree := by
  have h := E.leading_grade
  rw [Nat.mul_add]
  omega

/-- **R18.26 leading/next-pair order.** -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNM_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.M) =
      E.qN + E.qM +
        E.leading.transverseDegree + E.next.transverseDegree := by
  have hN := E.leading_grade
  have hM := E.next_grade
  rw [Nat.mul_add]
  omega

/-- The binary active-pivot order is the leading contact-pair order plus the
four transverse powers contributed by the active two-by-two Hessian pivot. -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNN_add_four_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.N)) + 4 =
      E.qN + E.qN +
        (E.leading.transverseDegree + E.leading.transverseDegree + 4) := by
  rw [E.qNN_eq_contact_pair]
  omega

/-- Likewise for the leading/next pair. -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNM_add_four_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.M)) + 4 =
      E.qN + E.qM +
        (E.leading.transverseDegree + E.next.transverseDegree + 4) := by
  rw [E.qNM_eq_contact_pair]
  omega

/-- **R18.27 leading scalar consequence.**  The leading longitudinal index is
positive, so a zero PR self scalar forces the maximal transverse degree to be
zero. -/
theorem QsOtherFacetContactPrExtremalDegreeData.leading_transverseDegree_eq_zero_of_selfScalar
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hzero :
      - (E.next.N : K) * (E.leading.transverseDegree : K) *
          ((E.next.N : K) + (E.leading.transverseDegree : K) - 1) = 0) :
    E.leading.transverseDegree = 0 := by
  apply prContactWeightedEuler_selfDegreeScalar_eq_zero_forces_transverse_zero
    (K := K) E.next.N E.leading.transverseDegree
  · omega
  · exact hzero

/-- **R18.27 next scalar consequence.**  After the leading slice is pure
longitudinal, a zero PR cross scalar leaves only transverse degrees zero and
one; equivalently the maximal next transverse degree is at most one. -/
theorem QsOtherFacetContactPrExtremalDegreeData.next_transverseDegree_le_one_of_crossScalar
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hzero :
      (E.next.N : K) * (E.next.transverseDegree : K) *
          ((E.next.N : K) - 1) *
          ((E.next.transverseDegree : K) - 1) = 0) :
    E.next.transverseDegree ≤ 1 := by
  rcases
      prContactWeightedEuler_crossDegreeScalar_eq_zero_forces_transverse_zero_or_one
        (K := K) E.next.N E.next.transverseDegree E.N_two_le hzero with
    h0 | h1
  · omega
  · omega

/-- **R18.28 leading slice cancellation.**  The maximal leading transverse
slice is nonzero, so vanishing of the self scalar times its square already
forces the scalar to vanish.  This is the exact form produced by the leading
`qNN` coefficient calculation. -/
theorem QsOtherFacetContactPrExtremalDegreeData.leading_transverseDegree_eq_zero_of_selfSlice
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hzero :
      MvPolynomial.C
          (- (E.next.N : K) * (E.leading.transverseDegree : K) *
            ((E.next.N : K) + (E.leading.transverseDegree : K) - 1)) *
        E.leading.slice * E.leading.slice = 0) :
    E.leading.transverseDegree = 0 := by
  let a : K :=
    - (E.next.N : K) * (E.leading.transverseDegree : K) *
      ((E.next.N : K) + (E.leading.transverseDegree : K) - 1)
  have haC : (MvPolynomial.C a : MvPolynomial (Fin 3) K) = 0 := by
    by_contra hne
    have hprod :
        (MvPolynomial.C a : MvPolynomial (Fin 3) K) *
            E.leading.slice * E.leading.slice ≠ 0 :=
      mul_ne_zero (mul_ne_zero hne E.leading.slice_ne_zero)
        E.leading.slice_ne_zero
    exact hprod (by simpa [a] using hzero)
  have ha : a = 0 := by
    apply MvPolynomial.C_injective (Fin 3) K
    simpa using haC
  apply E.leading_transverseDegree_eq_zero_of_selfScalar
  simpa [a] using ha

/-- **R18.28 leading/next slice cancellation.**  Once the leading slice has
been forced pure longitudinal, both retained extremal slices are nonzero.
Thus a zero cross scalar times their product forces exactly the scalar equation
consumed by R18.27, and hence the entire next longitudinal coefficient has
maximal transverse degree at most one. -/
theorem QsOtherFacetContactPrExtremalDegreeData.next_transverseDegree_le_one_of_crossSlice
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hzero :
      MvPolynomial.C
          ((E.next.N : K) * (E.next.transverseDegree : K) *
            ((E.next.N : K) - 1) *
            ((E.next.transverseDegree : K) - 1)) *
        E.leading.slice * E.next.slice = 0) :
    E.next.transverseDegree ≤ 1 := by
  let a : K :=
    (E.next.N : K) * (E.next.transverseDegree : K) *
      ((E.next.N : K) - 1) * ((E.next.transverseDegree : K) - 1)
  have haC : (MvPolynomial.C a : MvPolynomial (Fin 3) K) = 0 := by
    by_contra hne
    have hprod :
        (MvPolynomial.C a : MvPolynomial (Fin 3) K) *
            E.leading.slice * E.next.slice ≠ 0 :=
      mul_ne_zero (mul_ne_zero hne E.leading.slice_ne_zero)
        E.next.slice_ne_zero
    exact hprod (by simpa [a] using hzero)
  have ha : a = 0 := by
    apply MvPolynomial.C_injective (Fin 3) K
    simpa using haC
  apply E.next_transverseDegree_le_one_of_crossScalar
  simpa [a] using ha

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
