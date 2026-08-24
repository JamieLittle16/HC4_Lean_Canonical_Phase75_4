import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyBihomogeneousKernel
import Mathlib.Tactic

/-!
# Canonical longitudinal factorisation before the transverse Schur descent

Stage 4B9 descended the B8 first-key kernel to a maximal ordinary-homogeneous
source slice.  Stage 4B10 then proved the exact bihomogeneous support profile
of the *canonical* maximal vector

    U = ordinarySourceVectorLeading L.leadingVector L.leading_ne_zero.

There is one small provenance issue to keep explicit before cancelling the
longitudinal variable: the older B9 carrier record existentially stores a
vector and therefore forgets that its vector is literally this canonical
`U`.  This file retains the canonical vector in the homogeneous-kernel
package and then uses the existing `MvPolynomial.finSuccEquiv` representation

    MvPolynomial (Fin 4) K  ~=  Polynomial (MvPolynomial (Fin 3) K)

to turn fixed longitudinal support into an exact polynomial monomial factor.

For the maximal first-key slice we obtain exactly

    finSuccEquiv R = X^e * H,

where `e = D-m`.  For the canonical maximal kernel vector there are two
lossless alternatives:

* all three transverse coordinates vanish, in which case the longitudinal
  coordinate is nonzero;
* some transverse coordinate is nonzero, and there is one `lambda` such that

      finSuccEquiv U_0     = X^(lambda+1) * A,
      finSuccEquiv U_{j+1} = X^lambda     * B_j    (j=0,1,2).

This is the exact common longitudinal factor needed by the next stage.  No
new source classification, Hessian calculation, or Schur argument is added.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Generic fixed-longitudinal-support factorisation -/

/-- If every supported source monomial has the same exponent `n` in source
coordinate `0`, then `finSuccEquiv` is literally one outer polynomial
monomial `X^n` times its transverse coefficient. -/
theorem finSuccEquiv_eq_monomial_of_longitudinalExponent
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n) :
    MvPolynomial.finSuccEquiv K 3 F =
      Polynomial.monomial n
        ((MvPolynomial.finSuccEquiv K 3 F).coeff n) := by
  apply Polynomial.ext
  intro a
  by_cases ha : a = n
  · subst a
    simp
  · have hlhs : (MvPolynomial.finSuccEquiv K 3 F).coeff a = 0 := by
      apply MvPolynomial.ext
      intro t
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      have hz : MvPolynomial.coeff (t.cons a) F = 0 := by
        by_contra hne
        have hx := hlong (t.cons a) hne
        have hzero : (t.cons a) (0 : Fin 4) = a := by simp
        rw [hzero] at hx
        exact ha hx
      simpa using hz
    rw [hlhs]
    simp [Polynomial.coeff_monomial, ha, Ne.symm ha]

/-- The B3/B4 homogeneous first-key slice therefore has an exact outer
longitudinal monomial factor, not merely a support-theoretic one. -/
theorem FirstTransverseKeyHomogeneousSliceData.finSuccEquiv_eq_longitudinalMonomial
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m) :
    MvPolynomial.finSuccEquiv K 3 S.slice =
      Polynomial.monomial (S.ordinaryDegree - m)
        ((MvPolynomial.finSuccEquiv K 3 S.slice).coeff
          (S.ordinaryDegree - m)) := by
  exact finSuccEquiv_eq_monomial_of_longitudinalExponent
    S.slice (S.ordinaryDegree - m) S.slice_longitudinalExponent

/-! ## Retain the canonical B9 vector instead of forgetting its provenance -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- B9 homogeneous source slice together with the kernel equation for the
literal canonical B10 vector attached to `L`. -/
structure FirstKeyCanonicalMaximalHomogeneousKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) where
  sliceData :
    FirstTransverseKeyMaximalHomogeneousSliceData
      (initialForm pureLongitudinalTransverseWeight
        (-(firstPositiveTransverseSourceDegree
          (polynomialFamilySpecialFiber C.family) L.hpos : ℤ))
        (polynomialFamilySpecialFiber C.family))
      (firstPositiveTransverseSourceDegree
        (polynomialFamilySpecialFiber C.family) L.hpos)
  transverseKernel :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian sliceData.sliceData.slice).mulVec
        L.maximalHomogeneousVector i.succ = 0

/-- The existing B9 maximal-degree descent already constructs the canonical
vector; this theorem simply retains that equality in the carrier API. -/
theorem FirstKeyLeadingTransverseKernelData.exists_canonicalMaximalHomogeneousKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    Nonempty (C.FirstKeyCanonicalMaximalHomogeneousKernelData L) := by
  let F₀ := polynomialFamilySpecialFiber C.family
  let m := firstPositiveTransverseSourceDegree F₀ L.hpos
  let Q := initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) F₀

  have hQne : Q ≠ 0 := by
    dsimp [Q, m, F₀]
    exact firstPositiveTransverseInitialForm_ne_zero
      (polynomialFamilySpecialFiber C.family) L.hpos

  have hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)) := by
    dsimp [Q]
    exact initialForm_isWeightedHomogeneous
      pureLongitudinalTransverseWeight (-(m : ℤ)) F₀

  have hker :
      ∀ i : Fin 3,
        (HC4.Polynomial.hessian Q).mulVec L.leadingVector i.succ = 0 := by
    simpa [Q, m, F₀] using L.transverseKernel

  rcases exists_maximalHomogeneousSlice_transverseKernel
      Q m hQne hQhom L.leadingVector L.leading_ne_zero hker with
    ⟨S, _hUne, hUker⟩

  exact ⟨{
    sliceData := by simpa [Q, m, F₀] using S
    transverseKernel := by
      intro i
      simpa [FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector]
        using hUker i
  }⟩

/-- Exact longitudinal factorisation of the canonical maximal source slice. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.slice_finSuccEquiv_eq_monomial
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice =
      Polynomial.monomial
        (D.sliceData.sliceData.ordinaryDegree -
          firstPositiveTransverseSourceDegree
            (polynomialFamilySpecialFiber C.family) L.hpos)
        ((MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice).coeff
          (D.sliceData.sliceData.ordinaryDegree -
            firstPositiveTransverseSourceDegree
              (polynomialFamilySpecialFiber C.family) L.hpos)) := by
  exact D.sliceData.sliceData.finSuccEquiv_eq_longitudinalMonomial

/-! ## Exact longitudinal factorisation of the canonical kernel vector -/

/-- Some transverse coordinate of the canonical maximal vector survives. -/
def FirstKeyLeadingTransverseKernelData.HasNonzeroTransverseMaximalCoordinate
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) : Prop :=
  ∃ j : Fin 3, L.maximalHomogeneousVector j.succ ≠ 0

/-- In the complementary branch, nonzeroness of the complete vector forces
its longitudinal coordinate to survive. -/
theorem FirstKeyLeadingTransverseKernelData.zeroCoordinate_ne_zero_of_transverse_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (hzero : ∀ j : Fin 3, L.maximalHomogeneousVector j.succ = 0) :
    L.maximalHomogeneousVector (0 : Fin 4) ≠ 0 := by
  intro h0
  apply L.maximalHomogeneousVector_ne_zero
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hzero j

/-- Exact outer-polynomial factor profile of the canonical maximal vector in
the branch where a transverse coordinate survives. -/
structure FirstKeyMaximalVectorLongitudinalFactorData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) where
  exponent : ℕ
  transverse_nonzero : L.HasNonzeroTransverseMaximalCoordinate
  transverseFactor :
    ∀ j : Fin 3,
      MvPolynomial.finSuccEquiv K 3 (L.maximalHomogeneousVector j.succ) =
        Polynomial.monomial exponent
          ((MvPolynomial.finSuccEquiv K 3
            (L.maximalHomogeneousVector j.succ)).coeff exponent)
  longitudinalFactor :
    MvPolynomial.finSuccEquiv K 3
        (L.maximalHomogeneousVector (0 : Fin 4)) =
      Polynomial.monomial (exponent + 1)
        ((MvPolynomial.finSuccEquiv K 3
          (L.maximalHomogeneousVector (0 : Fin 4))).coeff (exponent + 1))

/-- B10's support equalities upgrade to literal common monomial factors under
`finSuccEquiv`. -/
theorem FirstKeyLeadingTransverseKernelData.exists_longitudinalFactorData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (htrans : L.HasNonzeroTransverseMaximalCoordinate) :
    Nonempty (C.FirstKeyMaximalVectorLongitudinalFactorData L) := by
  rcases htrans with ⟨j, hj⟩
  rcases MvPolynomial.support_nonempty.mpr hj with ⟨d, hdmem⟩
  have hd : MvPolynomial.coeff d (L.maximalHomogeneousVector j.succ) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdmem
  let lambda := d (0 : Fin 4)

  have htransFactor :
      ∀ k : Fin 3,
        MvPolynomial.finSuccEquiv K 3 (L.maximalHomogeneousVector k.succ) =
          Polynomial.monomial lambda
            ((MvPolynomial.finSuccEquiv K 3
              (L.maximalHomogeneousVector k.succ)).coeff lambda) := by
    intro k
    apply finSuccEquiv_eq_monomial_of_longitudinalExponent
    intro e he
    have hexp :=
      L.maximalHomogeneousVector_transverse_longitudinalExponent_eq
        k j e d he hd
    simpa [lambda] using hexp

  have hzeroFactor :
      MvPolynomial.finSuccEquiv K 3
          (L.maximalHomogeneousVector (0 : Fin 4)) =
        Polynomial.monomial (lambda + 1)
          ((MvPolynomial.finSuccEquiv K 3
            (L.maximalHomogeneousVector (0 : Fin 4))).coeff (lambda + 1)) := by
    apply finSuccEquiv_eq_monomial_of_longitudinalExponent
    intro e he
    have hexp :=
      L.maximalHomogeneousVector_zero_longitudinalExponent_eq_succ
        j e d he hd
    simpa [lambda] using hexp

  exact ⟨{
    exponent := lambda
    transverse_nonzero := ⟨j, hj⟩
    transverseFactor := htransFactor
    longitudinalFactor := hzeroFactor
  }⟩

/-- Lossless branch split for the canonical maximal vector: either it is
purely longitudinal, or every coordinate has the exact common longitudinal
factor profile needed for cancellation. -/
theorem FirstKeyLeadingTransverseKernelData.transverse_zero_or_longitudinalFactorData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    (∀ j : Fin 3, L.maximalHomogeneousVector j.succ = 0) ∨
      Nonempty (C.FirstKeyMaximalVectorLongitudinalFactorData L) := by
  classical
  by_cases hzero : ∀ j : Fin 3, L.maximalHomogeneousVector j.succ = 0
  · exact Or.inl hzero
  · right
    apply L.exists_longitudinalFactorData
    unfold FirstKeyLeadingTransverseKernelData.HasNonzeroTransverseMaximalCoordinate
    push_neg at hzero
    exact hzero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
