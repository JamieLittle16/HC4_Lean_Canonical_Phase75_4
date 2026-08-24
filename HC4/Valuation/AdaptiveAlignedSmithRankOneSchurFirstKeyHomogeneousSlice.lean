import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurXeLmRigidity
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# Ordinary-homogeneous slice of the first transverse Schur source key

Stage 4B1 exposes the least positive transverse source component

    Q = in_{-m}(F₀),    m > 0,

for the honest special fibre.  Its weight is

    wt(x₀) = 0,  wt(x₁)=wt(x₂)=wt(x₃)=-1,

so every monomial of `Q` has *exact* total transverse degree `m`.

The next source-to-Schur argument needs an ordinary-homogeneous key, but this
should not be reconstructed by hand.  The Newton library already contains the
canonical ordinary-degree refinement
`smithSubfaceDegreeComponent`.  In this file we apply that existing
construction to the full projected support of `Q` and choose any nonzero
ordinary degree component.

The resulting slice `R` is nonzero and satisfies simultaneously

* ordinary homogeneity of degree `D`;
* exact total transverse degree `m`;
* hence a fixed longitudinal exponent `D - m` on every supported monomial.

Thus, support-theoretically,

    R = x₀^(D-m) H_m(x₁,x₂,x₃),

with `H_m` a nonzero transverse homogeneous form of degree `m`.

No Hessian classification is reproved here.  This is only the canonical
source grading needed before applying the already-existing rank-one
homogeneous packet machinery to an active binary slice.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero ordinary-homogeneous slice of an exact first transverse key.

The `slice_eq` field records that this is literally the existing canonical
Smith-subface degree component, not a newly reconstructed polynomial. -/
structure FirstTransverseKeyHomogeneousSliceData
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ) where
  ordinaryDegree : ℕ
  slice : MvPolynomial (Fin 4) K
  slice_eq :
    slice =
      smithSubfaceDegreeComponent
        (smithProjectedSupport (1 : Fin 4) 2 3 Q)
        Q ordinaryDegree
  slice_ne_zero : slice ≠ 0
  slice_homogeneous : slice.IsHomogeneous ordinaryDegree
  key_exactTransverseDegree :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d Q ≠ 0 →
        pureLongitudinalTransverseDegree d = m
  slice_source :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d slice ≠ 0 →
        MvPolynomial.coeff d Q ≠ 0 ∧
          HC4.Polynomial.ordinaryDegree4 d = ordinaryDegree
  slice_exactTransverseDegree :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d slice ≠ 0 →
        pureLongitudinalTransverseDegree d = m
  slice_longitudinalExponent :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d slice ≠ 0 →
        d (0 : Fin 4) = ordinaryDegree - m

/-- Weighted homogeneity of weight `-m` for the canonical transverse weight
is exactly total transverse degree `m`. -/
theorem exactTransverseDegree_of_pureLongitudinalWeightedHomogeneous
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ))) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d Q ≠ 0 →
        pureLongitudinalTransverseDegree d = m := by
  intro d hd
  have hw := hhom hd
  rw [weight_pureLongitudinalTransverseWeight] at hw
  omega

/-- **Canonical homogeneous slice of an exact first transverse key.**

A nonzero exact transverse key always has a nonzero ordinary-degree component
on its full Smith projected support.  The component is built with the
existing `smithSubfaceDegreeComponent`; the only new observation is that the
transverse weight and ordinary degree together force the longitudinal
exponent to be `D-m`. -/
theorem exists_firstTransverseKeyHomogeneousSlice
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hQne : Q ≠ 0)
    (hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ))) :
    Nonempty (FirstTransverseKeyHomogeneousSliceData Q m) := by
  classical

  have hQexact :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d Q ≠ 0 →
          pureLongitudinalTransverseDegree d = m :=
    exactTransverseDegree_of_pureLongitudinalWeightedHomogeneous Q m hQhom

  rcases MvPolynomial.support_nonempty.mpr hQne with ⟨d, hdQ⟩
  let D := HC4.Polynomial.ordinaryDegree4 d
  let T := smithProjectedSupport (1 : Fin 4) 2 3 Q
  let R := smithSubfaceDegreeComponent T Q D

  have hdcoeff : MvPolynomial.coeff d Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdQ

  have heT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T := by
    dsimp [T]
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hdQ, rfl⟩

  have hRne : R ≠ 0 := by
    have h := smithSubfaceDegreeComponent_ne_zero_of_mem
      T Q d hdQ heT
    simpa [R, D] using h

  have hRhom : R.IsHomogeneous D := by
    simpa [R] using smithSubfaceDegreeComponent_isHomogeneous T Q D

  have hRsource :
      ∀ q : Fin 4 →₀ ℕ,
        MvPolynomial.coeff q R ≠ 0 →
          MvPolynomial.coeff q Q ≠ 0 ∧
            HC4.Polynomial.ordinaryDegree4 q = D := by
    intro q hq
    have hq' := hq
    change MvPolynomial.coeff q (smithSubfaceDegreeComponent T Q D) ≠ 0 at hq'
    rw [coeff_smithSubfaceDegreeComponent] at hq'
    by_cases hcond :
        smithSupportExponentOf (1 : Fin 4) 2 3 q ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 q = D
    · rw [if_pos hcond] at hq'
      exact ⟨hq', hcond.2⟩
    · rw [if_neg hcond] at hq'
      exact False.elim (hq' rfl)

  have hRexact :
      ∀ q : Fin 4 →₀ ℕ,
        MvPolynomial.coeff q R ≠ 0 →
          pureLongitudinalTransverseDegree q = m := by
    intro q hq
    exact hQexact q (hRsource q hq).1

  have hRlong :
      ∀ q : Fin 4 →₀ ℕ,
        MvPolynomial.coeff q R ≠ 0 →
          q (0 : Fin 4) = D - m := by
    intro q hq
    have hdegree := (hRsource q hq).2
    have htrans := hRexact q hq
    unfold HC4.Polynomial.ordinaryDegree4 at hdegree
    unfold pureLongitudinalTransverseDegree at htrans
    omega

  exact ⟨{
    ordinaryDegree := D
    slice := R
    slice_eq := by rfl
    slice_ne_zero := hRne
    slice_homogeneous := hRhom
    key_exactTransverseDegree := hQexact
    slice_source := hRsource
    slice_exactTransverseDegree := hRexact
    slice_longitudinalExponent := hRlong
  }⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing form: every Stage-4B1 first source key has a canonical
nonzero ordinary-homogeneous slice with exact transverse degree and fixed
longitudinal exponent. -/
theorem HasFirstTransverseSourceKey.exists_homogeneousSlice
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    ∃ hpos :
        (positiveTransverseSourceSupport
          (polynomialFamilySpecialFiber C.family)).Nonempty,
      let F₀ := polynomialFamilySpecialFiber C.family
      let m := firstPositiveTransverseSourceDegree F₀ hpos
      let Q :=
        HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) F₀
      Nonempty (FirstTransverseKeyHomogeneousSliceData Q m) := by
  rcases hkey with ⟨hpos, hmpos, hQne, hQhom, _hessian⟩
  refine ⟨hpos, ?_⟩
  dsimp only
  exact exists_firstTransverseKeyHomogeneousSlice
    (HC4.Polynomial.initialForm pureLongitudinalTransverseWeight
      (-(firstPositiveTransverseSourceDegree
        (polynomialFamilySpecialFiber C.family) hpos : ℤ))
      (polynomialFamilySpecialFiber C.family))
    (firstPositiveTransverseSourceDegree
      (polynomialFamilySpecialFiber C.family) hpos)
    hQne hQhom

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
