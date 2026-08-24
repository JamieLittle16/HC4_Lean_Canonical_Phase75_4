import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLeadingKernel
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLongitudinalFactor
import Mathlib.Tactic

/-!
# Maximal ordinary-homogeneous kernel packet inside the first Schur source key

Stage 4B8 places a nonzero polynomial vector `V` in the three transverse
Hessian-kernel rows of the genuine first transverse source key `Q`.

To use the already-green homogeneous packet machinery, one must descend this
identity to one ordinary-homogeneous component of `Q`.  An arbitrary component
is not sufficient: products with neighbouring ordinary degrees could cancel.
The correct lossless choice is the maximal ordinary degree of `Q`, together
with the maximal ordinary degree occurring in the polynomial vector `V`.

Because Hessian formation lowers ordinary degree by exactly two, the maximal
ordinary component of every product

    Hess(Q)_{ij} * V_j

is then

    Hess(R)_{ij} * U_j,

where `R` is the maximal ordinary-homogeneous component of `Q` and `U` is the
maximal ordinary-homogeneous component of `V`.  Taking that exact component in
the B8 kernel identity gives

    (Hess R * U)_i = 0,    i = 1,2,3,

and `U != 0`.

The maximal component `R` is built with the *existing*
`smithSubfaceDegreeComponent` construction on the full projected support, so
it is simultaneously a `FirstTransverseKeyHomogeneousSliceData`.  Hence all
Stage-4B4 longitudinal-factor results apply immediately: coefficientwise,

    R = x0^(D-m) * H_m(x1,x2,x3).

No new homogeneous decomposition, Hessian differentiation, or longitudinal
factorisation is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Full projected support really is the whole polynomial -/

/-- Restricting a polynomial to the Smith projection of its own support does
nothing.  This tiny identity lets us invoke the existing maximal Smith-subface
component theorem without introducing a second ordinary-degree decomposition. -/
theorem smithSubfacePolynomial_fullProjectedSupport_eq
    (Q : MvPolynomial (Fin 4) K) :
    smithSubfacePolynomial (1 : Fin 4) 2 3
        (smithProjectedSupport (1 : Fin 4) 2 3 Q) Q = Q := by
  classical
  ext d
  rw [coeff_smithSubfacePolynomial]
  by_cases hd : MvPolynomial.coeff d Q = 0
  · simp [hd]
  · have hds : d ∈ Q.support := MvPolynomial.mem_support_iff.mpr hd
    have hmem := smithSupportExponentOf_mem_projectedSupport Q d hds
    simp [hmem]

/-! ## Canonical maximal ordinary slice of an exact transverse key -/

/-- The Stage-4B3 homogeneous-slice package, strengthened only by the fact
that its ordinary degree is maximal on the whole first key. -/
structure FirstTransverseKeyMaximalHomogeneousSliceData
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ) where
  sliceData : FirstTransverseKeyHomogeneousSliceData Q m
  maximalDegree :
    ∀ d ∈ Q.support,
      HC4.Polynomial.ordinaryDegree4 d ≤ sliceData.ordinaryDegree
  slice_eq_topInitial :
    sliceData.slice =
      initialForm (fun _ : Fin 4 => (1 : ℤ))
        (sliceData.ordinaryDegree : ℤ) Q

/-- The already-existing maximal Smith-subface degree theorem supplies a
canonical extremal B3 slice on the full projected support. -/
theorem exists_firstTransverseKeyMaximalHomogeneousSlice
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hQne : Q ≠ 0)
    (hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ))) :
    Nonempty (FirstTransverseKeyMaximalHomogeneousSliceData Q m) := by
  classical
  let T := smithProjectedSupport (1 : Fin 4) 2 3 Q

  have hfull :
      smithSubfacePolynomial (1 : Fin 4) 2 3 T Q = Q := by
    simpa [T] using smithSubfacePolynomial_fullProjectedSupport_eq Q

  have hW :
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T Q).support.Nonempty := by
    rw [hfull]
    exact MvPolynomial.support_nonempty.mpr hQne

  rcases exists_maximalDegree_nonzero_smithSubfaceComponent T Q hW with
    ⟨D, hRne, hmaxW⟩

  let R := smithSubfaceDegreeComponent T Q D

  have hQexact :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d Q ≠ 0 →
          pureLongitudinalTransverseDegree d = m :=
    exactTransverseDegree_of_pureLongitudinalWeightedHomogeneous Q m hQhom

  have hRhom : R.IsHomogeneous D := by
    simpa [R] using smithSubfaceDegreeComponent_isHomogeneous T Q D

  have hRsource :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d R ≠ 0 →
          MvPolynomial.coeff d Q ≠ 0 ∧
            HC4.Polynomial.ordinaryDegree4 d = D := by
    intro d hd
    have hd' := hd
    change MvPolynomial.coeff d (smithSubfaceDegreeComponent T Q D) ≠ 0 at hd'
    rw [coeff_smithSubfaceDegreeComponent] at hd'
    by_cases hcond :
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D
    · rw [if_pos hcond] at hd'
      exact ⟨hd', hcond.2⟩
    · rw [if_neg hcond] at hd'
      exact False.elim (hd' rfl)

  have hRexact :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d R ≠ 0 →
          pureLongitudinalTransverseDegree d = m := by
    intro d hd
    exact hQexact d (hRsource d hd).1

  have hRlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d R ≠ 0 →
          d (0 : Fin 4) = D - m := by
    intro d hd
    have hdegree := (hRsource d hd).2
    have htrans := hRexact d hd
    unfold HC4.Polynomial.ordinaryDegree4 at hdegree
    unfold pureLongitudinalTransverseDegree at htrans
    omega

  let S : FirstTransverseKeyHomogeneousSliceData Q m := {
    ordinaryDegree := D
    slice := R
    slice_eq := by rfl
    slice_ne_zero := by simpa [R] using hRne
    slice_homogeneous := hRhom
    key_exactTransverseDegree := hQexact
    slice_source := hRsource
    slice_exactTransverseDegree := hRexact
    slice_longitudinalExponent := hRlong
  }

  have hmaxQ :
      ∀ d ∈ Q.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D := by
    intro d hd
    apply hmaxW d
    rw [hfull]
    exact hd

  have htop :
      R = initialForm (fun _ : Fin 4 => (1 : ℤ)) (D : ℤ) Q := by
    dsimp [R]
    unfold smithSubfaceDegreeComponent
    rw [hfull]

  exact ⟨{
    sliceData := S
    maximalDegree := by simpa [S] using hmaxQ
    slice_eq_topInitial := by simpa [S] using htop
  }⟩

/-! ## Maximal ordinary component of a polynomial vector -/

/-- Ordinary degrees occurring anywhere in a four-component polynomial
vector. -/
noncomputable def ordinarySourceVectorDegreeSupport
    (V : Fin 4 → MvPolynomial (Fin 4) K) : Finset ℕ := by
  classical
  exact
    (Finset.univ : Finset (Fin 4)).biUnion fun j =>
      (V j).support.image HC4.Polynomial.ordinaryDegree4

/-- A supported vector monomial contributes its ordinary degree to the common
finite degree support. -/
theorem ordinarySourceVectorDegree_mem
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ (V j).support) :
    HC4.Polynomial.ordinaryDegree4 d ∈
      ordinarySourceVectorDegreeSupport V := by
  classical
  unfold ordinarySourceVectorDegreeSupport
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- A nonzero polynomial vector has a nonempty ordinary-degree support. -/
theorem ordinarySourceVectorDegreeSupport_nonempty
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) :
    (ordinarySourceVectorDegreeSupport V).Nonempty := by
  have hj : ∃ j : Fin 4, V j ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hV
    funext j
    exact hnone j
  rcases hj with ⟨j, hj⟩
  rcases MvPolynomial.support_nonempty.mpr hj with ⟨d, hd⟩
  exact ⟨HC4.Polynomial.ordinaryDegree4 d,
    ordinarySourceVectorDegree_mem V j d hd⟩

/-- Maximal ordinary degree occurring in a nonzero polynomial vector. -/
noncomputable def ordinarySourceVectorTopDegree
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) : ℕ :=
  (ordinarySourceVectorDegreeSupport V).max'
    (ordinarySourceVectorDegreeSupport_nonempty V hV)

/-- The maximal vector degree is attained. -/
theorem ordinarySourceVectorTopDegree_mem
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) :
    ordinarySourceVectorTopDegree V hV ∈
      ordinarySourceVectorDegreeSupport V := by
  unfold ordinarySourceVectorTopDegree
  exact Finset.max'_mem _ (ordinarySourceVectorDegreeSupport_nonempty V hV)

/-- Every component is weakly bounded by the common maximal ordinary degree. -/
theorem ordinarySourceVector_component_isWeightLE
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0)
    (j : Fin 4) :
    IsWeightLE (fun _ : Fin 4 => (1 : ℤ))
      (ordinarySourceVectorTopDegree V hV : ℤ) (V j) := by
  intro d hd
  have hmem := ordinarySourceVectorDegree_mem V j d hd
  have hle :
      HC4.Polynomial.ordinaryDegree4 d ≤
        ordinarySourceVectorTopDegree V hV := by
    unfold ordinarySourceVectorTopDegree
    exact Finset.le_max' _ _ hmem
  rw [ordinaryIntegerWeight_eq_ordinaryDegree4]
  exact_mod_cast hle

/-- Exact maximal ordinary component of each vector coordinate. -/
noncomputable def ordinarySourceVectorLeading
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) : Fin 4 → MvPolynomial (Fin 4) K :=
  fun j =>
    initialForm (fun _ : Fin 4 => (1 : ℤ))
      (ordinarySourceVectorTopDegree V hV : ℤ) (V j)

/-- At least one coordinate attains the common maximal ordinary degree. -/
theorem ordinarySourceVectorLeading_ne_zero
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) :
    ordinarySourceVectorLeading V hV ≠ 0 := by
  classical
  have htop := ordinarySourceVectorTopDegree_mem V hV
  unfold ordinarySourceVectorDegreeSupport at htop
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at htop
  rcases htop with ⟨j, hj⟩
  rcases Finset.mem_image.mp hj with ⟨d, hd, hdegree⟩
  have hw :
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d =
        (ordinarySourceVectorTopDegree V hV : ℤ) := by
    rw [ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast hdegree
  have hcoeffV : MvPolynomial.coeff d (V j) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcomponent :
      MvPolynomial.coeff d (ordinarySourceVectorLeading V hV j) =
        MvPolynomial.coeff d (V j) := by
    rw [ordinarySourceVectorLeading, coeff_initialForm]
    simp [hw]
  intro hzero
  have hjzero := congrFun hzero j
  have hcoeffzero :
      MvPolynomial.coeff d (ordinarySourceVectorLeading V hV j) = 0 := by
    rw [hjzero]
    simp
  rw [hcomponent] at hcoeffzero
  exact hcoeffV hcoeffzero

/-! ## Maximal homogeneous descent of the B8 transverse kernel -/

/-- **Stage 4B9 homogeneous kernel descent.**

For an exact first transverse key `Q`, a nonzero polynomial vector killed by
all three transverse Hessian rows descends losslessly to the maximal ordinary
homogeneous slice of `Q` and the maximal ordinary homogeneous piece of the
vector. -/
theorem exists_maximalHomogeneousSlice_transverseKernel
    (Q : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hQne : Q ≠ 0)
    (hQhom :
      MvPolynomial.IsWeightedHomogeneous
        pureLongitudinalTransverseWeight Q (-(m : ℤ)))
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0)
    (hkernel :
      ∀ i : Fin 3,
        (HC4.Polynomial.hessian Q).mulVec V i.succ = 0) :
    ∃ S : FirstTransverseKeyMaximalHomogeneousSliceData Q m,
      let U := ordinarySourceVectorLeading V hV
      U ≠ 0 ∧
        ∀ i : Fin 3,
          (HC4.Polynomial.hessian S.sliceData.slice).mulVec U i.succ = 0 := by
  classical
  rcases exists_firstTransverseKeyMaximalHomogeneousSlice Q m hQne hQhom with
    ⟨S⟩
  let D := S.sliceData.ordinaryDegree
  let E := ordinarySourceVectorTopDegree V hV
  let U := ordinarySourceVectorLeading V hV

  have hQLE :
      IsWeightLE (fun _ : Fin 4 => (1 : ℤ)) (D : ℤ) Q := by
    intro d hd
    rw [ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast S.maximalDegree d hd

  have hU_ne : U ≠ 0 := by
    simpa [U] using ordinarySourceVectorLeading_ne_zero V hV

  have hrowKernel :
      ∀ i : Fin 3,
        (HC4.Polynomial.hessian S.sliceData.slice).mulVec U i.succ = 0 := by
    intro i
    have hterm :
        ∀ j : Fin 4,
          initialForm (fun _ : Fin 4 => (1 : ℤ))
              ((D : ℤ) - 2 + (E : ℤ))
              (HC4.Polynomial.hessian Q i.succ j * V j) =
            HC4.Polynomial.hessian S.sliceData.slice i.succ j * U j := by
      intro j
      have hHLE := hQLE.hessian_entry i.succ j
      have hVLE := ordinarySourceVector_component_isWeightLE V hV j
      have hmul := initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hHLE hVLE
      have hweights :
          ((D : ℤ) - (1 : ℤ) - (1 : ℤ)) + (E : ℤ) =
            (D : ℤ) - 2 + (E : ℤ) := by ring
      change
        initialForm (fun _ : Fin 4 => (1 : ℤ))
            (((D : ℤ) - (1 : ℤ) - (1 : ℤ)) + (E : ℤ))
            (HC4.Polynomial.hessian Q i.succ j * V j) =
          initialForm (fun _ : Fin 4 => (1 : ℤ))
              ((D : ℤ) - (1 : ℤ) - (1 : ℤ))
              (HC4.Polynomial.hessian Q i.succ j) *
            initialForm (fun _ : Fin 4 => (1 : ℤ)) (E : ℤ) (V j) at hmul
      rw [hweights] at hmul
      have hHtop := hessian_initialForm_entry
        (fun _ : Fin 4 => (1 : ℤ)) (D : ℤ) Q i.succ j
      have hslice := S.slice_eq_topInitial
      rw [← hslice] at hHtop
      rw [← hHtop] at hmul
      simpa [U, ordinarySourceVectorLeading, E] using hmul

    have hrow :
        ∑ j : Fin 4, HC4.Polynomial.hessian Q i.succ j * V j = 0 := by
      have hi := hkernel i
      simpa [Matrix.mulVec, dotProduct] using hi

    have hsum :
        ∑ j : Fin 4,
            HC4.Polynomial.hessian S.sliceData.slice i.succ j * U j = 0 := by
      calc
        ∑ j : Fin 4,
            HC4.Polynomial.hessian S.sliceData.slice i.succ j * U j =
            ∑ j : Fin 4,
              initialForm (fun _ : Fin 4 => (1 : ℤ))
                ((D : ℤ) - 2 + (E : ℤ))
                (HC4.Polynomial.hessian Q i.succ j * V j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact (hterm j).symm
        _ = initialForm (fun _ : Fin 4 => (1 : ℤ))
              ((D : ℤ) - 2 + (E : ℤ))
              (∑ j : Fin 4, HC4.Polynomial.hessian Q i.succ j * V j) := by
                rw [map_sum]
        _ = 0 := by rw [hrow]; simp
    simpa [Matrix.mulVec, dotProduct] using hsum

  exact ⟨S, hU_ne, hrowKernel⟩

/-! ## Carrier-facing package -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The B8 leading first-key kernel, descended to one maximal
ordinary-homogeneous source packet.  This is now exactly the homogeneous
`x0^e H_m` object to which B4 applies. -/
structure FirstKeyMaximalHomogeneousKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  hpos :
    (positiveTransverseSourceSupport
      (polynomialFamilySpecialFiber C.family)).Nonempty
  sliceData :
    FirstTransverseKeyMaximalHomogeneousSliceData
      (initialForm pureLongitudinalTransverseWeight
        (-(firstPositiveTransverseSourceDegree
          (polynomialFamilySpecialFiber C.family) hpos : ℤ))
        (polynomialFamilySpecialFiber C.family))
      (firstPositiveTransverseSourceDegree
        (polynomialFamilySpecialFiber C.family) hpos)
  vector : Fin 4 → MvPolynomial (Fin 4) K
  vector_ne_zero : vector ≠ 0
  transverseKernel :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian sliceData.sliceData.slice).mulVec
        vector i.succ = 0

/-- B8 canonically descends one step further to a nonzero homogeneous kernel
packet. -/
theorem FirstKeyLeadingTransverseKernelData.exists_maximalHomogeneousKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    Nonempty C.FirstKeyMaximalHomogeneousKernelData := by
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
    ⟨S, hUne, hUker⟩

  let U := ordinarySourceVectorLeading L.leadingVector L.leading_ne_zero
  exact ⟨{
    hpos := L.hpos
    sliceData := by simpa [Q, m, F₀] using S
    vector := U
    vector_ne_zero := by simpa [U] using hUne
    transverseKernel := by
      intro i
      simpa [U] using hUker i
  }⟩

/-- The homogeneous packet produced above inherits the complete B4 common
longitudinal-monomial profile for free. -/
theorem FirstKeyMaximalHomogeneousKernelData.longitudinalMonomialFactorProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : C.FirstKeyMaximalHomogeneousKernelData) :
    ∀ b c d : ℕ,
      longitudinalCoefficientPolynomial b c d D.sliceData.sliceData.slice ≠ 0 →
        b + c + d =
            firstPositiveTransverseSourceDegree
              (polynomialFamilySpecialFiber C.family) D.hpos ∧
          ∃ a : K,
            a ≠ 0 ∧
            longitudinalCoefficientPolynomial b c d
                D.sliceData.sliceData.slice =
              Polynomial.monomial
                (D.sliceData.sliceData.ordinaryDegree -
                  firstPositiveTransverseSourceDegree
                    (polynomialFamilySpecialFiber C.family) D.hpos) a := by
  exact D.sliceData.sliceData.longitudinalMonomialFactorProfile

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
