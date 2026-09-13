import HC4.Newton.SingularBoundaryRankSplit
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Coordinate kernel retained by the canonical codimension-two exposed carrier

`exposedSingularNonlinearBoundaryVertex` is constructed by successively taking
coordinate-maximal exact initial forms in coordinates `0,1,2,3`.  The public
record intentionally retained only the final carrier and exposed monomial, but
its canonical constructor contains more lossless support provenance:

* the stored carrier is the coordinate-`2` maximal face `D2.face`;
* every exponent in that carrier has the same coordinates `0,1,2` as the
  final exposed exponent.

Consequently, if the final exposed exponent lies on a codimension-two
coordinate boundary, at least one of its two zero coordinates lies among
`0,1,2`, and that coordinate vanishes on the *entire stored singular carrier*.
The corresponding formal partial derivative is therefore literally zero.

This is a state-free provenance lemma.  It does not turn the carrier kernel
into repair progress and it does not identify this finite coordinate-max chain
with any Smith/Rees clock.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- On the canonical A18.5.92 carrier, coordinates `0,1,2` are exactly locked
to the corresponding coordinates of the final exposed exponent. -/
theorem exposedSingularNonlinearBoundaryVertex_carrier_coordinate_eq
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d)
    (i : Fin 3)
    {q : Fin 4 →₀ ℕ}
    (hq : q ∈
      (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).carrier.support) :
    q (Fin.castSucc i) =
      (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).exponent
        (Fin.castSucc i) := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : hessianDeterminant D0.face = 0 := D0.hessian_zero hzero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : hessianDeterminant D1.face = 0 := D1.hessian_zero h0zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : hessianDeterminant D2.face = 0 := D2.hessian_zero h1zero
  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  have hcarrier :
      (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).carrier =
        D2.face := by
    rfl
  have hexponent :
      (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).exponent =
        D3.witness := by
    rfl

  rw [hcarrier] at hq
  rw [hexponent]

  have hq1 : q ∈ D1.face.support := D2.support_subset hq
  have hq0 : q ∈ D0.face.support := D1.support_subset hq1
  have hd2 : D3.witness ∈ D2.face.support := D3.witness_mem
  have hd1 : D3.witness ∈ D1.face.support := D2.support_subset hd2
  have hd0 : D3.witness ∈ D0.face.support := D1.support_subset hd1

  fin_cases i
  · simpa using
      (D0.coordinate_eq q hq0).trans
        (D0.coordinate_eq D3.witness hd0).symm
  · simpa using
      (D1.coordinate_eq q hq1).trans
        (D1.coordinate_eq D3.witness hd1).symm
  · simpa using
      (D2.coordinate_eq q hq).trans
        (D2.coordinate_eq D3.witness hd2).symm

/-- Two distinct zero coordinates in four variables force at least one zero
among the first three coordinates. -/
theorem exists_firstThree_zero_of_codimensionTwo
    {d : Fin 4 →₀ ℕ}
    (hcodim : MvExponentOnCodimensionTwoBoundary d) :
    ∃ i : Fin 3, d (Fin.castSucc i) = 0 := by
  by_cases h0 : d (0 : Fin 4) = 0
  · exact ⟨(0 : Fin 3), by simpa using h0⟩
  by_cases h1 : d (1 : Fin 4) = 0
  · exact ⟨(1 : Fin 3), by simpa using h1⟩
  by_cases h2 : d (2 : Fin 4) = 0
  · exact ⟨(2 : Fin 3), by simpa using h2⟩
  rcases hcodim with ⟨i, j, hij, hi, hj⟩
  exfalso
  fin_cases i <;> fin_cases j <;> simp_all

/-- **Canonical codimension-two carrier kernel.**

For the actual A18.5.92 constructor, a codimension-two final exposed exponent
forces a literal coordinate partial derivative of the stored singular carrier
to vanish.  The kernel coordinate is one of `0,1,2`, exactly because those are
the coordinates already locked before the final coordinate-`3` exposure. -/
theorem exposedSingularNonlinearBoundaryVertex_carrier_has_coordinateKernel_of_codimensionTwo
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d)
    (hcodim :
      MvExponentOnCodimensionTwoBoundary
        (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).exponent) :
    ∃ i : Fin 3,
      MvPolynomial.pderiv (Fin.castSucc i)
        (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).carrier = 0 := by
  rcases exists_firstThree_zero_of_codimensionTwo hcodim with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro m hm
  have hmem :
      m ∈
        (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).carrier.support :=
    MvPolynomial.mem_support_iff.mpr hm
  exact
    (exposedSingularNonlinearBoundaryVertex_carrier_coordinate_eq
      F hF hzero hnonlinear i hmem).trans hi

end

end HC4.Newton
