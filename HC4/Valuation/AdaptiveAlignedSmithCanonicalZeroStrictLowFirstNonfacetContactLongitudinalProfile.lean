import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticPreclosing
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectInitialForm
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# A19.114: exact noncancelling longitudinal profile of the contact source

The final staircase profile must retain a genuine longitudinal degree at least
two.  Evaluating the three transverse variables at scalars would risk
cancellation.  Mathlib already supplies the exact representation we need:

    MvPolynomial.finSuccEquiv K 3 F

views a four-variable source `F` as a polynomial in source coordinate `0` with
coefficients in `MvPolynomial (Fin 3) K`.  Distinct transverse monomials remain
distinct coefficients, so no evaluation or generic-point choice is involved.

For the represented source in the lower `.qs` branch:

* the ray facet gives a nonzero constant longitudinal coefficient;
* the strict-low codimension-two witness gives a nonzero coefficient in
  longitudinal degree at least two;
* the integral contact bound implies
  `natDegree * (contactGap + 1) <= topFace.degree`.

Thus every non-residual field of the eventual weighted profile is already
available over the transverse polynomial coefficient domain.
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

/-- Source polynomial viewed exactly as a longitudinal polynomial with symbolic
transverse coefficients. -/
noncomputable def qsContactRawLongitudinalProfile :
    Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.finSuccEquiv K 3
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)

/-- Exact raw profile data before passing the transverse coefficient domain to
its fraction field and applying the stationary residual equation. -/
structure QsOtherFacetContactRawLongitudinalProfilePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetContactQuadraticReesPackage C) where
  profile : Polynomial (MvPolynomial (Fin 3) K)
  profile_eq : profile = qsContactRawLongitudinalProfile (T := T)
  coeff_zero_ne : profile.coeff 0 ≠ 0
  support_bound : profile.natDegree * P.profileWeight ≤ T.topFace.degree
  degree_two_le : 2 ≤ profile.natDegree

private theorem smithTransverse_cons_zero_eq
    (e : Fin 4 →₀ ℕ) :
    (HC4.Newton.smithTransverseExponent (e 1) (e 2) (e 3)).cons (e 0) = e := by
  ext i
  fin_cases i
  · simp
  · change
      ((HC4.Newton.smithTransverseExponent (e 1) (e 2) (e 3)).cons (e 0))
        (Fin.succ (0 : Fin 3)) = e 1
    rw [Finsupp.cons_succ]
    exact HC4.Newton.smithTransverseExponent_zero (e 1) (e 2) (e 3)
  · change
      ((HC4.Newton.smithTransverseExponent (e 1) (e 2) (e 3)).cons (e 0))
        (Fin.succ (1 : Fin 3)) = e 2
    rw [Finsupp.cons_succ]
    exact HC4.Newton.smithTransverseExponent_one (e 1) (e 2) (e 3)
  · change
      ((HC4.Newton.smithTransverseExponent (e 1) (e 2) (e 3)).cons (e 0))
        (Fin.succ (2 : Fin 3)) = e 3
    rw [Finsupp.cons_succ]
    exact HC4.Newton.smithTransverseExponent_two (e 1) (e 2) (e 3)

/-- **A19.114 noncancelling raw profile.** -/
theorem QsOtherFacetContactQuadraticReesPackage.rawLongitudinalProfilePackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    Nonempty (QsOtherFacetContactRawLongitudinalProfilePackage C P) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let Q : Polynomial (MvPolynomial (Fin 3) K) :=
    MvPolynomial.finSuccEquiv K 3 F

  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  have hfacetSourceCoeff :
      MvPolynomial.coeff C.ray.facetExponent F ≠ 0 := by
    rw [← C.ray_coeff_eq_represented_source_of_mem C.ray.facet_mem_face]
    exact MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face
  let mf : Fin 3 →₀ ℕ :=
    HC4.Newton.smithTransverseExponent
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
  have hmf : mf.cons 0 = C.ray.facetExponent := by
    dsimp [mf]
    rw [← hfacet0]
    exact smithTransverse_cons_zero_eq C.ray.facetExponent
  have hQzeroCoeff :
      MvPolynomial.coeff mf (Q.coeff 0) ≠ 0 := by
    have h := MvPolynomial.finSuccEquiv_coeff_coeff mf F 0
    rw [hmf] at h
    rw [h]
    exact hfacetSourceCoeff
  have hQzero : Q.coeff 0 ≠ 0 := by
    intro hz
    rw [hz] at hQzeroCoeff
    simp at hQzeroCoeff
  have hQne : Q ≠ 0 := by
    intro hz
    have := congrArg (fun q : Polynomial (MvPolynomial (Fin 3) K) => q.coeff 0) hz
    simp [hQzero] at this

  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨e, heF, _hedeg, he0, _hecodim⟩
  let me : Fin 3 →₀ ℕ :=
    HC4.Newton.smithTransverseExponent (e 1) (e 2) (e 3)
  have hme : me.cons (e 0) = e := by
    dsimp [me]
    exact smithTransverse_cons_zero_eq e
  have heSourceCoeff : MvPolynomial.coeff e F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp heF
  have hQeCoeff : MvPolynomial.coeff me (Q.coeff (e 0)) ≠ 0 := by
    have h := MvPolynomial.finSuccEquiv_coeff_coeff me F (e 0)
    rw [hme] at h
    rw [h]
    exact heSourceCoeff
  have hQe : Q.coeff (e 0) ≠ 0 := by
    intro hz
    rw [hz] at hQeCoeff
    simp at hQeCoeff
  have heMemQ : e 0 ∈ Q.support := Polynomial.mem_support_iff.mpr hQe
  have hdegreeTwo : 2 ≤ Q.natDegree := by
    have hle := Polynomial.le_natDegree_of_mem_supp _ heMemQ
    omega

  have hlead : Q.coeff Q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  rcases MvPolynomial.support_nonempty.mpr hlead with ⟨m, hm⟩
  have hmCoeff : MvPolynomial.coeff m (Q.coeff Q.natDegree) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hsourceCoeff :
      MvPolynomial.coeff (m.cons Q.natDegree) F ≠ 0 := by
    have h := MvPolynomial.finSuccEquiv_coeff_coeff m F Q.natDegree
    rw [← h]
    simpa [Q] using hmCoeff
  have hsourceMem : m.cons Q.natDegree ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hcontact := P.source_weight_le hsourceMem
  have hzero : (m.cons Q.natDegree) (0 : Fin 4) = Q.natDegree := by
    simp
  rw [hzero] at hcontact
  have hdegLower :
      Q.natDegree ≤
        HC4.Polynomial.ordinaryDegree4 (m.cons Q.natDegree) := by
    simp [HC4.Polynomial.ordinaryDegree4]
    omega
  have hsupport : Q.natDegree * P.profileWeight ≤ T.topFace.degree := by
    rw [P.profileWeight_eq]
    calc
      Q.natDegree * (P.contactGap + 1) =
          P.contactGap * Q.natDegree + Q.natDegree := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm Q.natDegree P.contactGap]
      _ = Q.natDegree + P.contactGap * Q.natDegree := by omega
      _ ≤ HC4.Polynomial.ordinaryDegree4 (m.cons Q.natDegree) +
            P.contactGap * Q.natDegree :=
          Nat.add_le_add_right hdegLower _
      _ ≤ T.topFace.degree := hcontact

  exact ⟨{
    profile := Q
    profile_eq := by rfl
    coeff_zero_ne := hQzero
    support_bound := hsupport
    degree_two_le := hdegreeTwo
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
