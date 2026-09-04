import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingTransverseSlice
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# A19.R18.22--23: exact two exposed PR profile slices and Euler action

R18.21 has reduced the closing arithmetic to the highest longitudinal profile
index and the next-highest index.  The leading transverse slice is already
retained canonically.  This module performs the matching finite extraction for
the next-highest longitudinal coefficient and records the honest contact-Rees
grade of one supported monomial in each exposed slice.

The two PR scalar identities are uniform on a fixed transverse total degree,
not merely on a chosen monomial.  We therefore also convert the exact support
of each retained slice into the polynomial Euler identities

    E_perp S = t S,
    (E_perp^2 - E_perp) S = t (t - 1) S.

This prevents cancellation between distinct transverse monomials of the same
total degree from being hidden behind the single-monomial scalar formulas.
Nothing here uses a Schur identity or a terminal vanishing equation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural all-ones weight on the three transverse profile variables. -/
def qsContactTransverseNatWeight : Fin 3 → ℕ := fun _ => 1

/-- Its Finsupp weight is exactly the total transverse degree already used by
the contact grading. -/
theorem weight_qsContactTransverseNatWeight
    (m : Fin 3 →₀ ℕ) :
    Finsupp.weight qsContactTransverseNatWeight m =
      qsContactTransverseDegree m := by
  rw [Finsupp.weight_apply]
  simp [qsContactTransverseNatWeight, Finsupp.sum_fintype,
    qsContactTransverseDegree, Fin.sum_univ_three]

/-- Total transverse Euler operator on a three-variable profile coefficient. -/
noncomputable def qsContactTransverseEuler
    (S : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i S

/-- Falling radial Euler operator `E_perp (E_perp S) - E_perp S`. -/
noncomputable def qsContactTransverseFallingEuler
    (S : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  qsContactTransverseEuler (qsContactTransverseEuler S) -
    qsContactTransverseEuler S

/-- Exact transverse support degree gives Mathlib natural weighted
homogeneity for the all-ones weight. -/
theorem isWeightedHomogeneous_qsContactTransverseNatWeight_of_exactDegree
    (S : MvPolynomial (Fin 3) K)
    (t : ℕ)
    (hexact : ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m S ≠ 0 → qsContactTransverseDegree m = t) :
    MvPolynomial.IsWeightedHomogeneous qsContactTransverseNatWeight S t := by
  intro m hm
  rw [weight_qsContactTransverseNatWeight]
  exact hexact m hm

/-- **R18.23 transverse Euler identity.** -/
theorem qsContactTransverseEuler_eq_degree_mul
    (S : MvPolynomial (Fin 3) K)
    (t : ℕ)
    (hexact : ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m S ≠ 0 → qsContactTransverseDegree m = t) :
    qsContactTransverseEuler S = MvPolynomial.C (t : K) * S := by
  have hhom :=
    isWeightedHomogeneous_qsContactTransverseNatWeight_of_exactDegree
      S t hexact
  have heuler := hhom.sum_weight_X_mul_pderiv
  simpa [qsContactTransverseEuler, qsContactTransverseNatWeight,
    Fin.sum_univ_three] using heuler

/-- The transverse Euler operator is linear over coefficient-field constants. -/
theorem qsContactTransverseEuler_C_mul
    (a : K)
    (S : MvPolynomial (Fin 3) K) :
    qsContactTransverseEuler (MvPolynomial.C a * S) =
      MvPolynomial.C a * qsContactTransverseEuler S := by
  simp [qsContactTransverseEuler, Fin.sum_univ_three]
  ring

/-- **R18.23 falling transverse Euler identity.** -/
theorem qsContactTransverseFallingEuler_eq_degree_mul
    (S : MvPolynomial (Fin 3) K)
    (t : ℕ)
    (hexact : ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m S ≠ 0 → qsContactTransverseDegree m = t) :
    qsContactTransverseFallingEuler S =
      MvPolynomial.C ((t : K) * ((t : K) - 1)) * S := by
  have hE := qsContactTransverseEuler_eq_degree_mul S t hexact
  unfold qsContactTransverseFallingEuler
  rw [hE, qsContactTransverseEuler_C_mul, hE]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- Exact maximal-transverse piece of the next-highest longitudinal profile
coefficient.  The index `M` is retained in the same form expected by the
existing two-exposed-layer cancellation theorem. -/
structure QsOtherFacetContactNextTransverseSliceData
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) where
  N : ℕ
  M : ℕ
  N_eq : N = R.profile.natDegree
  M_eq : M =
    (R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree
  M_lt_N : M < N
  transverseDegree : ℕ
  slice : MvPolynomial (Fin 3) K
  slice_eq :
    slice = HC4.Polynomial.initialForm
      qsContactTransverseIntegerWeight (transverseDegree : ℤ)
      (R.profile.coeff M)
  slice_ne_zero : slice ≠ 0
  slice_source :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m slice ≠ 0 →
        MvPolynomial.coeff m (R.profile.coeff M) ≠ 0
  slice_exact_transverseDegree :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m slice ≠ 0 →
        qsContactTransverseDegree m = transverseDegree
  transverseDegree_max :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m (R.profile.coeff M) ≠ 0 →
        qsContactTransverseDegree m ≤ transverseDegree

/-- The next-highest longitudinal coefficient is genuinely nonzero and hence
has a nonzero maximal transverse homogeneous component. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.exists_nextTransverseSlice
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Nonempty (QsOtherFacetContactNextTransverseSliceData R) := by
  classical
  let N : ℕ := R.profile.natDegree
  have hNtwo : 2 ≤ N := by
    simpa [N] using R.degree_two_le
  have hNpos : 0 < N := by omega
  let Q : Polynomial (MvPolynomial (Fin 3) K) :=
    R.profile - Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N
  have hQne : Q ≠ 0 := by
    intro hzero
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 3) K) => p.coeff 0) hzero
    dsimp [Q] at hc
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul] at hc
    have h0N : (0 : ℕ) ≠ N := by omega
    simp [Polynomial.coeff_X_pow, h0N] at hc
    exact R.coeff_zero_ne hc
  have htopdeg :
      (Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree ≤ N := by
    calc
      (Polynomial.C R.profile.leadingCoeff * Polynomial.X ^ N).natDegree ≤
          (Polynomial.X ^ N).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = N := by simp
  have hQdeg : Q.natDegree ≤ N := by
    dsimp [Q]
    exact (Polynomial.natDegree_sub_le_iff_left htopdeg).2 (by simp [N])
  have hQcoeffN : Q.coeff N = 0 := by
    dsimp [Q, N]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    simp [Polynomial.coeff_X_pow]
  let M : ℕ := Q.natDegree
  have hMN : M < N := by
    have hne : Q.natDegree ≠ N := by
      intro heq
      have hlead : Q.coeff Q.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hQne
      rw [heq, hQcoeffN] at hlead
      exact hlead rfl
    dsimp [M]
    omega
  have hQlead : Q.coeff M ≠ 0 := by
    dsimp [M]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hprofileM : R.profile.coeff M = Q.coeff M := by
    dsimp [Q]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hne : M ≠ N := Nat.ne_of_lt hMN
    simp [Polynomial.coeff_X_pow, hne]
  have hAMne : R.profile.coeff M ≠ 0 := by
    rw [hprofileM]
    exact hQlead
  have hsupport : (R.profile.coeff M).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hAMne
  rcases Finset.exists_max_image
      (R.profile.coeff M).support qsContactTransverseDegree hsupport with
    ⟨m, hm, hmax⟩
  let t : ℕ := qsContactTransverseDegree m
  let S : MvPolynomial (Fin 3) K :=
    HC4.Polynomial.initialForm
      qsContactTransverseIntegerWeight (t : ℤ) (R.profile.coeff M)
  have hmcoeff : MvPolynomial.coeff m (R.profile.coeff M) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hmweight :
      Finsupp.weight qsContactTransverseIntegerWeight m = (t : ℤ) := by
    rw [weight_qsContactTransverseIntegerWeight]
  have hmS : MvPolynomial.coeff m S ≠ 0 := by
    dsimp [S]
    rw [HC4.Polynomial.coeff_initialForm, if_pos hmweight]
    exact hmcoeff
  have hSne : S ≠ 0 := by
    intro hz
    rw [hz] at hmS
    simp at hmS
  have hsource :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q S ≠ 0 →
          MvPolynomial.coeff q (R.profile.coeff M) ≠ 0 := by
    intro q hq
    have hq' := hq
    dsimp [S] at hq'
    rw [HC4.Polynomial.coeff_initialForm] at hq'
    split at hq'
    · exact hq'
    · exact (hq' rfl).elim
  have hexact :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q S ≠ 0 →
          qsContactTransverseDegree q = t := by
    intro q hq
    have hq' := hq
    dsimp [S] at hq'
    rw [HC4.Polynomial.coeff_initialForm] at hq'
    split at hq'
    · have hw :
          Finsupp.weight qsContactTransverseIntegerWeight q = (t : ℤ) := ‹_›
      rw [weight_qsContactTransverseIntegerWeight] at hw
      exact_mod_cast hw
    · exact (hq' rfl).elim
  have hmax' :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q (R.profile.coeff M) ≠ 0 →
          qsContactTransverseDegree q ≤ t := by
    intro q hq
    exact hmax q (MvPolynomial.mem_support_iff.mpr hq)
  exact ⟨{
    N := N
    M := M
    N_eq := rfl
    M_eq := by rfl
    M_lt_N := hMN
    transverseDegree := t
    slice := S
    slice_eq := rfl
    slice_ne_zero := hSne
    slice_source := hsource
    slice_exact_transverseDegree := hexact
    transverseDegree_max := hmax'
  }⟩

/-- Leading exposed slice: exact transverse Euler eigenvalue. -/
theorem QsOtherFacetContactLeadingTransverseSliceData.transverseEuler_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactLeadingTransverseSliceData R) :
    qsContactTransverseEuler S.slice =
      MvPolynomial.C (S.transverseDegree : K) * S.slice :=
  qsContactTransverseEuler_eq_degree_mul
    S.slice S.transverseDegree S.slice_exact_transverseDegree

/-- Leading exposed slice: exact falling transverse Euler eigenvalue. -/
theorem QsOtherFacetContactLeadingTransverseSliceData.transverseFallingEuler_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactLeadingTransverseSliceData R) :
    qsContactTransverseFallingEuler S.slice =
      MvPolynomial.C
        ((S.transverseDegree : K) * ((S.transverseDegree : K) - 1)) *
        S.slice :=
  qsContactTransverseFallingEuler_eq_degree_mul
    S.slice S.transverseDegree S.slice_exact_transverseDegree

/-- Leading maximality collapses the entire leading coefficient to transverse
degree zero once the exposed self scalar has forced the maximal slice degree
to vanish. -/
theorem QsOtherFacetContactLeadingTransverseSliceData.source_transverseDegree_eq_zero
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactLeadingTransverseSliceData R)
    (hzero : S.transverseDegree = 0)
    {m : Fin 3 →₀ ℕ}
    (hm : MvPolynomial.coeff m
      (R.profile.coeff R.profile.natDegree) ≠ 0) :
    qsContactTransverseDegree m = 0 := by
  have hle := S.transverseDegree_max m hm
  rw [hzero] at hle
  omega

/-- Next-highest exposed slice: exact transverse Euler eigenvalue. -/
theorem QsOtherFacetContactNextTransverseSliceData.transverseEuler_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactNextTransverseSliceData R) :
    qsContactTransverseEuler S.slice =
      MvPolynomial.C (S.transverseDegree : K) * S.slice :=
  qsContactTransverseEuler_eq_degree_mul
    S.slice S.transverseDegree S.slice_exact_transverseDegree

/-- Next-highest exposed slice: exact falling transverse Euler eigenvalue. -/
theorem QsOtherFacetContactNextTransverseSliceData.transverseFallingEuler_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactNextTransverseSliceData R) :
    qsContactTransverseFallingEuler S.slice =
      MvPolynomial.C
        ((S.transverseDegree : K) * ((S.transverseDegree : K) - 1)) *
        S.slice :=
  qsContactTransverseFallingEuler_eq_degree_mul
    S.slice S.transverseDegree S.slice_exact_transverseDegree

/-- Once the cross scalar has forced the maximal next transverse degree to at
most one, every monomial in the whole next longitudinal coefficient has
transverse degree at most one. -/
theorem QsOtherFacetContactNextTransverseSliceData.source_transverseDegree_le_one
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactNextTransverseSliceData R)
    (hle : S.transverseDegree ≤ 1)
    {m : Fin 3 →₀ ℕ}
    (hm : MvPolynomial.coeff m (R.profile.coeff S.M) ≠ 0) :
    qsContactTransverseDegree m ≤ 1 := by
  exact le_trans (S.transverseDegree_max m hm) hle

/-- Finite PR extremal data used by the closing coefficient calculation.  It
retains one actual supported monomial from each exact transverse slice and the
corresponding honest contact deficit equations. -/
structure QsOtherFacetContactPrExtremalDegreeData
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) where
  leading : QsOtherFacetContactLeadingTransverseSliceData R
  next : QsOtherFacetContactNextTransverseSliceData R
  leadingExponent : Fin 3 →₀ ℕ
  leading_mem : leadingExponent ∈ leading.slice.support
  nextExponent : Fin 3 →₀ ℕ
  next_mem : nextExponent ∈ next.slice.support
  qN : ℕ
  qM : ℕ
  N_two_le : 2 ≤ next.N
  leading_grade :
    qN + P.profileWeight * next.N + leading.transverseDegree = T.topFace.degree
  next_grade :
    qM + P.profileWeight * next.M + next.transverseDegree = T.topFace.degree

/-- Construct the exact two exposed degree packages.  The grading equalities
are just natural subtraction after applying the already-proved contact support
budget to the retained source monomials. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.prExtremalDegreeData
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Nonempty (QsOtherFacetContactPrExtremalDegreeData R) := by
  classical
  let L := Classical.choice R.exists_leadingTransverseSlice
  let M := Classical.choice R.exists_nextTransverseSlice
  have hLN : M.N = R.profile.natDegree := M.N_eq
  have hleadSupport : L.slice.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr L.slice_ne_zero
  rcases hleadSupport with ⟨mN, hmN⟩
  have hmNcoeff : MvPolynomial.coeff mN L.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmN
  have hmNsource :
      MvPolynomial.coeff mN (R.profile.coeff R.profile.natDegree) ≠ 0 :=
    L.slice_source mN hmNcoeff
  have hmNraw : mN ∈ (R.profile.coeff R.profile.natDegree).support :=
    MvPolynomial.mem_support_iff.mpr hmNsource
  have hleadBound := R.transverseDegree_add_profileWeight_mul_le hmNraw
  have hleadDegree := L.slice_exact_transverseDegree mN hmNcoeff
  have hnextSupport : M.slice.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr M.slice_ne_zero
  rcases hnextSupport with ⟨mM, hmM⟩
  have hmMcoeff : MvPolynomial.coeff mM M.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmM
  have hmMsource : MvPolynomial.coeff mM (R.profile.coeff M.M) ≠ 0 :=
    M.slice_source mM hmMcoeff
  have hmMraw : mM ∈ (R.profile.coeff M.M).support :=
    MvPolynomial.mem_support_iff.mpr hmMsource
  have hnextBound := R.transverseDegree_add_profileWeight_mul_le hmMraw
  have hnextDegree := M.slice_exact_transverseDegree mM hmMcoeff
  let qN := T.topFace.degree -
    (L.transverseDegree + P.profileWeight * M.N)
  let qM := T.topFace.degree -
    (M.transverseDegree + P.profileWeight * M.M)
  have hleadGrade :
      qN + P.profileWeight * M.N + L.transverseDegree = T.topFace.degree := by
    dsimp [qN]
    rw [hLN]
    rw [hleadDegree] at hleadBound
    omega
  have hnextGrade :
      qM + P.profileWeight * M.M + M.transverseDegree = T.topFace.degree := by
    dsimp [qM]
    rw [hnextDegree] at hnextBound
    omega
  exact ⟨{
    leading := L
    next := M
    leadingExponent := mN
    leading_mem := hmN
    nextExponent := mM
    next_mem := hmM
    qN := qN
    qM := qM
    N_two_le := by
      rw [M.N_eq]
      exact R.degree_two_le
    leading_grade := hleadGrade
    next_grade := hnextGrade
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
