import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalComplementLayers
import Mathlib.Tactic

/-!
# A19.R18.36: the exact leading PR self coefficient

We extract both indices of the leading self pair.  The longitudinal support
ceiling leaves only `(N,N)`, and contact-order minimality then leaves only
`(qN,qN)`.  Applying this to the three straightened complementary entries
computes the raw complementary determinant as

    -N*t*(N+t-1) * S_N^2.

This is a coefficient identity, not a vanishing theorem.  The geometric step
must still kill this exact coefficient, keeping the bordered Schur and mixed
coupling corrections from R18.21.  Singularity of the full Hessian alone
does not say that a raw complementary two-by-two determinant is zero.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}
variable {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}

private noncomputable def prLayer
    (F : MvPolynomial (Fin 4) (Polynomial K)) (q n : ℕ) :
    MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3 (familyParameterLayer F q)).coeff n

omit [CharZero K] [IsAlgClosed K] in
private theorem prLayer_add (F G : MvPolynomial (Fin 4) (Polynomial K)) (q n : ℕ) :
    prLayer (F + G) q n = prLayer F q n + prLayer G q n := by
  simp only [prLayer, ← parameterFirstEquiv_coeff, map_add, Polynomial.coeff_add]

omit [CharZero K] [IsAlgClosed K] in
private theorem prLayer_sub (F G : MvPolynomial (Fin 4) (Polynomial K)) (q n : ℕ) :
    prLayer (F - G) q n = prLayer F q n - prLayer G q n := by
  simp only [prLayer, ← parameterFirstEquiv_coeff, map_sub, Polynomial.coeff_sub]

omit [CharZero K] [IsAlgClosed K] in
private theorem prLayer_constant_mul (c : K)
    (F : MvPolynomial (Fin 4) (Polynomial K)) (q n : ℕ) :
    prLayer (MvPolynomial.C (Polynomial.C c) * F) q n =
      MvPolynomial.C c * prLayer F q n := by
  apply MvPolynomial.ext
  intro m
  simp only [prLayer, MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.coeff_C_mul]
  rw [familyParameterLayer_coeff, familyParameterLayer_coeff,
    MvPolynomial.coeff_C_mul, Polynomial.coeff_C_mul]

omit [CharZero K] [IsAlgClosed K] in
private theorem prLayer_mul (F G : MvPolynomial (Fin 4) (Polynomial K)) (q n : ℕ) :
    prLayer (F * G) q n =
      ∑ ij ∈ Finset.antidiagonal q, ∑ ab ∈ Finset.antidiagonal n,
        prLayer F ij.1 ab.1 * prLayer G ij.2 ab.2 := by
  classical
  unfold prLayer
  rw [← parameterFirstEquiv_coeff, map_mul, Polynomial.coeff_mul]
  simp only [map_sum, Polynomial.finset_sum_coeff, map_mul,
    Polynomial.coeff_mul, parameterFirstEquiv_coeff]

/-- The two finite convolutions collapse separately; no product clock is used. -/
private theorem prLayer_mul_leading
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (F G : MvPolynomial (Fin 4) (Polynomial K))
    (a b : ℕ → ℕ → K)
    (hF : ∀ q n, prLayer F q n =
      MvPolynomial.C (a q n) * R.contactLongitudinalParameterLayer q n)
    (hG : ∀ q n, prLayer G q n =
      MvPolynomial.C (b q n) * R.contactLongitudinalParameterLayer q n) :
    prLayer (F * G) (E.qN + E.qN) (E.next.N + E.next.N) =
      prLayer F E.qN E.next.N * prLayer G E.qN E.next.N := by
  classical
  rw [prLayer_mul]
  have hlong (i j : ℕ) :
      (∑ ab ∈ Finset.antidiagonal (E.next.N + E.next.N),
        prLayer F i ab.1 * prLayer G j ab.2) =
      prLayer F i E.next.N * prLayer G j E.next.N := by
    apply Finset.sum_eq_single (E.next.N, E.next.N)
    · intro ab hab hne
      have hab' := Finset.mem_antidiagonal.mp hab
      by_cases ha : E.next.N < ab.1
      · rw [hF, E.contactParameterLayer_longitudinal_eq_zero_of_N_lt i ab.1 ha]
        simp
      · have hb : E.next.N < ab.2 := by
          by_contra hb
          apply hne
          apply Prod.ext <;> omega
        rw [hG, E.contactParameterLayer_longitudinal_eq_zero_of_N_lt j ab.2 hb]
        simp
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim
  simp_rw [hlong]
  apply Finset.sum_eq_single (E.qN, E.qN)
  · intro ij hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    by_cases hi : ij.1 < E.qN
    · rw [hF, E.contactLeadingParameterLayer_eq_zero_of_lt ij.1 hi]
      simp
    · have hj : ij.2 < E.qN := by
        by_contra hj
        apply hne
        apply Prod.ext <;> omega
      rw [hG, E.contactLeadingParameterLayer_eq_zero_of_lt ij.2 hj]
      simp
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

private theorem prLayer_x (q n : ℕ) :
    prLayer (P.contactWeightedEulerShear qsPrContactSchurPermutation).x q n =
      MvPolynomial.C ((n : K) * ((n : K) - 1)) *
        R.contactLongitudinalParameterLayer q n := by
  have hx : (P.contactWeightedEulerShear qsPrContactSchurPermutation).x =
      HC4.Polynomial.eulerScaledHessian P.contactFamily (0 : Fin 4) 0 := by
    simp [QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear,
      QsOtherFacetContactQuadraticReesPackage.contactEulerHessianFourBlock,
      GeneralFourBlock.shearSecondComplement, GeneralFourBlock.ofSymmetricMatrix]
  rw [hx]
  exact R.contactLongitudinalSourceHessianLayer_eq q n

private theorem prLayer_y (q n : ℕ) :
    prLayer (P.contactWeightedEulerShear qsPrContactSchurPermutation).y q n =
      MvPolynomial.C ((n : K) *
        ((T.topFace.degree : K) - (P.profileWeight : K) - (q : K))) *
        R.contactLongitudinalParameterLayer q n := by
  rw [P.pr_contactWeightedEulerShear_y, prLayer_sub, prLayer_constant_mul]
  have he : prLayer (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) q n =
      MvPolynomial.C (n : K) * R.contactLongitudinalParameterLayer q n :=
    R.contactLongitudinalSourceEulerLayer_eq q n
  have hqe :
      prLayer (familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily)) q n =
        MvPolynomial.C (q : K) *
          prLayer (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) q n := by
    unfold prLayer
    rw [familyParameterLayer_familyParameterEuler]
    apply MvPolynomial.ext
    intro m
    simp only [MvPolynomial.finSuccEquiv_coeff_coeff]
    change MvPolynomial.coeff (m.cons n)
        (MvPolynomial.C (q : K) * _) = _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [hqe, he]
  simp only [map_mul, map_sub]
  ring

private theorem prLayer_z (q n : ℕ) :
    prLayer (P.contactWeightedEulerShear qsPrContactSchurPermutation).z q n =
      MvPolynomial.C
        ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1) -
          2 * ((T.topFace.degree : K) - 1) * (q : K) +
          (q : K) * ((q : K) - 1) +
          (P.profileWeight : K) * (1 - (P.profileWeight : K)) * (n : K)) *
        R.contactLongitudinalParameterLayer q n := by
  rw [P.pr_contactWeightedEulerShear_z]
  have htwo :
      (2 * MvPolynomial.C (Polynomial.C ((T.topFace.degree : K) - 1)) :
        MvPolynomial (Fin 4) (Polynomial K)) =
        MvPolynomial.C (Polynomial.C (2 * ((T.topFace.degree : K) - 1))) := by
    simp only [map_mul, map_ofNat]
  rw [htwo]
  simp only [prLayer_add, prLayer_sub, prLayer_constant_mul]
  have he := R.contactLongitudinalParameterEulerLayer_eq q n
  have hee := R.contactLongitudinalParameterSecondEulerLayer_eq q n
  have hn := R.contactLongitudinalSourceEulerLayer_eq q n
  change prLayer (familyParameterEuler P.contactFamily) q n = _ at he
  change prLayer (familyParameterSecondEuler P.contactFamily) q n = _ at hee
  change prLayer (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) q n = _ at hn
  rw [he, hee, hn]
  have hbase : prLayer P.contactFamily q n =
      R.contactLongitudinalParameterLayer q n := rfl
  rw [hbase]
  simp only [map_add, map_sub, map_mul, map_one, map_ofNat]
  ring

/-- **R18.36 exact leading self coefficient.**  Both convolutions and all
parameter/source Euler operators have been evaluated.  The right side is the
precise nonzero-slice expression consumed by
`leading_transverseDegree_eq_zero_of_selfSlice` if geometry proves it zero. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingRawComplementDetLayer_eq
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        ((P.contactWeightedEulerShear qsPrContactSchurPermutation).x *
            (P.contactWeightedEulerShear qsPrContactSchurPermutation).z -
          (P.contactWeightedEulerShear qsPrContactSchurPermutation).y *
            (P.contactWeightedEulerShear qsPrContactSchurPermutation).y)
        (E.qN + E.qN))).coeff (E.next.N + E.next.N) =
      MvPolynomial.C
        (-(E.next.N : K) * (E.leading.transverseDegree : K) *
          ((E.next.N : K) + (E.leading.transverseDegree : K) - 1)) *
        E.leading.slice * E.leading.slice := by
  change prLayer _ _ _ = _
  rw [prLayer_sub]
  rw [prLayer_mul_leading E _ _ _ _ (prLayer_x (R := R)) (prLayer_z (R := R)),
    prLayer_mul_leading E _ _ _ _ (prLayer_y (R := R)) (prLayer_y (R := R))]
  rw [prLayer_x (R := R), prLayer_z (R := R), prLayer_y (R := R),
    E.contactLeadingParameterLayer_eq]
  have hs := prContactWeightedEuler_rawComplement_selfScalar (K := K)
    T.topFace.degree P.profileWeight E.next.N E.leading.transverseDegree E.qN
    E.leading_grade
  have hsC := congrArg (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) hs
  simp only [map_sub, map_mul, map_add, map_neg, map_one] at hsC ⊢
  linear_combination hsC * E.leading.slice * E.leading.slice

/-- **R18.37 exact leading parameter residual.**  The residual does not
vanish just because the contact convolution is extremal.  Its scalar is
`N*qN*(qN+N+2*t-1)`, whereas the raw complementary determinant has scalar
`-N*t*(N+t-1)`.  These two quantities must not be identified. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterResidualLayer_eq
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer P.contactProfileParameterResidual
        (E.qN + E.qN))).coeff (E.next.N + E.next.N) =
      MvPolynomial.C
        ((E.next.N : K) * (E.qN : K) *
          ((E.qN : K) + (E.next.N : K) +
            2 * (E.leading.transverseDegree : K) - 1)) *
        E.leading.slice * E.leading.slice := by
  let F := P.contactFamily
  let H := HC4.Polynomial.eulerScaledHessian F (0 : Fin 4) 0
  let A := HC4.Polynomial.mvEuler (0 : Fin 4) F
  let B := familyParameterEuler A
  let J := familyParameterEuler F
  let L := familyParameterSecondEuler F
  have hH (q n : ℕ) : prLayer H q n =
      MvPolynomial.C ((n : K) * ((n : K) - 1)) *
        R.contactLongitudinalParameterLayer q n :=
    R.contactLongitudinalSourceHessianLayer_eq q n
  have hA (q n : ℕ) : prLayer A q n =
      MvPolynomial.C (n : K) * R.contactLongitudinalParameterLayer q n :=
    R.contactLongitudinalSourceEulerLayer_eq q n
  have hJ (q n : ℕ) : prLayer J q n =
      MvPolynomial.C (q : K) * R.contactLongitudinalParameterLayer q n :=
    R.contactLongitudinalParameterEulerLayer_eq q n
  have hL (q n : ℕ) : prLayer L q n =
      MvPolynomial.C ((q : K) * ((q : K) - 1)) *
        R.contactLongitudinalParameterLayer q n := by
    have h := R.contactLongitudinalParameterSecondEulerLayer_eq q n
    simpa only [map_mul, map_sub, map_one] using h
  have hB (q n : ℕ) : prLayer B q n =
      MvPolynomial.C ((q : K) * (n : K)) *
        R.contactLongitudinalParameterLayer q n := by
    have hb : prLayer B q n = MvPolynomial.C (q : K) * prLayer A q n := by
      dsimp [B, prLayer]
      rw [familyParameterLayer_familyParameterEuler]
      apply MvPolynomial.ext
      intro m
      simp only [MvPolynomial.finSuccEquiv_coeff_coeff]
      change MvPolynomial.coeff (m.cons n)
          (MvPolynomial.C (q : K) * _) = _
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
        MvPolynomial.finSuccEquiv_coeff_coeff]
    rw [hb, hA, map_mul, mul_assoc]
  have hres : P.contactProfileParameterResidual =
      H * L -
        MvPolynomial.C (Polynomial.C (2 * ((T.topFace.degree : K) - 1))) *
          (H * J) +
        MvPolynomial.C (Polynomial.C
          (2 * ((T.topFace.degree : K) - (P.profileWeight : K)))) *
          (A * B) - B * B := by
    unfold QsOtherFacetContactQuadraticReesPackage.contactProfileParameterResidual
    dsimp [H, L, J, A, B, F]
    simp only [map_mul, map_ofNat]
    ring
  change prLayer _ _ _ = _
  rw [hres]
  simp only [prLayer_sub, prLayer_add, prLayer_constant_mul]
  rw [prLayer_mul_leading E H L _ _ hH hL,
    prLayer_mul_leading E H J _ _ hH hJ,
    prLayer_mul_leading E A B _ _ hA hB,
    prLayer_mul_leading E B B _ _ hB hB]
  rw [hH, hL, hJ, hA, hB, E.contactLeadingParameterLayer_eq]
  have hgradeK : (T.topFace.degree : K) =
      (E.qN : K) + (P.profileWeight : K) * (E.next.N : K) +
        (E.leading.transverseDegree : K) := by
    exact_mod_cast E.leading_grade.symm
  have hs :
      (E.next.N : K) * ((E.next.N : K) - 1) *
          ((E.qN : K) * ((E.qN : K) - 1)) -
        2 * ((T.topFace.degree : K) - 1) *
          ((E.next.N : K) * ((E.next.N : K) - 1) * (E.qN : K)) +
        2 * ((T.topFace.degree : K) - (P.profileWeight : K)) *
          ((E.next.N : K) * ((E.qN : K) * (E.next.N : K))) -
        ((E.qN : K) * (E.next.N : K)) * ((E.qN : K) * (E.next.N : K)) =
      (E.next.N : K) * (E.qN : K) *
        ((E.qN : K) + (E.next.N : K) +
          2 * (E.leading.transverseDegree : K) - 1) := by
    rw [hgradeK]
    ring
  have hsC := congrArg (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) hs
  simp only [map_sub, map_mul, map_add, map_one, map_ofNat] at hsC ⊢
  linear_combination hsC * E.leading.slice * E.leading.slice

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
