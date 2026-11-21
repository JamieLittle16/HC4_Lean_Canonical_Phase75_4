import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberCentral
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberThreeLayerReflection
import HC4.Valuation.RankThreeLineSpecialisationHessianDeterminantSwap
import HC4.Polynomial.FiniteStaircaseTranslatedMiddleEvaluation
import HC4.Polynomial.FiniteStaircaseEndpointDoubleRootEvaluation
import HC4.Polynomial.FiniteStaircaseThreeLayerEvaluation
import Mathlib.Tactic

/-!
# A19 central one-fibre: the lower translated mode vanishes

After the previous eliminations a surviving one-fibre profile lies on
`j+1=k`, has degree `k`, and translates at the common endpoint affine root to

    u0 X^(k-1) + v0 X^k,   v0 != 0.

At `X=2 alpha` write `u=alpha^(k-1)u0`, `v=alpha^k v0`.  The honest highest-
and locked-based three-layer pencils are both singular.  Their nonresonant
second parameter-gap jets therefore give the two state-free middle variation
equations.  If `u != 0`, cancelling the nonzero endpoint factors leaves

    ((k*n+k-n-3)u + 2kv) = 0,
    ((ell*k-ell+2k-4)u + 2kv) = 0.

Subtracting yields `(k-1)(n-ell-1)u=0`, contradicting `k>1`, `u!=0`, and the
retained strict separation `n<ell+1`.  Hence `u=0`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

/-- **Central lower translated mode vanishes.** -/
theorem oneFiber_central_translated_lower_mode_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    let a0 : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
    let b0 : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
    let cLo : K := a0 * ((F.locked.ell : K) + 1)
    let dLo : K := b0 * (F.locked.ell : K)
    let alpha : K := -cLo / dLo
    let psi := translatePolynomial alpha Alo.coefficientProfile
    alpha ^ (Alo.k - 1) * psi.coeff (Alo.k - 1) = 0 := by
  let a0 : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b0 : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let c0 : K := MvPolynomial.coeff F.highest.e0 S.slice
  let d0 : K := MvPolynomial.coeff F.highest.e1 S.slice
  let cLo : K := a0 * ((F.locked.ell : K) + 1)
  let dLo : K := b0 * (F.locked.ell : K)
  let cHi : K := c0 * (F.highest.n : K)
  let dHi : K := d0 * ((F.highest.n - 1 : ℕ) : K)
  let alpha : K := -cLo / dLo
  let psi : Polynomial K := translatePolynomial alpha Alo.coefficientProfile
  let u0 : K := psi.coeff (Alo.k - 1)
  let v0 : K := psi.coeff Alo.k
  let u : K := alpha ^ (Alo.k - 1) * u0
  let v : K := alpha ^ Alo.k * v0
  let lamHi : K := d0 * alpha / (F.highest.n : K)
  let lamLo : K := b0 * alpha / ((F.locked.ell : K) + 1)

  have hdiag := D.oneFiber_middle_diagonal F Alo Ahi
    hthree houtThree hnot hext
  have hdeg := D.oneFiber_middle_profile_natDegree_eq_k F Alo Ahi
    hthree houtThree hnot hext

  have ha0 : a0 ≠ 0 := by
    dsimp [a0]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb0 : b0 ≠ 0 := by
    dsimp [b0]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hc0 : c0 ≠ 0 := by
    dsimp [c0]
    apply MvPolynomial.mem_support_iff.mp
    rw [F.highest.slice_support_eq]
    simp
  have hd0 : d0 ≠ 0 := by
    dsimp [d0]
    apply MvPolynomial.mem_support_iff.mp
    rw [F.highest.slice_support_eq]
    simp
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hell1K : (F.locked.ell : K) + 1 ≠ 0 := by
    have h : (F.locked.ell + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  have hnK : (F.highest.n : K) ≠ 0 := by
    exact_mod_cast (show F.highest.n ≠ 0 by omega)
  have hn1K : ((F.highest.n - 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (show F.highest.n - 1 ≠ 0 by omega)
  have hcLo : cLo ≠ 0 := by
    dsimp [cLo]
    exact mul_ne_zero ha0 hell1K
  have hdLo : dLo ≠ 0 := by
    dsimp [dLo]
    exact mul_ne_zero hb0 hellK
  have hdHi : dHi ≠ 0 := by
    dsimp [dHi]
    exact mul_ne_zero hd0 hn1K
  have halpha : alpha ≠ 0 := by
    dsimp [alpha]
    exact div_ne_zero (neg_ne_zero.mpr hcLo) hdLo

  have hnorm := F.oneFiber_translatedProfile_eq_middle_twoMode
    Alo Ahi hthree houtThree hext hdiag
  have htrans :
      psi = Polynomial.monomial (Alo.k - 1) u0 +
        Polynomial.monomial Alo.k v0 := by
    simpa [a0, b0, cLo, dLo, alpha, psi, u0, v0] using hnorm.2
  have hpsiNe : psi ≠ 0 := by
    intro hz
    have h0a : u0 = 0 := by
      dsimp [u0]
      rw [hz]
      simp
    have h0b : v0 = 0 := by
      dsimp [v0]
      rw [hz]
      simp
    rcases hnorm.1 with h | h <;> contradiction
  have hpsiDeg : psi.natDegree = Alo.k := by
    calc
      psi.natDegree = Alo.coefficientProfile.natDegree := by
        dsimp [psi, alpha, translatePolynomial]
        rw [Polynomial.natDegree_comp]
        simp
      _ = Alo.k := hdeg
  have hv0 : v0 ≠ 0 := by
    have hm : Alo.k ∈ psi.support := by
      rw [← hpsiDeg]
      exact Polynomial.natDegree_mem_support_of_nonzero hpsiNe
    dsimp [v0]
    exact Polynomial.mem_support_iff.mp hm
  have hv : v ≠ 0 := by
    dsimp [v]
    exact mul_ne_zero (pow_ne_zero _ halpha) hv0

  have hrootLo :
      a0 * ((F.locked.ell : K) + 1) +
        b0 * (F.locked.ell : K) * alpha = 0 := by
    change cLo + dLo * alpha = 0
    dsimp [alpha]
    field_simp [hdLo]
    ring
  have hrootEq := F.oneFiber_endpointRoots_eq
    Alo Ahi hthree houtThree hext
  have halphaHi : alpha = -cHi / dHi := by
    simpa [a0, b0, c0, d0, cLo, dLo, cHi, dHi, alpha] using hrootEq
  have hrootHi :
      c0 * (F.highest.n : K) +
        d0 * ((F.highest.n - 1 : ℕ) : K) * alpha = 0 := by
    change cHi + dHi * alpha = 0
    rw [halphaHi]
    field_simp [hdHi]
    ring
  have hlamHi : lamHi ≠ 0 := by
    dsimp [lamHi]
    exact div_ne_zero (mul_ne_zero hd0 halpha) hnK
  have hlamLo : lamLo ≠ 0 := by
    dsimp [lamLo]
    exact div_ne_zero (mul_ne_zero hb0 halpha) hell1K

  have hwall := Alo.wallSlope_eq hthree houtThree
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hgapNe : F.highest.n - Alo.k ≠ Alo.k - 1 := by
    intro hgap
    have hwallNat :
        (F.highest.n - 1) * Alo.j =
          F.locked.ell * (F.highest.n - Alo.k) := by
      have hn1 : 1 ≤ F.highest.n := by omega
      have hkn : Alo.k ≤ F.highest.n := by omega
      exact_mod_cast hwall
    have hj : Alo.j = Alo.k - 1 := by omega
    rw [hj, hgap] at hwallNat
    have hpos : 0 < Alo.k - 1 := by omega
    have heq : F.highest.n - 1 = F.locked.ell :=
      Nat.eq_of_mul_eq_mul_right hpos hwallNat
    omega
  have hresHi : F.highest.n - 1 ≠ 2 * (F.highest.n - Alo.k) := by
    intro h
    apply hgapNe
    omega
  have hresLo : F.highest.n - 1 ≠ 2 * (Alo.k - 1) := by
    intro h
    apply hgapNe
    omega
  have hqHi : 0 < F.highest.n - Alo.k := by omega
  have hqHiN : F.highest.n - Alo.k < F.highest.n - 1 := by omega
  have hqLo : 0 < Alo.k - 1 := by omega
  have hqLoN : Alo.k - 1 < F.highest.n - 1 := by omega

  have hk3 : 3 ≤ Alo.k := by
    exact middle_oneFiber_k_three_le_of_wall
      F.highest.n_two_le hnell Alo.k_gt_one Alo.k_lt_highest
        (by simpa [hdiag] using hwall)

  let AhiM := highestBinomialMomentHessian F.V F.highest.n c0 d0
  let Bmid := parallelStaircaseMomentHessian F.V Alo.k Alo.j Alo.coefficientProfile
  let AloM := lockedBinomialMomentHessian F.V F.locked.ell a0 b0
  let qHi := F.highest.n - Alo.k
  let qLo := Alo.k - 1
  let N := F.highest.n - 1
  let x := 2 * alpha

  have hmatrix := D.swappedEuler_eq_oneFiberThreeLayerMomentPencil
    F Alo Ahi hthree houtThree hnot hext
  have hdetSwapped : (swappedRankThreeEulerHessian D.family).det = 0 :=
    det_swappedRankThreeEulerHessian_eq_zero_of_hessianDeterminant_eq_zero
      D.family D.hessian_zero
  have hdetOrig :
      (parameterThreeLayerMatrix AhiM Bmid AloM qHi N).det = 0 := by
    have hp : (oneFiberThreeLayerMomentPencil F Alo).det = 0 := by
      rw [← hmatrix]
      exact hdetSwapped
    simpa [AhiM, Bmid, AloM, qHi, N,
      oneFiberThreeLayerMomentPencil, parameterThreeLayerMatrix,
      c0, d0, a0, b0] using hp
  have hdetRefl :
      (parameterThreeLayerMatrix AloM Bmid AhiM qLo N).det = 0 := by
    have hp := D.det_oneFiberReflectedThreeLayerMomentPencil_eq_zero
      F Alo Ahi hthree houtThree hnot hext
    simpa [AhiM, Bmid, AloM, qLo, N,
      oneFiberReflectedThreeLayerMomentPencil, parameterThreeLayerMatrix,
      c0, d0, a0, b0] using hp

  have hzeroHi := snd_snd_det_secondVariationJetMatrix_eval_eq_zero
    x AhiM Bmid AloM qHi N hqHi hqHiN hresHi hdetOrig
  have hzeroLo := snd_snd_det_secondVariationJetMatrix_eval_eq_zero
    x AloM Bmid AhiM qLo N hqLo hqLoN hresLo hdetRefl

  have hEvalHi : evalPolynomialMatrix x AhiM =
      lamHi • highestDoubleRootMomentCore (F.V : K) (F.highest.n : K) := by
    dsimp [x, AhiM]
    exact eval_two_mul_highestBinomialMomentHessian_of_root
      F.V F.highest.n c0 d0 alpha (by omega) hrootHi
  have hEvalLo : evalPolynomialMatrix x AloM =
      lamLo • lockedDoubleRootMomentCore (F.V : K) (F.locked.ell : K) := by
    dsimp [x, AloM]
    exact eval_two_mul_lockedBinomialMomentHessian_of_root
      F.V F.locked.ell a0 b0 alpha F.locked.ell_pos hrootLo
  have hEvalMid : evalPolynomialMatrix x Bmid =
      u • middleLowerDoubleRootMomentCore (F.V : K) (Alo.k : K) +
        v • middleUpperDoubleRootMomentCore (F.V : K) (Alo.k : K) := by
    dsimp [x, Bmid, u, v, u0, v0, psi]
    have h := eval_two_mul_parallelStaircaseMoment_of_translate_eq_middleTwoMode
      F.V Alo.k alpha
        (translatePolynomial alpha Alo.coefficientProfile).coeff (Alo.k - 1)
        (translatePolynomial alpha Alo.coefficientProfile).coeff Alo.k
        Alo.coefficientProfile hk3
        (by simpa [hdiag] using htrans)
    simpa [hdiag] using h

  have hJetHi :
      secondVariationJetMatrix (evalPolynomialMatrix x AhiM)
          (evalPolynomialMatrix x Bmid) 0 =
        middleHighestSecondJet (F.V : K) (F.highest.n : K) (Alo.k : K)
          lamHi u v := by
    rw [hEvalHi, hEvalMid]
    apply Matrix.ext
    intro i j
    simp [secondVariationJetMatrix, secondVariationJetEntry,
      middleHighestSecondJet, middleTwoModeDoubleRootMomentCore]
  have hJetLo :
      secondVariationJetMatrix (evalPolynomialMatrix x AloM)
          (evalPolynomialMatrix x Bmid) 0 =
        middleLockedSecondJet (F.V : K) (F.locked.ell : K) (Alo.k : K)
          lamLo u v := by
    rw [hEvalLo, hEvalMid]
    apply Matrix.ext
    intro i j
    simp [secondVariationJetMatrix, secondVariationJetEntry,
      middleLockedSecondJet, middleTwoModeDoubleRootMomentCore]

  rw [hJetHi, snd_snd_det_middleHighestSecondJet] at hzeroHi
  rw [hJetLo, snd_snd_det_middleLockedSecondJet] at hzeroLo

  by_contra hu
  have hu' : u ≠ 0 := hu
  have hV : (F.V : K) ≠ 0 := by exact_mod_cast (show F.V ≠ 0 by omega)
  have hV1 : (F.V : K) + 1 ≠ 0 := by
    have h : F.V + 1 ≠ 0 := by omega
    exact_mod_cast h
  have hn1 : (F.highest.n : K) - 1 ≠ 0 := by
    intro hz
    have : (F.highest.n : K) = 1 := sub_eq_zero.mp hz
    have : F.highest.n = 1 := by exact_mod_cast this
    omega
  have hk1 : (Alo.k : K) - 1 ≠ 0 := by
    intro hz
    have : (Alo.k : K) = 1 := sub_eq_zero.mp hz
    have : Alo.k = 1 := by exact_mod_cast this
    omega
  have h8 : (8 : K) ≠ 0 := by norm_num

  have hEH :
      (((Alo.k : K) * (F.highest.n : K) + (Alo.k : K) -
          (F.highest.n : K) - 3) * u + 2 * (Alo.k : K) * v) = 0 := by
    simpa [h8, hV, hV1, hlamHi, hnK, hn1, hk1, hu'] using hzeroHi
  have hEL :
      (((F.locked.ell : K) * (Alo.k : K) - (F.locked.ell : K) +
          2 * (Alo.k : K) - 4) * u + 2 * (Alo.k : K) * v) = 0 := by
    simpa [h8, hV, hV1, hlamLo, hellK, hell1K, hk1, hu'] using hzeroLo

  have hfactor :
      (((Alo.k : K) - 1) *
        ((F.highest.n : K) - (F.locked.ell : K) - 1)) * u = 0 := by
    linear_combination hEH - hEL
  have hfactor0 :
      ((Alo.k : K) - 1) *
        ((F.highest.n : K) - (F.locked.ell : K) - 1) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hu'
  have hsepFactor :
      (F.highest.n : K) - (F.locked.ell : K) - 1 = 0 :=
    (mul_eq_zero.mp hfactor0).resolve_left hk1
  have heqK : (F.highest.n : K) = (F.locked.ell : K) + 1 := by
    linarith
  have heqNat : F.highest.n = F.locked.ell + 1 := by
    exact_mod_cast heqK
  exact (Nat.ne_of_lt (F.highest_n_lt_locked_height hthree houtThree)) heqNat

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
