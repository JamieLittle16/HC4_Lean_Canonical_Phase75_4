import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberSecondJet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberLeading
import HC4.Polynomial.FiniteStaircaseEndpointMomentDegree
import HC4.Polynomial.FiniteStaircasePureModeSecondVariation
import Mathlib.Tactic

/-!
# A19 upper pure unit one-fibre diagonal is impossible

On the unit upper diagonal `j=k`, the common honest profile has degree exactly
`k`.  The exact three-layer pair-Rees pencil and generic second parameter-gap
jet isolate the highest/interior second variation, whose top longitudinal
coefficient is a product of nonzero source and arithmetic factors.
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

/-- Upper unit one-fibre elimination. -/
theorem unitLeft_oneFiber_upper_diagonal_impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j = Alo.k) : False := by
  let q := F.highest.n - Alo.k
  let c : K := MvPolynomial.coeff F.highest.e0 S.slice
  let d : K := MvPolynomial.coeff F.highest.e1 S.slice
  let u : K := Alo.coefficientProfile.coeff Alo.k
  let A := highestBinomialMomentHessian 1 F.highest.n c d
  let B := parallelStaircaseMomentHessian 1 Alo.k Alo.j Alo.coefficientProfile
  let C2 := unitLeftOneFiberSecondOrderMomentMatrix F Alo
  let M := unitLeftOneFiberThreeLayerMomentPencil F Alo

  have hqpos : 0 < q := by dsimp [q]; omega
  have hqterminal : q < F.highest.n - 1 := by dsimp [q]; omega

  have hdetM : M.det = 0 := by
    have hmatrix := D.swappedEuler_eq_unitLeftOneFiberThreeLayerMomentPencil
      F Alo Ahi hthree houtThree hnot hext
    have hdet :=
      det_swappedRankThreeLineSpecialisedEulerHessian_eq_zero_of_hessian_zero
        D.family D.hessian_zero
    rw [hmatrix] at hdet
    simpa [M] using hdet

  have hgap : ∀ i j, HasNoPositiveParameterCoeffBelow q (M i j) := by
    intro i j
    simpa [q, M] using unitLeftOneFiberThreeLayerMomentPencil_hasGap F Alo i j

  have hsecond := snd_snd_det_matrixParameterGapSecondJet
    (R := Polynomial K) hqpos M hgap
  rw [hdetM] at hsecond
  simp only [Polynomial.coeff_zero, mul_zero] at hsecond

  have hjet := matrixParameterGapSecondJet_unitLeftOneFiberThreeLayer
    (K := K) F Alo
  change matrixParameterGapSecondJet (R := Polynomial K) hqpos M hgap =
      secondVariationJetMatrix A B C2 at hjet
  rw [hjet] at hsecond
  have hsecondZero :
      TrivSqZeroExt.snd (TrivSqZeroExt.snd
        (secondVariationJetMatrix A B C2).det) = 0 := by
    exact hsecond

  have hAdeg : ∀ i j, (A i j).natDegree ≤ 1 := by
    intro i j
    dsimp [A, c, d]
    exact highestBinomialMomentHessian_natDegree_le_one
      1 F.highest.n _ _ i j

  have hprofileDeg := F.oneFiber_upper_profile_natDegree_eq
    Alo Ahi hthree houtThree hext hdiag
  have hBdeg : ∀ i j, (B i j).natDegree ≤ Alo.k := by
    intro i j
    dsimp [B]
    calc
      (parallelStaircaseMomentHessian 1 Alo.k Alo.j
        Alo.coefficientProfile i j).natDegree ≤
          Alo.coefficientProfile.natDegree :=
        parallelStaircaseMomentHessian_natDegree_le
          1 Alo.k Alo.j Alo.coefficientProfile i j
      _ = Alo.k := hprofileDeg

  have hCdeg : ∀ i j, (C2 i j).natDegree ≤ 1 := by
    intro i j
    have h2q0 : 2 * q ≠ 0 := by omega
    have h2qq : 2 * q ≠ q := by omega
    by_cases hres : 2 * q = F.highest.n - 1
    · have hCeq :
          C2 i j =
            lockedBinomialMomentHessian 1 F.locked.ell
              (MvPolynomial.coeff C.ray.facetExponent P.carrier)
              (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j := by
        dsimp [C2, unitLeftOneFiberSecondOrderMomentMatrix, M, q] at *
        simp [unitLeftOneFiberThreeLayerMomentPencil, h2q0, h2qq, hres]
      rw [hCeq]
      exact lockedBinomialMomentHessian_natDegree_le_one
        1 F.locked.ell _ _ i j
    · have hCeq : C2 i j = 0 := by
        dsimp [C2, unitLeftOneFiberSecondOrderMomentMatrix, M, q] at *
        simp [unitLeftOneFiberThreeLayerMomentPencil, h2q0, h2qq, hres]
      rw [hCeq]
      simp

  have htop := coeff_top_snd_snd_det_secondVariationJetMatrix
    A B C2 Alo.k (by omega) hAdeg hBdeg hCdeg
  rw [hsecondZero] at htop
  simp only [Polynomial.coeff_zero] at htop
  have htopZero :
      TrivSqZeroExt.snd (TrivSqZeroExt.snd
        (secondVariationTopMatrix A B Alo.k).det) = 0 := htop.symm

  have hAcoeff := coeff_one_highestBinomialMomentHessian
    1 F.highest.n c d
  have hBcoeff := F.oneFiber_upper_moment_top_coeff Alo hdiag
  have hTopMatrix :
      secondVariationTopMatrix A B Alo.k =
        highestUpperPureModeSecondJet
          (1 : K) (F.highest.n : K) (Alo.k : K) d u := by
    apply Matrix.ext
    intro i j
    have hAi := congrFun (congrFun hAcoeff i) j
    have hBi := congrFun (congrFun hBcoeff i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hAi hBi
    simp [secondVariationTopMatrix, secondVariationTopEntry,
      highestUpperPureModeSecondJet, A, B, u]
    rw [hAi, hBi]

  rw [hTopMatrix] at htopZero
  rw [snd_snd_det_highestUpperPureModeSecondJet] at htopZero

  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hd : d ≠ 0 := by
    dsimp [d]
    exact MvPolynomial.mem_support_iff.mp he1S
  have hu : u ≠ 0 := by
    dsimp [u]
    exact F.oneFiber_upper_profile_top_ne_zero
      Alo Ahi hthree houtThree hext hdiag
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hV : (1 : K) ≠ 0 := by norm_num
  have hV1 : (1 : K) + 1 ≠ 0 := by norm_num
  have hn1 : (F.highest.n : K) - 1 ≠ 0 := by
    intro hz
    have hz' : (F.highest.n : K) = 1 := sub_eq_zero.mp hz
    have hn : F.highest.n = 1 := by exact_mod_cast hz'
    omega
  have hk : (Alo.k : K) ≠ 0 := by
    exact_mod_cast (show Alo.k ≠ 0 by omega)
  have hn2 : (F.highest.n : K) - 2 ≠ 0 := by
    intro hz
    have hz' : (F.highest.n : K) = 2 := by linear_combination hz
    have hn : F.highest.n = 2 := by exact_mod_cast hz'
    omega

  have h0 : (2 : K) * (1 : K) ≠ 0 := mul_ne_zero htwo hV
  have h1 : (2 : K) * (1 : K) * ((1 : K) + 1) ≠ 0 :=
    mul_ne_zero h0 hV1
  have h2 :
      (2 : K) * (1 : K) * ((1 : K) + 1) *
        ((F.highest.n : K) - 1) ^ 2 ≠ 0 :=
    mul_ne_zero h1 (pow_ne_zero 2 hn1)
  have h3 :
      (2 : K) * (1 : K) * ((1 : K) + 1) *
        ((F.highest.n : K) - 1) ^ 2 * (Alo.k : K) ^ 2 ≠ 0 :=
    mul_ne_zero h2 (pow_ne_zero 2 hk)
  have h4 :
      (2 : K) * (1 : K) * ((1 : K) + 1) *
        ((F.highest.n : K) - 1) ^ 2 * (Alo.k : K) ^ 2 *
        ((F.highest.n : K) - 2) ≠ 0 :=
    mul_ne_zero h3 hn2
  have h5 :
      (2 : K) * (1 : K) * ((1 : K) + 1) *
        ((F.highest.n : K) - 1) ^ 2 * (Alo.k : K) ^ 2 *
        ((F.highest.n : K) - 2) * d ^ 2 ≠ 0 :=
    mul_ne_zero h4 (pow_ne_zero 2 hd)
  have h6 :
      (2 : K) * (1 : K) * ((1 : K) + 1) *
        ((F.highest.n : K) - 1) ^ 2 * (Alo.k : K) ^ 2 *
        ((F.highest.n : K) - 2) * d ^ 2 * u ^ 2 ≠ 0 :=
    mul_ne_zero h5 (pow_ne_zero 2 hu)
  exact h6 htopZero

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
