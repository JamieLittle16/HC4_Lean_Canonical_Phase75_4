import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveSlopeKernelFree
import HC4.Valuation.PrimitiveSmithEndpoint
import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSoundEpisodeInterface
import Mathlib.Tactic

/-!
# A18.4.42: no-wall Smith loss is a same-scale descent

The factor-20 no-wall primitive endpoint is not used recursively here.  If
`m` is the least parameter order on the zero Smith grade, the equal-slope
integral Smith move `(m,m)` already exists on the incoming family itself.
After that move every coefficient has a common factor `X^m`; extracting it
changes the exact Hessian clock from `Delta` to `Delta - 4*m` at the same
literal parameter scale.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Equal Smith slopes contribute exactly the expected monomial parameter
power to each source coefficient. -/
theorem smithConformalCoefficientFactor_same
    (m : ℕ) (d : Fin 4 →₀ ℕ) :
    smithConformalCoefficientFactor (K := K) m m d =
      Polynomial.X ^ smithConformalRawExponent m m d := by
  rw [show smithConformalCoefficientFactor (K := K) m m d =
      ∏ i : Fin 4, Polynomial.X ^
        (smithConformalSourceExponent m m i * d i) by
    unfold smithConformalCoefficientFactor
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul]
    rfl]
  rw [Fin.prod_univ_four]
  simp [smithConformalSourceExponent, smithConformalRawExponent,
    ← pow_add]

/-- Cancel `X^a` from a stronger divisibility `X^(a+b) ∣ X^a*q`. -/
theorem polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
    (a b : ℕ) (q : Polynomial K)
    (h : (Polynomial.X ^ (a + b) : Polynomial K) ∣
      Polynomial.X ^ a * q) :
    (Polynomial.X ^ b : Polynomial K) ∣ q := by
  rcases h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have heq :
      Polynomial.X ^ a * q =
        Polynomial.X ^ a * (Polynomial.X ^ b * r) := by
    calc
      Polynomial.X ^ a * q = Polynomial.X ^ (a + b) * r := hr
      _ = Polynomial.X ^ a * (Polynomial.X ^ b * r) := by
        rw [pow_add]
        ring
  exact mul_left_cancel₀ (pow_ne_zero a Polynomial.X_ne_zero) heq

/-- Nonnegative canonical Smith grade already makes the equal-slope move
integral on the unramified incoming family. -/
theorem noWall_unramifiedSmith_coefficientDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone : ¬ HasAlignedSmithGenuineWall P a b)
    (m : ℕ) :
    HasIntegralSmithConformalCoefficientDivisibility m m P := by
  intro d hd
  have hnonneg :=
    no_negativeSmithDerivative_of_noGenuineWall P a b hnone d hd
  have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
  have hraw4 : 4 ≤ smithConformalRawExponent 2 2 d := by
    rw [hrel] at hnonneg
    exact_mod_cast (by omega :
      (4 : ℤ) ≤ (smithConformalRawExponent 2 2 d : ℤ))
  have hraw : 2 * m ≤ smithConformalRawExponent m m d := by
    unfold smithConformalRawExponent at hraw4 ⊢
    nlinarith
  rw [smithConformalCoefficientFactor_same]
  unfold smithConformalMultiplier smithConformalMultiplierExponent
  exact dvd_mul_of_dvd_left
    (polynomial_X_pow_dvd_X_pow_of_le
      (K := K) (m + m) _ (by omega)) _

/-- After the direct equal-slope move, the least zero-grade coefficient order
is still a common parameter factor of the whole normalised family. -/
theorem noWall_unramifiedSmith_commonFactor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hnone : ¬ HasAlignedSmithGenuineWall P a b)
    (hne : (zeroSmithSourceSupport P).Nonempty) :
    let m := minimalZeroSmithParameterOrder P hne
    let hsmith := noWall_unramifiedSmith_coefficientDivisibility
      (K := K) P a b hnone m
    HasCommonParameterFactor m
      (integralSmithConformalFamily m m P hsmith) := by
  dsimp only
  let m := minimalZeroSmithParameterOrder P hne
  let hsmith := noWall_unramifiedSmith_coefficientDivisibility
    (K := K) P a b hnone m
  let Q := integralSmithConformalFamily m m P hsmith
  intro d hdQ
  have hdP : d ∈ P.support :=
    support_integralSmithConformalFamily_subset m m P hsmith hdQ
  have hnonneg :=
    no_negativeSmithDerivative_of_noGenuineWall P a b hnone d hdP
  let v := smithFamilyCoefficientOrder P d
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdP
  have hv :
      v = polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_eq P hdP
  have hvdvd :
      (Polynomial.X ^ v : Polynomial K) ∣ MvPolynomial.coeff d P := by
    rw [hv]
    exact polynomialParameterOrder_dvd _ hcoeffne
  have hresidual :
      3 * m ≤ smithConformalRawExponent m m d + v := by
    by_cases hz : smithSeparatorDelta 1 1 (smithAxisProjection d) = 0
    · have hd0 : d ∈ zeroSmithSourceSupport P :=
        (mem_zeroSmithSourceSupport P).2 ⟨hdP, hz⟩
      have hmle : m ≤ v := minimalZeroSmithParameterOrder_le P hne hd0
      have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
      rw [hz] at hrel
      have hraw4 : smithConformalRawExponent 2 2 d = 4 := by
        exact_mod_cast (by omega :
          (smithConformalRawExponent 2 2 d : ℤ) = 4)
      unfold smithConformalRawExponent at hraw4 ⊢
      nlinarith
    · have hpos :=
        smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
          (smithAxisProjection d) hnonneg hz
      have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
      rw [hrel] at hpos
      have hraw6 : 6 ≤ smithConformalRawExponent 2 2 d := by
        exact_mod_cast (by omega :
          (6 : ℤ) ≤ (smithConformalRawExponent 2 2 d : ℤ))
      unfold smithConformalRawExponent at hraw6 ⊢
      nlinarith
  have hfactor := smithConformalCoefficientFactor_same (K := K) m d
  have htotal :
      (Polynomial.X ^
          (smithConformalRawExponent m m d + v) : Polynomial K) ∣
        smithConformalCoefficientFactor (K := K) m m d *
          MvPolynomial.coeff d P := by
    rcases hvdvd with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [hfactor, hr, pow_add]
    ring
  have hstrong :
      (Polynomial.X ^ (3 * m) : Polynomial K) ∣
        smithConformalCoefficientFactor (K := K) m m d *
          MvPolynomial.coeff d P :=
    dvd_trans
      (polynomial_X_pow_dvd_X_pow_of_le
        (K := K) (3 * m)
        (smithConformalRawExponent m m d + v) hresidual)
      htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem m m P hsmith hdP
  have hq :
      MvPolynomial.coeff d Q =
        smithConformalCoefficientQuotient m m P hsmith d := by
    dsimp [Q]
    exact coeff_integralSmithConformalFamily_of_mem m m P hsmith hdP
  rw [hq]
  apply polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
      (K := K) (2 * m) m
      (smithConformalCoefficientQuotient m m P hsmith d)
  have hmult :
      smithConformalMultiplier (K := K) m m = Polynomial.X ^ (2 * m) := by
    unfold smithConformalMultiplier smithConformalMultiplierExponent
    congr 1
    omega
  rw [show 2 * m + m = 3 * m by omega]
  rw [← hmult, ← hspec]
  exact hstrong

/-- No-wall marked sections are axial, hence the direct equal-slope Smith
normalisation leaves them literally unchanged. -/
theorem integralSmithConformalSection_eq_of_noWall
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b c : Fin 4 → Polynomial K)
    (hnone : ¬ HasAlignedSmithGenuineWall P a b)
    (hc : c = a ∨ c = b)
    (m : ℕ)
    (hdiv : HasIntegralSmithConformalSectionDivisibility m m c) :
    integralSmithConformalSection m m c hdiv = c := by
  have hinflate :=
    smithConformalInflateSection_integralSection_eq m m c hdiv
  funext i
  fin_cases i
  · simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient, smithConformalSourceExponent]
      using congrFun hinflate (0 : Fin 4)
  · have hz : c (1 : Fin 4) = 0 := by
      rcases hc with rfl | rfl
      · exact leftTransverse_zero_of_noGenuineWall P a b hnone 1 (by decide)
      · exact rightTransverse_zero_of_noGenuineWall P a b hnone 1 (by decide)
    rw [hz]
    have hi := congrFun hinflate (1 : Fin 4)
    rw [hz] at hi
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient, smithConformalSourceExponent] using
      (mul_eq_zero.mp hi).resolve_left
        (pow_ne_zero m Polynomial.X_ne_zero)
  · have hz : c (2 : Fin 4) = 0 := by
      rcases hc with rfl | rfl
      · exact leftTransverse_zero_of_noGenuineWall P a b hnone 2 (by decide)
      · exact rightTransverse_zero_of_noGenuineWall P a b hnone 2 (by decide)
    rw [hz]
    have hi := congrFun hinflate (2 : Fin 4)
    rw [hz] at hi
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient, smithConformalSourceExponent] using
      (mul_eq_zero.mp hi).resolve_left
        (pow_ne_zero m Polynomial.X_ne_zero)
  · have hz : c (3 : Fin 4) = 0 := by
      rcases hc with rfl | rfl
      · exact leftTransverse_zero_of_noGenuineWall P a b hnone 3 (by decide)
      · exact rightTransverse_zero_of_noGenuineWall P a b hnone 3 (by decide)
    rw [hz]
    have hi := congrFun hinflate (3 : Fin 4)
    rw [hz] at hi
    simpa [smithConformalInflateSection,
      smithConformalDerivativeCoefficient, smithConformalSourceExponent] using
      (mul_eq_zero.mp hi).resolve_left
        (pow_ne_zero (m + m) Polynomial.X_ne_zero)

/-- The strict no-wall primitive clock loss admits an actual successor on the
incoming scale. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_sameScaleNoWallSmithSuccessor
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K)) s.movingSection)
    (hmpos :
      0 < minimalZeroSmithParameterOrder
        (zeroJetNormalizedFamily s.family)
        (zeroSmithSourceSupport_nonempty_of_noGenuineWall
          (zeroJetNormalizedFamily s.family)
          (zeroPolynomialSection (K := K)) s.movingSection
          s.rawDefect s.normalized_hessianDefect hnone)) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedSameScaleEpisodeProgress RR target s := by
  let P := zeroJetNormalizedFamily s.family
  let a := zeroPolynomialSection (K := K)
  let b := s.movingSection
  let hne := zeroSmithSourceSupport_nonempty_of_noGenuineWall
    P a b s.rawDefect s.normalized_hessianDefect hnone
  let m := minimalZeroSmithParameterOrder P hne
  have hm : 0 < m := by simpa [P, a, b, hne, m] using hmpos
  let hsmith := noWall_unramifiedSmith_coefficientDivisibility
    (K := K) P a b hnone m
  let Q := integralSmithConformalFamily m m P hsmith
  let hcommon := noWall_unramifiedSmith_commonFactor
    (K := K) P a b s.rawDefect s.normalized_hessianDefect hnone hne
  let T := commonParameterFactorFamily m Q hcommon

  have hQdef : HasPolynomialFamilyHessianDefect (K := K) Q s.rawDefect := by
    dsimp [Q]
    exact integralSmithConformalFamily_preservesHessianDefect
      m m s.rawDefect P hsmith s.normalized_hessianDefect
  have hTdef : HasPolynomialFamilyHessianDefect
      (K := K) T (s.rawDefect - 4 * m) := by
    dsimp [T]
    exact commonParameterFactor_hasHessianDefect_sub_four_mul
      m Q hcommon s.rawDefect hQdef
  have hcost : 4 * m ≤ s.rawDefect :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) m Q hcommon s.rawDefect hQdef

  have hQdegree : NonlinearDegreeBound s.degreeCap Q := by
    dsimp [Q]
    exact nonlinearDegreeBound_integralSmithConformal
      s.degreeCap m m P s.normalized_nonlinearDegreeBound hsmith
  have hTdegree : NonlinearDegreeBound s.degreeCap T := by
    apply nonlinearDegreeBound_of_support_subset hQdegree
    exact support_commonParameterFactorFamily_subset m Q hcommon

  have hadiv : HasIntegralSmithConformalSectionDivisibility m m a := by
    intro i
    simp [a, zeroPolynomialSection]
  have hbdiv : HasIntegralSmithConformalSectionDivisibility m m b := by
    intro i
    fin_cases i
    · simp [smithConformalDerivativeCoefficient, smithConformalSourceExponent]
    · rw [rightTransverse_zero_of_noGenuineWall P a b hnone 1 (by decide)]
      exact dvd_zero _
    · rw [rightTransverse_zero_of_noGenuineWall P a b hnone 2 (by decide)]
      exact dvd_zero _
    · rw [rightTransverse_zero_of_noGenuineWall P a b hnone 3 (by decide)]
      exact dvd_zero _
  have haeq : integralSmithConformalSection m m a hadiv = a :=
    integralSmithConformalSection_eq_of_noWall P a b a hnone (Or.inl rfl) m hadiv
  have hbeq : integralSmithConformalSection m m b hbdiv = b :=
    integralSmithConformalSection_eq_of_noWall P a b b hnone (Or.inr rfl) m hbdiv
  have hQcoll : HasPolynomialFamilyExactGradientCollision Q a b := by
    have h := polynomialFamilyExactGradientCollision_integralSmithConformal
      m m P hsmith a b hadiv hbdiv s.normalized_exactCollision
    rwa [haeq, hbeq] at h
  have hTcoll : HasPolynomialFamilyExactGradientCollision T a b := by
    dsimp [T]
    exact polynomialFamilyExactGradientCollision_commonParameterFactor
      m Q hcommon a b hQcoll

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) := {
    rawDefect := s.rawDefect - 4 * m
    scale := s.scale
    scale_pos := s.scale_pos
    degreeCap := s.degreeCap
    sourceComplexity := s.sourceComplexity
    repair := s.repair
    family := T
    movingSection := b
    hessianDefect := hTdef
    nonlinearDegreeBound := hTdegree
    exactCollision := by simpa [a] using hTcoll
    sectionSpecial := by simpa [b] using s.sectionSpecial
  }
  refine ⟨target, ?_⟩
  apply certifiedSameScaleEpisodeProgress_of_rawDefect_lt (K := K) RR
  · rfl
  · change s.rawDefect - 4 * m < s.rawDefect
    omega

end

end HC4.Valuation
