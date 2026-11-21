import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseLowerHull
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseLowerHullExposure
import HC4.Newton.FiniteSupportExposedVertex
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# Source-honest lower-hull exposure for the unit finite staircase

The unit lower-hull package already retains a positive supporting inequality in
the literal source deficits `(e₁,e₂)`.  Its exact maximal initial face is
singular.  If that face did not reach the opposite coordinate roof `e₂=0`, two
coordinate-max refinements would isolate a monomial with all four coordinates
positive, contradicting the nonvanishing Hessian determinant of such a
monomial.

The only unit-specific change from the verified nonunit argument is simpler:
when `d₀,d₁,d₂>0`, the unit staircase equation itself rules out `d₃=0`.
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

/-- **Central point or honest exposed cross-roof lower face in the unit case.** -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.central_or_exposed_crossRoof
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ c ∈ P.carrier.support, c 1 = 0 ∧ c 2 = 0) ∨
      ∃ A B : ℕ, ∃ b z : Fin 4 →₀ ℕ,
        0 < A ∧ 0 < B ∧
        b ∈ P.carrier.support ∧ b 1 = 0 ∧ 0 < b 2 ∧
        z ∈ P.carrier.support ∧ 0 < z 1 ∧ z 2 = 0 ∧
        HC4.Polynomial.IsWeightLE
          (finiteStaircaseLowerHullWeight A B)
          (finiteStaircaseLowerHullLevel B (b 2)) P.carrier ∧
        b ∈ (HC4.Polynomial.initialForm
          (finiteStaircaseLowerHullWeight A B)
          (finiteStaircaseLowerHullLevel B (b 2)) P.carrier).support ∧
        z ∈ (HC4.Polynomial.initialForm
          (finiteStaircaseLowerHullWeight A B)
          (finiteStaircaseLowerHullLevel B (b 2)) P.carrier).support ∧
        HC4.Polynomial.hessianDeterminant
          (HC4.Polynomial.initialForm
            (finiteStaircaseLowerHullWeight A B)
            (finiteStaircaseLowerHullLevel B (b 2)) P.carrier) = 0 := by
  classical

  rcases F.central_or_lowerHull hthree houtThree with hcentral | ⟨L⟩
  · exact Or.inl hcentral

  let b : Fin 4 →₀ ℕ := L.lo
  let a : Fin 4 →₀ ℕ := L.edge
  have hbP : b ∈ P.carrier.support := by simpa [b] using L.lo_mem
  have haP : a ∈ P.carrier.support := by simpa [a] using L.edge_mem
  have hb1 : b 1 = 0 := by simpa [b] using L.lo_one_zero
  have hb2pos : 0 < b 2 := by simpa [b] using L.lo_two_pos
  have ha1pos : 0 < a 1 := by simpa [a] using L.edge_one_pos
  have ha2lt : a 2 < b 2 := by simpa [a, b] using L.edge_two_lt

  let A : ℕ := b 2 - a 2
  let B : ℕ := a 1
  have hA : 0 < A := by
    dsimp [A]
    omega
  have hB : 0 < B := by simpa [B] using ha1pos
  have hAK : (A : ℤ) = (b 2 : ℤ) - (a 2 : ℤ) := by
    dsimp [A]
    rw [Nat.cast_sub (Nat.le_of_lt ha2lt)]
  have hBK : (B : ℤ) = (a 1 : ℤ) := by rfl

  let w := finiteStaircaseLowerHullWeight A B
  let level := finiteStaircaseLowerHullLevel B (b 2)
  let G := HC4.Polynomial.initialForm w level P.carrier

  have hbound : HC4.Polynomial.IsWeightLE w level P.carrier := by
    intro x hxP
    have hx := L.lower_bound x hxP
    change
      Finsupp.weight (finiteStaircaseLowerHullWeight A B) x ≤
        finiteStaircaseLowerHullLevel B (b 2)
    rw [weight_finiteStaircaseLowerHullWeight]
    dsimp [finiteStaircaseLowerHullLevel]
    have hx' :
        (B : ℤ) * (b 2 : ℤ) ≤
          (A : ℤ) * (x 1 : ℤ) + (B : ℤ) * (x 2 : ℤ) := by
      rw [hAK, hBK]
      simpa [a, b] using hx
    linarith

  have hbLevel : Finsupp.weight w b = level := by
    dsimp [w, level, finiteStaircaseLowerHullLevel]
    rw [weight_finiteStaircaseLowerHullWeight, hb1]
    simp

  have haLevel : Finsupp.weight w a = level := by
    dsimp [w, level, finiteStaircaseLowerHullLevel]
    rw [weight_finiteStaircaseLowerHullWeight, hAK, hBK]
    ring

  have hbG : b ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [G]
    rw [HC4.Polynomial.coeff_initialForm, if_pos hbLevel]
    exact MvPolynomial.mem_support_iff.mp hbP

  have haG : a ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [G]
    rw [HC4.Polynomial.coeff_initialForm, if_pos haLevel]
    exact MvPolynomial.mem_support_iff.mp haP

  have hGzero : HC4.Polynomial.hessianDeterminant G = 0 := by
    dsimp [G]
    exact HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
      w level P.carrier hbound P.hessian_zero

  have hGne : G ≠ 0 := MvPolynomial.support_nonempty.mp ⟨b, hbG⟩

  rcases F.locked_yRoof_mem with
    ⟨hLmem, _hL0, hL1, hL2, _hL3⟩
  rcases F.highest_zRoof_mem with
    ⟨hHmem, _hH0, hH1, hH2, _hH3⟩

  have hz : ∃ z ∈ G.support, z 2 = 0 := by
    by_contra hnoz
    push_neg at hnoz

    let D1 := HC4.Newton.coordinateMaxInitialData G hGne (1 : Fin 4)
    have hD1zero : HC4.Polynomial.hessianDeterminant D1.face = 0 :=
      D1.hessian_zero hGzero
    let D2 := HC4.Newton.coordinateMaxInitialData
      D1.face D1.face_ne_zero (2 : Fin 4)
    have hD2zero : HC4.Polynomial.hessianDeterminant D2.face = 0 :=
      D2.hessian_zero hD1zero

    let d := D2.witness
    have hdD1 : d ∈ D1.face.support := D2.witness_mem
    have hdG : d ∈ G.support := D1.support_subset hdD1
    have hdP : d ∈ P.carrier.support := by
      dsimp [G] at hdG
      exact HC4.Polynomial.support_initialForm_subset w level P.carrier hdG

    have ha1le : a 1 ≤ D1.level := D1.maximal a haG
    have hd1eq : d 1 = D1.level := D1.coordinate_eq d hdD1
    have hd1pos : 0 < d 1 := by omega
    have hd2pos : 0 < d 2 := by
      have hd2ne : d 2 ≠ 0 := hnoz d hdG
      exact Nat.pos_of_ne_zero hd2ne

    have hdLevel : Finsupp.weight w d = level := by
      have hhom := HC4.Polynomial.initialForm_isWeightedHomogeneous
        w level P.carrier
      exact hhom (MvPolynomial.mem_support_iff.mp hdG)

    have hLbound := hbound hLmem
    have hHbound := hbound hHmem
    have hlockedMin :
        A * d 1 + B * d 2 ≤ B * F.locked.ell := by
      dsimp [w, level, finiteStaircaseLowerHullLevel] at hdLevel hLbound
      rw [weight_finiteStaircaseLowerHullWeight] at hdLevel hLbound
      rw [hL1, hL2] at hLbound
      push_cast at hdLevel hLbound
      nlinarith only [hdLevel, hLbound]
    have hhighestMin :
        A * d 1 + B * d 2 ≤ A * (F.highest.n - 1) := by
      dsimp [w, level, finiteStaircaseLowerHullLevel] at hdLevel hHbound
      rw [weight_finiteStaircaseLowerHullWeight] at hdLevel hHbound
      rw [hH1, hH2] at hHbound
      push_cast at hdLevel hHbound
      nlinarith only [hdLevel, hHbound]

    have hd0pos : 0 < d 0 := by
      by_contra hnot
      have hd0 : d 0 = 0 := Nat.eq_zero_of_not_pos hnot
      have hwall0 := F.support_deficit_wall hthree houtThree hdP
      rw [hd0] at hwall0
      norm_num at hwall0
      have hwall :
          ((F.highest.n : ℤ) - 1) * ((d 2 : ℤ) - 1) =
            (F.locked.ell : ℤ) *
              ((F.highest.n : ℤ) - (d 1 : ℤ)) := by
        nlinarith only [hwall0]
      exact HC4.Polynomial.zeroLongitudinal_not_positive_lowerHull
        F.highest.n_two_le F.locked.ell_pos hd1pos hd2pos hA hB
        hwall
        (by exact_mod_cast hlockedMin)
        (by
          have hn1 : 1 ≤ F.highest.n := by omega
          exact_mod_cast hhighestMin)

    have hd3pos : 0 < d 3 := by
      have hcurve := (F.support_staircase_equations hthree houtThree hdP).2
      simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
        HC4.Polynomial.rankThreeQuotientCoordinate_pair,
        HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
        one_mul] at hcurve
      push_cast at hcurve
      by_contra hnot
      have hd3 : d 3 = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hd3] at hcurve
      norm_num at hcurve
      have hd0Z : (0 : ℤ) < (d 0 : ℤ) := by exact_mod_cast hd0pos
      have hd1Z : (0 : ℤ) < (d 1 : ℤ) := by exact_mod_cast hd1pos
      have hd2Z : (0 : ℤ) < (d 2 : ℤ) := by exact_mod_cast hd2pos
      nlinarith only [hcurve, hd0Z, hd1Z, hd2Z]

    have hd2face : ∀ q ∈ D2.face.support, q = d := by
      intro q hq
      have hqD1 : q ∈ D1.face.support := D2.support_subset hq
      have hq1 : q 1 = d 1 := by
        exact (D1.coordinate_eq q hqD1).trans hd1eq.symm
      have hd2eq : d 2 = D2.level := by
        simpa [d] using D2.witness_coordinate
      have hq2 : q 2 = d 2 := by
        exact (D2.coordinate_eq q hq).trans hd2eq.symm
      have hqG : q ∈ G.support := D1.support_subset hqD1
      have hqP : q ∈ P.carrier.support := by
        dsimp [G] at hqG
        exact HC4.Polynomial.support_initialForm_subset w level P.carrier hqG
      exact F.support_eq_of_deficits_eq hthree houtThree hqP hdP hq1 hq2

    let c : K := MvPolynomial.coeff d D2.face
    have hc : c ≠ 0 := by
      dsimp [c]
      have hcoeff :
          MvPolynomial.coeff d D2.face = MvPolynomial.coeff d D1.face := by
        rw [D2.face_eq, HC4.Polynomial.coeff_initialForm,
          HC4.Newton.weight_coordinateMaxWeight]
        have hd2coord : d (2 : Fin 4) = D2.level := by
          simpa [d] using D2.witness_coordinate
        simp [hd2coord]
      rw [hcoeff]
      exact MvPolynomial.mem_support_iff.mp D2.witness_mem

    have hmono : D2.face = MvPolynomial.monomial d c := by
      apply MvPolynomial.ext
      intro q
      by_cases hqd : q = d
      · subst q
        simp [c]
      · have hqzero : MvPolynomial.coeff q D2.face = 0 := by
          by_contra hne
          have hqs : q ∈ D2.face.support :=
            MvPolynomial.mem_support_iff.mpr hne
          exact hqd (hd2face q hqs)
        have hdq : d ≠ q := by intro h; exact hqd h.symm
        rw [hqzero]
        simp [hdq]

    have hpos : ∀ i : Fin 4, 0 < d i := by
      intro i
      fin_cases i
      · exact hd0pos
      · exact hd1pos
      · exact hd2pos
      · exact hd3pos
    have hdeg3 : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
      simp [HC4.Polynomial.ordinaryDegree4]
      omega
    have hne := HC4.Polynomial.hessianDeterminant_monomial_ne_zero
      hc hpos hdeg3
    rw [hmono] at hD2zero
    exact hne hD2zero

  rcases hz with ⟨z, hzG, hz2⟩
  have hzP : z ∈ P.carrier.support := by
    dsimp [G] at hzG
    exact HC4.Polynomial.support_initialForm_subset w level P.carrier hzG
  have hz1pos : 0 < z 1 := by
    by_contra hnot
    have hz1 : z 1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hzbound := L.lower_bound z hzP
    rw [hz1, hz2] at hzbound
    norm_num at hzbound
    have hposprod : (0 : ℤ) < (L.edge 1 : ℤ) * (L.lo 2 : ℤ) := by
      exact mul_pos (by exact_mod_cast L.edge_one_pos)
        (by exact_mod_cast L.lo_two_pos)
    nlinarith only [hzbound, hposprod]

  exact Or.inr ⟨A, B, b, z, hA, hB,
    hbP, hb1, hb2pos, hzP, hz1pos, hz2,
    hbound, hbG, hzG, hGzero⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
