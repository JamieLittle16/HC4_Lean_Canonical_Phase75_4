import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitEarliestLineDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseSourceDeficits
import HC4.Polynomial.DerivativeBounds
import Mathlib.Tactic

/-!
# Reflected tilted support bounds for the central deficit family

For reflected spacing d = J-q, use the source weights

left:  w(e) = d*e2 - (e1+e2),
right: w(e) = d*e1 - (e1+e2).

The first reflected line has weight -q.  The earliest-departure packet proves
that every positive exact layer before s has weight at most -q.  At the
selected order s, choosing the largest missing exponent gives one unique
top-weight source monomial.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

def firstDeficitLeftTiltWeight (d : ℕ) : Fin 4 → ℤ :=
  fun i =>
    if i = (1 : Fin 4) then -1
    else if i = (2 : Fin 4) then (d : ℤ) - 1
    else 0

def firstDeficitRightTiltWeight (d : ℕ) : Fin 4 → ℤ :=
  fun i =>
    if i = (1 : Fin 4) then (d : ℤ) - 1
    else if i = (2 : Fin 4) then -1
    else 0

theorem weight_firstDeficitLeftTiltWeight
    (d : ℕ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (firstDeficitLeftTiltWeight d) e =
      (d : ℤ) * (e 2 : ℤ) - ((e 1 : ℤ) + (e 2 : ℤ)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [firstDeficitLeftTiltWeight]
    ring
  · intro i
    simp

theorem weight_firstDeficitRightTiltWeight
    (d : ℕ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (firstDeficitRightTiltWeight d) e =
      (d : ℤ) * (e 1 : ℤ) - ((e 1 : ℤ) + (e 2 : ℤ)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [firstDeficitRightTiltWeight]
    ring
  · intro i
    simp

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

private theorem firstDeficitOrder_le_of_layer_mem
    {n : ℕ} (hnpos : 0 < n)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer P.centralDeficitFamily n).support) :
    G.firstDeficitOrder ≤ n := by
  have hc :
      (MvPolynomial.coeff e P.centralDeficitFamily).coeff n ≠ 0 := by
    rw [← familyParameterLayer_coeff]
    exact MvPolynomial.mem_support_iff.mp he
  have heFamily : e ∈ P.centralDeficitFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hc
    simp at hc
  have hnmem : n ∈ familyParameterLayerOrders P.centralDeficitFamily :=
    (mem_familyParameterLayerOrders_iff P.centralDeficitFamily n).2
      ⟨e, heFamily, hc⟩
  exact firstPositiveActualParameterOrder_le
    P.centralDeficitFamily
    (centralDeficitFamily_hasPositiveActualLayer G)
    hnmem hnpos

theorem firstDeficitLeftTilt_earlierLayer_isWeightLE
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 2 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 2 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 2 →
        f 1 + f 2 < q + f 2 * (J - q) →
        s ≤ f 1 + f 2)
    {n : ℕ} (hnpos : 0 < n) (hns : n < s) :
    HC4.Polynomial.IsWeightLE
      (firstDeficitLeftTiltWeight (J - q)) (-(q : ℤ))
      (familyParameterLayer P.centralDeficitFamily n) := by
  intro e he
  have hsrc := (P.centralDeficitFamily_layer_mem_iff n e).1 he
  have horder : e 1 + e 2 = n := hsrc.2
  have hqle : q ≤ n := by
    rw [hq]
    exact G.firstDeficitOrder_le_of_layer_mem hnpos he
  let d := J - q
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hline : q + e 2 * d ≤ n := by
    by_cases h0 : e 2 = 0
    · rw [h0]
      simpa using hqle
    by_cases h1 : e 2 = 1
    · have hJle := hmin1 e hsrc.1 (by omega)
      rw [horder] at hJle
      have hJ : J = q + d := by
        dsimp [d]
        omega
      simpa [h1, hJ] using hJle
    by_cases h2 : e 2 = 2
    · have h2le := hmin2 e hsrc.1 (by omega)
      rw [horder] at h2le
      simpa [h2, d] using h2le
    · have h3 : 3 ≤ e 2 := by omega
      by_contra hnot
      have hbad : e 1 + e 2 < q + e 2 * d := by
        rw [horder]
        exact Nat.lt_of_not_ge hnot
      have hsle := hearliest e hsrc.1 h3 (by simpa [d] using hbad)
      rw [horder] at hsle
      omega
  rw [weight_firstDeficitLeftTiltWeight]
  have hlineZ :
      (q : ℤ) + (e 2 : ℤ) * (d : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hline
  have horderZ :
      (e 1 : ℤ) + (e 2 : ℤ) = (n : ℤ) := by
    exact_mod_cast horder
  rw [horderZ]
  dsimp [d] at hlineZ ⊢
  nlinarith

theorem firstDeficitRightTilt_earlierLayer_isWeightLE
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 1 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 1 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 1 →
        f 1 + f 2 < q + f 1 * (J - q) →
        s ≤ f 1 + f 2)
    {n : ℕ} (hnpos : 0 < n) (hns : n < s) :
    HC4.Polynomial.IsWeightLE
      (firstDeficitRightTiltWeight (J - q)) (-(q : ℤ))
      (familyParameterLayer P.centralDeficitFamily n) := by
  intro e he
  have hsrc := (P.centralDeficitFamily_layer_mem_iff n e).1 he
  have horder : e 1 + e 2 = n := hsrc.2
  have hqle : q ≤ n := by
    rw [hq]
    exact G.firstDeficitOrder_le_of_layer_mem hnpos he
  let d := J - q
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hline : q + e 1 * d ≤ n := by
    by_cases h0 : e 1 = 0
    · rw [h0]
      simpa using hqle
    by_cases h1 : e 1 = 1
    · have hJle := hmin1 e hsrc.1 (by omega)
      rw [horder] at hJle
      have hJ : J = q + d := by
        dsimp [d]
        omega
      simpa [h1, hJ] using hJle
    by_cases h2 : e 1 = 2
    · have h2le := hmin2 e hsrc.1 (by omega)
      rw [horder] at h2le
      simpa [h2, d] using h2le
    · have h3 : 3 ≤ e 1 := by omega
      by_contra hnot
      have hbad : e 1 + e 2 < q + e 1 * d := by
        rw [horder]
        exact Nat.lt_of_not_ge hnot
      have hsle := hearliest e hsrc.1 h3 (by simpa [d] using hbad)
      rw [horder] at hsle
      omega
  rw [weight_firstDeficitRightTiltWeight]
  have hlineZ :
      (q : ℤ) + (e 1 : ℤ) * (d : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hline
  have horderZ :
      (e 1 : ℤ) + (e 2 : ℤ) = (n : ℤ) := by
    exact_mod_cast horder
  rw [horderZ]
  dsimp [d] at hlineZ ⊢
  nlinarith

theorem firstDeficitLeftTilt_selectedLayer_top
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s m : ℕ}
    (hqJ : q < J)
    {depart : Fin 4 →₀ ℕ}
    (hdepart : depart ∈ P.carrier.support)
    (horder : depart 1 + depart 2 = s)
    (hmissing : depart 2 = m)
    (hm3 : 3 ≤ m)
    (hbad : s < q + m * (J - q))
    (hmax :
      ∀ f ∈ P.carrier.support,
        f 1 + f 2 = s →
        3 ≤ f 2 →
        f 1 + f 2 < q + f 2 * (J - q) →
        f 2 ≤ m) :
    let w := firstDeficitLeftTiltWeight (J - q)
    let M : ℤ := ((J - q : ℕ) : ℤ) * (m : ℤ) - (s : ℤ)
    let L := familyParameterLayer P.centralDeficitFamily s
    HC4.Polynomial.IsWeightLE w M L ∧
      HC4.Polynomial.initialForm w M L =
        MvPolynomial.monomial depart (MvPolynomial.coeff depart L) := by
  let d := J - q
  let w := firstDeficitLeftTiltWeight d
  let M : ℤ := (d : ℤ) * (m : ℤ) - (s : ℤ)
  let L := familyParameterLayer P.centralDeficitFamily s
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hdepartL : depart ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hdepart, horder⟩
  have hbound : HC4.Polynomial.IsWeightLE w M L := by
    intro e he
    have hsrc :=
      (P.centralDeficitFamily_layer_mem_iff s e).1 (by simpa [L] using he)
    have heorder : e 1 + e 2 = s := hsrc.2
    have hem : e 2 ≤ m := by
      by_contra hnot
      have hgt : m < e 2 := Nat.lt_of_not_ge hnot
      have he3 : 3 ≤ e 2 :=
        le_trans hm3 (Nat.le_of_lt hgt)
      have hebad : e 1 + e 2 < q + e 2 * d := by
        rw [heorder]
        have hb : s < q + m * d := by simpa [d] using hbad
        have hmul : m * d < e 2 * d :=
          Nat.mul_lt_mul_of_pos_right hgt hdpos
        omega
      exact (not_lt_of_ge
        (hmax e hsrc.1 heorder he3 (by simpa [d] using hebad))) hgt
    rw [weight_firstDeficitLeftTiltWeight]
    have hemZ : (e 2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hem
    have heorderZ :
        (e 1 : ℤ) + (e 2 : ℤ) = (s : ℤ) := by
      exact_mod_cast heorder
    rw [heorderZ]
    dsimp [w, M, d]
    have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
    nlinarith
  refine ⟨hbound, ?_⟩
  apply MvPolynomial.ext
  intro e
  rw [HC4.Polynomial.coeff_initialForm]
  by_cases hwt : Finsupp.weight w e = M
  · rw [if_pos hwt]
    by_cases he : e ∈ L.support
    · have hsrc :=
        (P.centralDeficitFamily_layer_mem_iff s e).1 (by simpa [L] using he)
      have heorder : e 1 + e 2 = s := hsrc.2
      have hem : e 2 = m := by
        rw [weight_firstDeficitLeftTiltWeight] at hwt
        have heorderZ :
            (e 1 : ℤ) + (e 2 : ℤ) = (s : ℤ) := by
          exact_mod_cast heorder
        rw [heorderZ] at hwt
        dsimp [w, M, d] at hwt
        have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
        have hemZ : (e 2 : ℤ) = (m : ℤ) := by nlinarith
        exact_mod_cast hemZ
      have he1 : e 1 = depart 1 := by
        rw [hmissing] at horder
        omega
      have heq : e = depart :=
        HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.QsOtherFacetPrLeftVContactFrontierData.support_eq_of_deficits_eq F hthree houtThree
          hsrc.1 hdepart he1 (by omega)
      subst e
      simp
    · have hz : MvPolynomial.coeff e L = 0 :=
        MvPolynomial.notMem_support_iff.mp he
      have hne : e ≠ depart := by
        intro heq
        subst e
        exact he hdepartL
      rw [hz, MvPolynomial.coeff_monomial]
      have hne' : depart ≠ e := fun h => hne h.symm
      simp [hne']
  · rw [if_neg hwt, MvPolynomial.coeff_monomial]
    by_cases heq : e = depart
    · subst e
      exfalso
      apply hwt
      rw [weight_firstDeficitLeftTiltWeight]
      have horderZ :
          (depart 1 : ℤ) + (depart 2 : ℤ) = (s : ℤ) := by
        exact_mod_cast horder
      rw [horderZ, hmissing]
    · have hne' : depart ≠ e := fun h => heq h.symm
      simp [hne']

theorem firstDeficitRightTilt_selectedLayer_top
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s m : ℕ}
    (hqJ : q < J)
    {depart : Fin 4 →₀ ℕ}
    (hdepart : depart ∈ P.carrier.support)
    (horder : depart 1 + depart 2 = s)
    (hmissing : depart 1 = m)
    (hm3 : 3 ≤ m)
    (hbad : s < q + m * (J - q))
    (hmax :
      ∀ f ∈ P.carrier.support,
        f 1 + f 2 = s →
        3 ≤ f 1 →
        f 1 + f 2 < q + f 1 * (J - q) →
        f 1 ≤ m) :
    let w := firstDeficitRightTiltWeight (J - q)
    let M : ℤ := ((J - q : ℕ) : ℤ) * (m : ℤ) - (s : ℤ)
    let L := familyParameterLayer P.centralDeficitFamily s
    HC4.Polynomial.IsWeightLE w M L ∧
      HC4.Polynomial.initialForm w M L =
        MvPolynomial.monomial depart (MvPolynomial.coeff depart L) := by
  let d := J - q
  let w := firstDeficitRightTiltWeight d
  let M : ℤ := (d : ℤ) * (m : ℤ) - (s : ℤ)
  let L := familyParameterLayer P.centralDeficitFamily s
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hdepartL : depart ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hdepart, horder⟩
  have hbound : HC4.Polynomial.IsWeightLE w M L := by
    intro e he
    have hsrc :=
      (P.centralDeficitFamily_layer_mem_iff s e).1 (by simpa [L] using he)
    have heorder : e 1 + e 2 = s := hsrc.2
    have hem : e 1 ≤ m := by
      by_contra hnot
      have hgt : m < e 1 := Nat.lt_of_not_ge hnot
      have he3 : 3 ≤ e 1 :=
        le_trans hm3 (Nat.le_of_lt hgt)
      have hebad : e 1 + e 2 < q + e 1 * d := by
        rw [heorder]
        have hb : s < q + m * d := by simpa [d] using hbad
        have hmul : m * d < e 1 * d :=
          Nat.mul_lt_mul_of_pos_right hgt hdpos
        omega
      exact (not_lt_of_ge
        (hmax e hsrc.1 heorder he3 (by simpa [d] using hebad))) hgt
    rw [weight_firstDeficitRightTiltWeight]
    have hemZ : (e 1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hem
    have heorderZ :
        (e 1 : ℤ) + (e 2 : ℤ) = (s : ℤ) := by
      exact_mod_cast heorder
    rw [heorderZ]
    dsimp [w, M, d]
    have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
    nlinarith
  refine ⟨hbound, ?_⟩
  apply MvPolynomial.ext
  intro e
  rw [HC4.Polynomial.coeff_initialForm]
  by_cases hwt : Finsupp.weight w e = M
  · rw [if_pos hwt]
    by_cases he : e ∈ L.support
    · have hsrc :=
        (P.centralDeficitFamily_layer_mem_iff s e).1 (by simpa [L] using he)
      have heorder : e 1 + e 2 = s := hsrc.2
      have hem : e 1 = m := by
        rw [weight_firstDeficitRightTiltWeight] at hwt
        have heorderZ :
            (e 1 : ℤ) + (e 2 : ℤ) = (s : ℤ) := by
          exact_mod_cast heorder
        rw [heorderZ] at hwt
        dsimp [w, M, d] at hwt
        have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hdpos
        have hemZ : (e 1 : ℤ) = (m : ℤ) := by nlinarith
        exact_mod_cast hemZ
      have he2 : e 2 = depart 2 := by
        rw [hmissing] at horder
        omega
      have heq : e = depart :=
        HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.QsOtherFacetPrLeftVContactFrontierData.support_eq_of_deficits_eq F hthree houtThree
          hsrc.1 hdepart (by omega) he2
      subst e
      simp
    · have hz : MvPolynomial.coeff e L = 0 :=
        MvPolynomial.notMem_support_iff.mp he
      have hne : e ≠ depart := by
        intro heq
        subst e
        exact he hdepartL
      rw [hz, MvPolynomial.coeff_monomial]
      have hne' : depart ≠ e := fun h => hne h.symm
      simp [hne']
  · rw [if_neg hwt, MvPolynomial.coeff_monomial]
    by_cases heq : e = depart
    · subst e
      exfalso
      apply hwt
      rw [weight_firstDeficitRightTiltWeight]
      have horderZ :
          (depart 1 : ℤ) + (depart 2 : ℤ) = (s : ℤ) := by
        exact_mod_cast horder
      rw [horderZ, hmissing]
    · have hne' : depart ≠ e := fun h => heq h.symm
      simp [hne']

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation