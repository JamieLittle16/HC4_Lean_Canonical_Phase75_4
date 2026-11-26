import HC4.Polynomial.RationalCharacteristicRankOneSpecialization

/-!
# Higher-order noncharacteristic vanishing

A zero jet is a recursively defined condition on all polynomial
partials up to a given order. Multiplication preserves zero jets,
and multiplication by a polynomial nonzero at the specialization
reflects them. The corrected differential equations then propagate
zero jets to every order, and total-degree descent forces the
original polynomial to be zero.

This argument does not require a Taylor expansion or a local ring.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K F : Type*} [Field K] [CharZero K]
  [CommRing F] [IsDomain F] [Algebra K F]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- Vanishing of the specialization of all partial derivatives
through order n, including the original polynomial. -/
def rankOne_zeroJet (φ : B K →ₐ[K] F) : ℕ → B K → Prop
  | 0, p => φ p = 0
  | n + 1, p => rankOne_zeroJet φ n p ∧
      ∀ i : Fin 3, rankOne_zeroJet φ n (pderiv i p)

theorem rankOne_zeroJet_eval
    (φ : B K →ₐ[K] F) (n : ℕ) (p : B K)
    (h : rankOne_zeroJet φ n p) : φ p = 0 := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.1

theorem rankOne_zeroJet_add
    (φ : B K →ₐ[K] F) (n : ℕ) (p q : B K)
    (hp : rankOne_zeroJet φ n p) (hq : rankOne_zeroJet φ n q) :
    rankOne_zeroJet φ n (p + q) := by
  induction n generalizing p q with
  | zero =>
    change φ p = 0 at hp
    change φ q = 0 at hq
    change φ (p + q) = 0
    rw [map_add, hp, hq, add_zero]
  | succ n ih =>
    refine ⟨ih p q hp.1 hq.1, ?_⟩
    intro i
    rw [map_add]
    exact ih _ _ (hp.2 i) (hq.2 i)

theorem rankOne_zeroJet_sub
    (φ : B K →ₐ[K] F) (n : ℕ) (p q : B K)
    (hp : rankOne_zeroJet φ n p) (hq : rankOne_zeroJet φ n q) :
    rankOne_zeroJet φ n (p - q) := by
  induction n generalizing p q with
  | zero =>
    change φ p = 0 at hp
    change φ q = 0 at hq
    change φ (p - q) = 0
    rw [map_sub, hp, hq, sub_self]
  | succ n ih =>
    refine ⟨ih p q hp.1 hq.1, ?_⟩
    intro i
    rw [map_sub]
    exact ih _ _ (hp.2 i) (hq.2 i)

theorem rankOne_zeroJet_mul
    (φ : B K →ₐ[K] F) (n : ℕ) (a p : B K)
    (hp : rankOne_zeroJet φ n p) :
    rankOne_zeroJet φ n (a * p) := by
  induction n generalizing a p with
  | zero =>
    change φ p = 0 at hp
    change φ (a * p) = 0
    rw [map_mul, hp, mul_zero]
  | succ n ih =>
    refine ⟨ih a p hp.1, ?_⟩
    intro i
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    apply rankOne_zeroJet_add
    · exact ih a _ (hp.2 i)
    · rw [mul_comm p (pderiv i a)]
      exact ih _ p hp.1

/-- A multiplier which is nonzero at the specialization cannot
increase the order of vanishing of a zero jet. -/
theorem rankOne_zeroJet_cancel
    (φ : B K →ₐ[K] F) (n : ℕ) (a p : B K)
    (ha : φ a ≠ 0) (hp : rankOne_zeroJet φ n (a * p)) :
    rankOne_zeroJet φ n p := by
  induction n generalizing a p with
  | zero =>
    change φ (a * p) = 0 at hp
    change φ p = 0
    rw [map_mul] at hp
    exact (mul_eq_zero.mp hp).resolve_left ha
  | succ n ih =>
    have h : rankOne_zeroJet φ n p := ih a p ha hp.1
    refine ⟨h, ?_⟩
    intro i
    have hd := hp.2 i
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hd
    have ht : rankOne_zeroJet φ n (p * pderiv i a) := by
      rw [mul_comm]
      exact rankOne_zeroJet_mul φ n _ _ h
    have hh := rankOne_zeroJet_sub φ n _ _ hd ht
    rw [add_sub_cancel_right] at hh
    exact ih a _ ha hh

/-- The tangent derivative preserves every zero jet when it
preserves the specialization kernel. Mixed partials commute. -/
theorem rankOne_zeroJet_tangent
    (φ : B K →ₐ[K] F) (j : Fin 3)
    (ht : ∀ p : B K, φ p = 0 → φ (pderiv j p) = 0)
    (n : ℕ) (p : B K) (hp : rankOne_zeroJet φ n p) :
    rankOne_zeroJet φ n (pderiv j p) := by
  induction n generalizing p with
  | zero => exact ht p hp
  | succ n ih =>
    refine ⟨ih p hp.1, ?_⟩
    intro i
    rw [HC4.Newton.pderiv_comm_backport]
    exact ih _ (hp.2 i)

/-- Noncharacteristic polynomial differential equations propagate
vanishing at the specialization to all finite jet orders. -/
theorem rankOne_zeroJet_of_differentialEquations
    (φ : B K →ₐ[K] F) (j : Fin 3)
    (a b : Fin 3 → B K) (p : B K)
    (ht : ∀ f : B K, φ f = 0 → φ (pderiv j f) = 0)
    (hb : ∀ l, l ≠ j → φ (b l) ≠ 0)
    (hd : ∀ l, l ≠ j → p ∣ rankOne_clearedPolynomialPartial (a l) (b l) j l p)
    (hp : φ p = 0) (n : ℕ) :
    rankOne_zeroJet φ n p := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    refine ⟨ih, ?_⟩
    intro l
    have hj := rankOne_zeroJet_tangent φ j ht n p ih
    by_cases hl : l = j
    · subst l
      exact hj
    · obtain ⟨r, hr⟩ := hd l hl
      change b l * pderiv l p - a l * pderiv j p = p * r at hr
      have he : b l * pderiv l p = a l * pderiv j p + p * r := by
        linear_combination hr
      apply rankOne_zeroJet_cancel φ n (b l) _ (hb l hl)
      rw [he]
      apply rankOne_zeroJet_add
      · exact rankOne_zeroJet_mul φ n _ _ hj
      · rw [mul_comm p r]
        exact rankOne_zeroJet_mul φ n _ _ ih

/-- Vanishing at every finite jet order detects the zero polynomial.
Use degree descent rather than a multivariate Taylor coefficient
formula. Characteristic zero is needed for the constant-polynomial
conclusion from vanishing partials. -/
theorem rankOne_eq_zero_of_all_zeroJets
    (φ : B K →ₐ[K] F) (p : B K)
    (hp : ∀ n, rankOne_zeroJet φ n p) : p = 0 := by
  classical
  have aux (d : ℕ) : ∀ f : B K, f.totalDegree = d →
      (∀ n, rankOne_zeroJet φ n f) → f = 0 := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro f hf hj
      have hc : f = MvPolynomial.C (f.coeff 0) := by
        by_cases hd : f.totalDegree = 0
        · exact totalDegree_eq_zero_iff_eq_C.mp hd
        · apply transverse_eq_C_of_all_pderiv_zero
          intro i
          apply ih (pderiv i f).totalDegree
          · rw [← hf]
            exact totalDegree_pderiv_lt_of_totalDegree_pos f i (Nat.pos_of_ne_zero hd)
          · rfl
          · intro n
            exact (hj (n + 1)).2 i
      have hz : φ f = 0 := hj 0
      have hv : algebraMap K F (f.coeff 0) = 0 := by
        calc
          _ = φ (MvPolynomial.C (f.coeff 0)) := (φ.commutes _).symm
          _ = φ f := congrArg φ hc.symm
          _ = 0 := hz
      have hh : f.coeff 0 = 0 := by
        apply (algebraMap K F).injective
        simpa only [map_zero] using hv
      calc
        f = MvPolynomial.C (f.coeff 0) := hc
        _ = 0 := by rw [hh, map_zero]
  exact aux p.totalDegree p rfl hp

/-- The noncharacteristic vanishing theorem. No degree bound on the
polynomial solution or its differential cofactors is required. -/
theorem rankOne_specialization_ne_zero_of_differentialEquations
    (φ : B K →ₐ[K] F) (j : Fin 3)
    (a b : Fin 3 → B K) (p : B K) (hp : p ≠ 0)
    (ht : ∀ f : B K, φ f = 0 → φ (pderiv j f) = 0)
    (hb : ∀ l, l ≠ j → φ (b l) ≠ 0)
    (hd : ∀ l, l ≠ j → p ∣ rankOne_clearedPolynomialPartial (a l) (b l) j l p) :
    φ p ≠ 0 := by
  intro hz
  apply hp
  apply rankOne_eq_zero_of_all_zeroJets φ p
  exact rankOne_zeroJet_of_differentialEquations φ j a b p ht hb hd hz

end
end HC4.Polynomial.RankThreeCubic
