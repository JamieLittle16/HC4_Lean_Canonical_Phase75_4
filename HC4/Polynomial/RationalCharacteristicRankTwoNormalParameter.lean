import HC4.Polynomial.RationalCharacteristicRankTwoAffineParameter

/-!
# The normal derivative and the direction tangent

The nonconstant straight direction has a rational common parameter.
The normalized left normal annihilates that direction and its
nonzero tangent, so every derivation killing the parameter also
kills the normal. Differentiating b * Dv = 0 then forces the row
beta * Dv to be proportional to the parameter differential.

Nilpotence sends the tangent into the velocity kernel. Hence either
the parameter differential annihilates the tangent, or the entire
normal is ground-field constant. This argument uses no
classification of line congruences.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Algebra

variable {F : Type*} [Field F]

/-- The square of a rank-two cube-zero matrix kills every vector
in the plane annihilated by its normalized left normal. -/
theorem rankTwo_square_kills_normalPlane
    (N : Matrix (Fin 3) (Fin 3) F) (b u : Fin 3 → F) (l : Fin 3)
    (hr : 2 ≤ N.rank) (h3 : N ^ 3 = 0)
    (hb : b ᵥ* N = 0) (hl : b l = 1) (hu : b ⬝ᵥ u = 0) :
    N *ᵥ (N *ᵥ u) = 0 := by
  have hcube : (N * N) * N = 0 := by
    simpa only [pow_succ, pow_zero, one_mul] using h3
  rw [Matrix.mulVec_mulVec]
  funext i
  let r : Fin 3 → F := fun j => (N * N) i j
  have hrN : r ᵥ* N = 0 := by
    funext j
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hcube
  have hprop (j : Fin 3) : r j = b j * r l := by
    have h := rankTwo_leftKernel_minors_zero N hr b r hb hrN l j
    rw [hl, one_mul] at h
    exact h
  change (∑ j : Fin 3, r j * u j) = 0
  have he : (∑ j : Fin 3, r j * u j) = r l * (b ⬝ᵥ u) := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hprop j]
    ring
  rw [he, hu, mul_zero]

/-- Any covector annihilating the normalized right kernel also
annihilates the image of the normal plane under N. -/
theorem rankTwo_normalPlane_image_pair_zero
    (N : Matrix (Fin 3) (Fin 3) F) (w b u beta : Fin 3 → F)
    (k l : Fin 3) (hr : 2 ≤ N.rank) (h3 : N ^ 3 = 0)
    (hk : w k = 1) (hl : b l = 1)
    (hw : N *ᵥ w = 0) (hb : b ᵥ* N = 0)
    (hu : b ⬝ᵥ u = 0) (hbeta : beta ⬝ᵥ w = 0) :
    (beta ᵥ* N) ⬝ᵥ u = 0 := by
  let z := N *ᵥ u
  have hz : N *ᵥ z = 0 := rankTwo_square_kills_normalPlane N b u l hr h3 hb hl hu
  have hp (i : Fin 3) : z i = w i * z k := by
    have h := rankTwo_rightKernel_minors_zero N hr w z hw hz k i
    rw [hk, one_mul] at h
    exact h
  rw [← Matrix.dotProduct_mulVec]
  change (∑ i : Fin 3, beta i * z i) = 0
  have he : (∑ i : Fin 3, beta i * z i) = z k * (beta ⬝ᵥ w) := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp i]
    ring
  rw [he, hbeta, mul_zero]

end Algebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev P (K : Type*) [Field K] := _root_.Polynomial K

/-- Product rule for the pairing of two rational vectors. -/
theorem rankTwo_derivation_dot
    (D : Derivation K (E K) (E K)) (x y : Fin 3 → E K) :
    D (x ⬝ᵥ y) = x ⬝ᵥ (fun i => D (y i)) +
      (fun i => D (x i)) ⬝ᵥ y := by
  simp only [dotProduct, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- A normalized normal to two independent parameter vectors is
constant under every derivation which kills the parameter. -/
theorem rankTwo_normal_invariant_of_parameter
    (D : Derivation K (E K) (E K)) (t : E K)
    (w b : Fin 3 → E K) (A Q U : Fin 3 → P K)
    (k l i : Fin 3) (ht : D t = 0)
    (hq : ∀ j, (Q j).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hw : ∀ j, w j = (A j).eval₂ (algebraMap K (E K)) t /
      (Q j).eval₂ (algebraMap K (E K)) t)
    (hk : w k = 1) (hl : b l = 1)
    (huk : (U k).eval₂ (algebraMap K (E K)) t = 0)
    (hui : (U i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hn : b ⬝ᵥ w = 0)
    (hbu : (∑ j : Fin 3, b j * (U j).eval₂ (algebraMap K (E K)) t) = 0) :
    ∀ j, D (b j) = 0 := by
  let u : Fin 3 → E K := fun j => (U j).eval₂ (algebraMap K (E K)) t
  let z : Fin 3 → E K := fun j => D (b j)
  have hpol (p : P K) : D (p.eval₂ (algebraMap K (E K)) t) = 0 := by
    rw [rationalParameter_polynomial_chainRule D t p, ht, mul_zero]
  have hwu (j : Fin 3) : D (w j) = 0 := by
    rw [hw, Derivation.leibniz_div]
    simp [hpol]
  have huu (j : Fin 3) : D (u j) = 0 := hpol (U j)
  have hz (x : Fin 3 → E K) (hx : b ⬝ᵥ x = 0)
      (hDx : ∀ j, D (x j) = 0) : z ⬝ᵥ x = 0 := by
    have h := rankTwo_derivation_dot D b x
    rw [hx, map_zero] at h
    have he : (fun j => D (x j)) = 0 := funext hDx
    rw [he] at h
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_add] at h
    exact h.symm
  have hzl : z l = 0 := by
    change D (b l) = 0
    rw [hl, Derivation.map_one_eq_zero]
  intro j
  have he := rankTwo_direction_normal_proportional w u b z k l i hk huk hui
    hl hn hbu (hz w hn hwu) (hz u hbu huu) j
  rw [hzl, mul_zero] at he
  exact he

/-- A normal whose derivative factors through dt is subject to
a row-integrability relation from the differentiated left kernel. -/
theorem rankTwo_normalDerivative_row_minors
    (V : I → E K) (b beta : Fin 3 → E K) (t : E K)
    (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (hdb : ∀ i j, rationalCharacteristicPartial j (b i) =
      rationalCharacteristicPartial j t * beta i) :
    ∀ j k : Fin 3,
      rationalCharacteristicPartial k t * (beta ᵥ* rationalCharacteristicJacobian V) j =
      rationalCharacteristicPartial j t * (beta ᵥ* rationalCharacteristicJacobian V) k := by
  let N := rationalCharacteristicJacobian V
  have he (j k : Fin 3) :
      rationalCharacteristicPartial k t * (beta ᵥ* N) j +
        ∑ i : Fin 3, b i * rationalCharacteristicPartial k (N i j) = 0 := by
    have h := congrArg (rationalCharacteristicPartial (K := K) k) (congrFun hb j)
    change rationalCharacteristicPartial k (∑ i : Fin 3, b i * N i j) =
      rationalCharacteristicPartial k 0 at h
    simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
      Finset.sum_add_distrib, hdb] at h
    have hf : (∑ i : Fin 3, N i j * (rationalCharacteristicPartial k t * beta i)) =
        rationalCharacteristicPartial k t * (beta ᵥ* N) j := by
      change (∑ i : Fin 3, N i j * (rationalCharacteristicPartial k t * beta i)) =
        rationalCharacteristicPartial k t * (∑ i : Fin 3, beta i * N i j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hf] at h
    linear_combination h
  intro j k
  have hs : (∑ i : Fin 3, b i * rationalCharacteristicPartial k (N i j)) =
      ∑ i : Fin 3, b i * rationalCharacteristicPartial j (N i k) := by
    apply Finset.sum_congr rfl
    intro i _
    change b i * rationalCharacteristicPartial k (rationalCharacteristicPartial j (V (.inr i))) =
      b i * rationalCharacteristicPartial j (rationalCharacteristicPartial k (V (.inr i)))
    rw [rationalCharacteristicPartial_comm k j]
  have h1 := he j k
  have h2 := he k j
  rw [hs] at h1
  linear_combination h1 - h2

set_option maxHeartbeats 2000000 in
/-- The normalized direction and its tangent are the two
independent vectors defining the source normal. If dt is
nonzero on that tangent, differentiated integrability and
nilpotence force the normal to be ground-field constant. -/
theorem rankTwo_parameter_tangent_or_constantNormal
    (V : I → E K) (w b : Fin 3 → E K) (k l : Fin 3)
    (hr : 2 ≤ (rationalCharacteristicJacobian V).rank)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hk : w k = 1) (hl : b l = 1)
    (hwN : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hn : b ⬝ᵥ w = 0) (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (t : E K) (A Q U : Fin 3 → P K) (s : E K)
    (hq : ∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hrep : ∀ i, w i = (A i).eval₂ (algebraMap K (E K)) t /
      (Q i).eval₂ (algebraMap K (E K)) t)
    (hfac : ∀ i j, rationalCharacteristicPartial j (w i) =
      s * (U i).eval₂ (algebraMap K (E K)) t * rationalCharacteristicPartial j t)
    (hi : ∃ i, (U i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hj : ∃ j, rationalCharacteristicPartial j t ≠ 0)
    (huk : (U k).eval₂ (algebraMap K (E K)) t = 0)
    (hbu : (∑ i : Fin 3, b i * (U i).eval₂ (algebraMap K (E K)) t) = 0) :
    rankTwo_directionalDerivation (fun i => (U i).eval₂ (algebraMap K (E K)) t) t = 0 ∨
      ∃ d : Fin 3 → K, d ≠ 0 ∧
        (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  let u : Fin 3 → E K := fun i => (U i).eval₂ (algebraMap K (E K)) t
  let N := rationalCharacteristicJacobian V
  obtain ⟨m, hm⟩ := hi
  obtain ⟨p, hp⟩ := hj
  let dt : Fin 3 → E K := fun j => rationalCharacteristicPartial j t
  let beta : Fin 3 → E K := fun i => rationalCharacteristicPartial p (b i) / dt p
  have hdb (i j : Fin 3) : rationalCharacteristicPartial j (b i) = dt j * beta i := by
    let D := rationalCharacteristicPartial (K := K) j -
      (dt j / dt p) • rationalCharacteristicPartial p
    have hDt : D t = 0 := by
      change dt j - (dt j / dt p) * dt p = 0
      rw [div_mul_cancel₀ _ hp, sub_self]
    have hbi : D (b i) = 0 :=
      rankTwo_normal_invariant_of_parameter D t w b A Q U k l m
        hDt hq hrep hk hl huk hm hn hbu i
    change rationalCharacteristicPartial j (b i) -
      (dt j / dt p) * rationalCharacteristicPartial p (b i) = 0 at hbi
    change rationalCharacteristicPartial j (b i) =
      dt j * (rationalCharacteristicPartial p (b i) / dt p)
    rw [sub_eq_zero.mp hbi]
    simp only [div_eq_mul_inv]
    ring
  have hbl : beta l = 0 := by
    change rationalCharacteristicPartial p (b l) / dt p = 0
    rw [hl, Derivation.map_one_eq_zero, zero_div]
  have hbw : beta ⬝ᵥ w = 0 := by
    have he := rankTwo_derivation_dot (rationalCharacteristicPartial (K := K) p) b w
    rw [hn, map_zero] at he
    have h1 : (b ⬝ᵥ (fun i => rationalCharacteristicPartial p (w i))) = 0 := by
      change (∑ i : Fin 3, b i * rationalCharacteristicPartial p (w i)) = 0
      simp only [hfac]
      have hf : (∑ i : Fin 3, b i * (s * u i * dt p)) =
          (s * dt p) * (b ⬝ᵥ u) := by
        rw [dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      change (∑ i : Fin 3, b i * (s * u i * dt p)) = 0
      rw [hf, show b ⬝ᵥ u = 0 from hbu, mul_zero]
    have h2 : ((fun i => rationalCharacteristicPartial p (b i)) ⬝ᵥ w) =
        dt p * (beta ⬝ᵥ w) := by
      rw [dotProduct, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hdb i p, mul_assoc]
    rw [h1, h2, zero_add] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hp
  change rankTwo_directionalDerivation u t = 0 ∨ _
  by_cases hz : rankTwo_directionalDerivation u t = 0
  · exact Or.inl hz
  · right
    let R := beta ᵥ* N
    have hpair : R ⬝ᵥ u = 0 :=
      rankTwo_normalPlane_image_pair_zero N w b u beta k l hr h3 hk hl hwN hb hbu hbw
    have hR (j : Fin 3) : R j = dt j * (R p / dt p) := by
      have h := rankTwo_normalDerivative_row_minors V b beta t hb hdb j p
      change dt p * R j = dt j * R p at h
      have hp' : dt p ≠ 0 := hp
      apply (mul_left_cancel₀ hp')
      calc
        dt p * R j = dt j * R p := h
        _ = dt p * (dt j * (R p / dt p)) := by
          calc
            dt j * R p = dt j * ((R p / dt p) * dt p) := by
              rw [div_mul_cancel₀ _ hp']
            _ = dt p * (dt j * (R p / dt p)) := by ring
    have hRp : R p = 0 := by
      have he : R ⬝ᵥ u = (R p / dt p) * rankTwo_directionalDerivation u t := by
        rw [dotProduct, rankTwo_directionalDerivation_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hR j]
        change dt j * (R p / dt p) * u j = (R p / dt p) * (u j * dt j)
        ring
      rw [hpair] at he
      have hzero := (mul_eq_zero.mp he.symm).resolve_right hz
      exact (mul_eq_zero.mp (show R p * (dt p)⁻¹ = 0 from hzero)).resolve_right (inv_ne_zero hp)
    have hRN : beta ᵥ* N = 0 := by
      funext j
      change R j = 0
      rw [hR, hRp, zero_div, mul_zero]
    have hbeta (j : Fin 3) : beta j = 0 := by
      have he := rankTwo_leftKernel_minors_zero N hr b beta hb hRN l j
      rw [hl, hbl, one_mul, mul_zero] at he
      exact he
    have hconst (i : Fin 3) : ∃ c : K, b i = algebraMap K (E K) c := by
      apply rationalCharacteristicPartial_constants
      intro j
      rw [hdb, hbeta, mul_zero]
    choose d hd using hconst
    have hd0 : d ≠ 0 := by
      intro h
      have he := hd l
      rw [hl, h, Pi.zero_apply, map_zero] at he
      exact one_ne_zero he
    refine ⟨d, hd0, ?_⟩
    have he : (fun i => algebraMap K (E K) (d i)) = b :=
      funext (fun i => (hd i).symm)
    rw [he]
    exact hb

end
end HC4.Polynomial.RankThreeCubic
