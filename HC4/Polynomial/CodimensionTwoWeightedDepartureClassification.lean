import HC4.Polynomial.CodimensionTwoWeightedDeparturePencil
import Mathlib.Tactic

/-!
# Classification of coefficient-weighted codimension-two departure pencils

The A19 source carrier does not have unit coefficients.  The weighted pencil
keeps the three honest nonzero source coefficients `C,A,B`.  Its extremal
Hessian determinant coefficients differ from the unit-coefficient pencil only
by nonzero powers of these scalars, so the same primitive-departure
classification follows without normalising or dividing the source polynomial.
-/

namespace HC4.Polynomial

noncomputable section

/-- **Weighted primitive codimension-two departure classification.**

The first departure has been oriented to have order one.  Singularity then
forces either a second primitive departure with the same active exponent, or
one of the two asymmetric endpoint configurations. -/
theorem singular_codimensionTwoWeightedDeparturePencil_leftPrimitive_classification
    {K : Type*} [Field K] [CharZero K]
    {D p a c n : ℕ} {C A B : K}
    (hD : 3 ≤ D)
    (hp : 0 < p)
    (hpD : p < D)
    (hn : 0 < n)
    (ha : a + 1 ≤ D)
    (hc : c + n ≤ D)
    (hC : C ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hsing :
      (codimensionTwoWeightedDeparturePencil
        (D : K) (p : K) (a : K) (1 : K)
        (c : K) (n : K) C A B).det = 0) :
    (n = 1 ∧ a = c) ∨
      (1 < n ∧
        ((a = 0 ∧ p = 1 ∧ c = 0) ∨
          (a = D - 1 ∧ p = D - 1 ∧ c = D - n))) := by
  have hD1Nat : 1 ≤ D := by omega
  have hD1K : (D : K) - 1 ≠ 0 := by
    intro hz
    have hcast : (D : K) = 1 := sub_eq_zero.mp hz
    have hnat : D = 1 := by exact_mod_cast hcast
    omega
  by_cases hn1 : n = 1
  · left
    refine ⟨hn1, ?_⟩
    subst n
    have hcoeff :
        A ^ 2 * B ^ 2 * ((D : K) - 1)^2 *
            ((a : K) - (c : K))^2 = 0 := by
      calc
        A ^ 2 * B ^ 2 * ((D : K) - 1)^2 *
              ((a : K) - (c : K))^2 =
            (((codimensionTwoWeightedDeparturePencil
              (D : K) (p : K) (a : K) 1 (c : K) 1 C A B).det).coeff 2).coeff 2 := by
                symm
                exact
                  coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_primitive
                    (K := K) (D : K) (p : K) (a : K) (c : K) C A B
        _ = 0 := by rw [hsing]; simp
    have hleft : A ^ 2 * B ^ 2 * ((D : K) - 1)^2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB))
        (pow_ne_zero 2 hD1K)
    have hsq : ((a : K) - (c : K))^2 = 0 := by
      have hrearr :
          (A ^ 2 * B ^ 2 * ((D : K) - 1)^2) *
              ((a : K) - (c : K))^2 = 0 := by
        simpa [mul_assoc] using hcoeff
      exact (mul_eq_zero.mp hrearr).resolve_left hleft
    have hdiff : (a : K) - (c : K) = 0 := by
      rw [pow_two] at hsq
      rcases mul_eq_zero.mp hsq with h | h <;> exact h
    have hacast : (a : K) = (c : K) := sub_eq_zero.mp hdiff
    exact_mod_cast hacast

  · right
    have hn2 : 1 < n := by omega
    refine ⟨hn2, ?_⟩
    have hnK : (n : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hn1K : (n : K) - 1 ≠ 0 := by
      intro hz
      have hcast : (n : K) = 1 := sub_eq_zero.mp hz
      have hnat : n = 1 := by exact_mod_cast hcast
      exact hn1 hnat

    have hcube :
        A ^ 3 * B *
          ((a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
            ((D : K) - (a : K) - 1)) = 0 := by
      calc
        A ^ 3 * B *
              ((a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
                ((D : K) - (a : K) - 1)) =
            (((codimensionTwoWeightedDeparturePencil
              (D : K) (p : K) (a : K) 1 (c : K) (n : K) C A B).det).coeff 3).coeff 1 := by
                symm
                exact
                  coeff_s_cube_t_det_codimensionTwoWeightedDeparturePencil_leftPrimitive
                    (K := K) (D : K) (p : K) (a : K) (c : K) (n : K) C A B
        _ = 0 := by rw [hsing]; simp
    have hcoeffAB : A ^ 3 * B ≠ 0 := mul_ne_zero (pow_ne_zero 3 hA) hB
    have hcore :
        (a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
            ((D : K) - (a : K) - 1) = 0 :=
      (mul_eq_zero.mp hcube).resolve_left hcoeffAB
    have hmid : (n : K) * ((D : K) - 1) * ((n : K) - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hnK hD1K) hn1K
    have hacore :
        (a : K) * ((D : K) - (a : K) - 1) = 0 := by
      have hrearr :
          ((a : K) * ((D : K) - (a : K) - 1)) *
              ((n : K) * ((D : K) - 1) * ((n : K) - 1)) = 0 := by
        calc
          _ = (a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
                ((D : K) - (a : K) - 1) := by ring
          _ = 0 := hcore
      exact (mul_eq_zero.mp hrearr).resolve_right hmid

    rcases mul_eq_zero.mp hacore with ha0K | haTopK
    · left
      have ha0 : a = 0 := by exact_mod_cast ha0K
      subst a
      have hcoeffP :
          -(C * A ^ 2 * B *
            ((n : K) * ((n : K) - 1) * (p : K) *
              ((D : K) - 1)^2 * ((p : K) - 1))) = 0 := by
        calc
          _ = (((codimensionTwoWeightedDeparturePencil
              (D : K) (p : K) 0 1 (c : K) (n : K) C A B).det).coeff 2).coeff 1 := by
                symm
                exact
                  coeff_s_sq_t_det_codimensionTwoWeightedDeparturePencil_leftZero
                    (K := K) (D : K) (p : K) (c : K) (n : K) C A B
          _ = 0 := by rw [hsing]; simp
      have hpK : (p : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
      have hknownP :
          C * A ^ 2 * B * (n : K) * ((n : K) - 1) * (p : K) *
              ((D : K) - 1)^2 ≠ 0 := by
        repeat' apply mul_ne_zero
        · exact hC
        · exact pow_ne_zero 2 hA
        · exact hB
        · exact hnK
        · exact hn1K
        · exact hpK
        · exact pow_ne_zero 2 hD1K
      have hpSub : (p : K) - 1 = 0 := by
        have hprod :
            (C * A ^ 2 * B * (n : K) * ((n : K) - 1) * (p : K) *
                ((D : K) - 1)^2) * ((p : K) - 1) = 0 := by
          have hz := neg_eq_zero.mp hcoeffP
          simpa [mul_assoc] using hz
        exact (mul_eq_zero.mp hprod).resolve_left hknownP
      have hpCast : (p : K) = 1 := sub_eq_zero.mp hpSub
      have hp1 : p = 1 := by exact_mod_cast hpCast
      subst p

      have hcoeffC :
          A ^ 2 * B ^ 2 *
            ((c : K) * (n : K) * ((D : K) - 1)^2 *
              ((c : K) + (n : K) - 1)) = 0 := by
        calc
          _ = (((codimensionTwoWeightedDeparturePencil
              (D : K) 1 0 1 (c : K) (n : K) C A B).det).coeff 2).coeff 2 := by
                symm
                exact
                  coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_leftZero_baseOne
                    (K := K) (D : K) (c : K) (n : K) C A B
          _ = 0 := by rw [hsing]; simp
      have hAB : A ^ 2 * B ^ 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)
      have hcoreC :
          (c : K) * (n : K) * ((D : K) - 1)^2 *
              ((c : K) + (n : K) - 1) = 0 :=
        (mul_eq_zero.mp hcoeffC).resolve_left hAB
      have hcnNat : 0 < c + n - 1 := by omega
      have hcnNe : c + n - 1 ≠ 0 := Nat.ne_of_gt hcnNat
      have hcnCast0 : ((c + n - 1 : ℕ) : K) ≠ 0 := by exact_mod_cast hcnNe
      have hcnCast :
          ((c + n - 1 : ℕ) : K) = (c : K) + (n : K) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ c + n), Nat.cast_add]
        norm_num
      have hlastC : (c : K) + (n : K) - 1 ≠ 0 := by
        rw [← hcnCast]
        exact hcnCast0
      have hknownC :
          (n : K) * ((D : K) - 1)^2 *
              ((c : K) + (n : K) - 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hnK (pow_ne_zero 2 hD1K)) hlastC
      have hcK : (c : K) = 0 := by
        have hrearr :
            (c : K) *
                ((n : K) * ((D : K) - 1)^2 *
                  ((c : K) + (n : K) - 1)) = 0 := by
          simpa [mul_assoc] using hcoreC
        exact (mul_eq_zero.mp hrearr).resolve_right hknownC
      have hc0 : c = 0 := by exact_mod_cast hcK
      exact ⟨rfl, rfl, hc0⟩

    · right
      have haCast : (a : K) = (D : K) - 1 := by linear_combination haTopK
      have hDm1Cast : ((D - 1 : ℕ) : K) = (D : K) - 1 := by
        rw [Nat.cast_sub hD1Nat]
        norm_num
      have haCast' : (a : K) = ((D - 1 : ℕ) : K) := by
        rw [hDm1Cast]
        exact haCast
      have haTop : a = D - 1 := by exact_mod_cast haCast'
      subst a

      have hcoeffP :
          -(C * A ^ 2 * B *
            ((n : K) * ((n : K) - 1) * ((D : K) - 1)^2 *
              ((p : K) - (D : K)) * ((p : K) - (D : K) + 1))) = 0 := by
        calc
          _ = (((codimensionTwoWeightedDeparturePencil
              (D : K) (p : K) ((D : K) - 1) 1
              (c : K) (n : K) C A B).det).coeff 2).coeff 1 := by
                symm
                exact
                  coeff_s_sq_t_det_codimensionTwoWeightedDeparturePencil_leftTop
                    (K := K) (D : K) (p : K) (c : K) (n : K) C A B
          _ = 0 := by
            simpa [hDm1Cast] using hsing
      have hpDne : p ≠ D := by omega
      have hpDcast : (p : K) - (D : K) ≠ 0 := by
        intro hz
        have heq : (p : K) = (D : K) := sub_eq_zero.mp hz
        have : p = D := by exact_mod_cast heq
        exact hpDne this
      have hknownP :
          C * A ^ 2 * B * (n : K) * ((n : K) - 1) *
              ((D : K) - 1)^2 * ((p : K) - (D : K)) ≠ 0 := by
        repeat' apply mul_ne_zero
        · exact hC
        · exact pow_ne_zero 2 hA
        · exact hB
        · exact hnK
        · exact hn1K
        · exact pow_ne_zero 2 hD1K
        · exact hpDcast
      have hpTopEq : (p : K) - (D : K) + 1 = 0 := by
        have hprod :
            (C * A ^ 2 * B * (n : K) * ((n : K) - 1) *
                ((D : K) - 1)^2 * ((p : K) - (D : K))) *
              ((p : K) - (D : K) + 1) = 0 := by
          have hz := neg_eq_zero.mp hcoeffP
          simpa [mul_assoc] using hz
        exact (mul_eq_zero.mp hprod).resolve_left hknownP
      have hpCast : (p : K) = (D : K) - 1 := by linear_combination hpTopEq
      have hpCast' : (p : K) = ((D - 1 : ℕ) : K) := by
        rw [hDm1Cast]
        exact hpCast
      have hpTop : p = D - 1 := by exact_mod_cast hpCast'
      subst p

      have hcoeffC :
          A ^ 2 * B ^ 2 *
            ((n : K) * ((D : K) - 1)^2 *
              ((c : K) + 1 - (D : K)) *
              ((c : K) + (n : K) - (D : K))) = 0 := by
        calc
          _ = (((codimensionTwoWeightedDeparturePencil
              (D : K) ((D : K) - 1) ((D : K) - 1) 1
              (c : K) (n : K) C A B).det).coeff 2).coeff 2 := by
                symm
                exact
                  coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_leftTop_baseTop
                    (K := K) (D : K) (c : K) (n : K) C A B
          _ = 0 := by
            simpa [hDm1Cast] using hsing
      have hAB : A ^ 2 * B ^ 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)
      have hcoreC :
          (n : K) * ((D : K) - 1)^2 *
              ((c : K) + 1 - (D : K)) *
              ((c : K) + (n : K) - (D : K)) = 0 :=
        (mul_eq_zero.mp hcoeffC).resolve_left hAB
      have hc1neD : c + 1 ≠ D := by omega
      have hc1Cast : (c : K) + 1 - (D : K) ≠ 0 := by
        intro hz
        have heq : (c : K) + 1 = (D : K) := sub_eq_zero.mp hz
        have hnat : c + 1 = D := by exact_mod_cast heq
        exact hc1neD hnat
      have hknownC :
          (n : K) * ((D : K) - 1)^2 *
              ((c : K) + 1 - (D : K)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hnK (pow_ne_zero 2 hD1K)) hc1Cast
      have hcTopEq : (c : K) + (n : K) - (D : K) = 0 := by
        have hprod :
            ((n : K) * ((D : K) - 1)^2 *
                ((c : K) + 1 - (D : K))) *
              ((c : K) + (n : K) - (D : K)) = 0 := by
          simpa [mul_assoc] using hcoreC
        exact (mul_eq_zero.mp hprod).resolve_left hknownC
      have hcSumCast : (c : K) + (n : K) = (D : K) := sub_eq_zero.mp hcTopEq
      have hcSum : c + n = D := by exact_mod_cast hcSumCast
      have hcFinal : c = D - n := by omega
      exact ⟨rfl, rfl, hcFinal⟩

end

end HC4.Polynomial
