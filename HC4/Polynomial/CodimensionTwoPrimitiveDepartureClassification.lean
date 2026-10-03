import HC4.Polynomial.CodimensionTwoPrimitiveDeparturePencil
import Mathlib.Tactic

/-!
# Classification of a primitive codimension-two departure pencil

This file turns the fixed determinant coefficients of
`CodimensionTwoPrimitiveDeparturePencil` into the exact natural-exponent
classification used by the A19.55 paper closure.

We orient the two missing coordinates so that the first departure is primitive
(`m = 1`).  If the second departure is also primitive, singularity forces the
two active exponents to agree.  If the second departure has order `n > 1`, the
remaining extremal coefficients force one of the two endpoint configurations

    (a,p,c) = (0,1,0)

or

    (a,p,c) = (D-1,D-1,D-n).

The cyclic case is obtained by swapping the two missing coordinates before
applying this theorem.  No source-state or valuation data occur here.
-/

namespace HC4.Polynomial

noncomputable section

/-- **Primitive codimension-two departure classification.** -/
theorem singular_codimensionTwoDeparturePencil_leftPrimitive_classification
    {K : Type*} [Field K] [CharZero K]
    {D p a c n : ℕ}
    (hD : 3 ≤ D)
    (hp : 0 < p)
    (hpD : p < D)
    (hn : 0 < n)
    (ha : a + 1 ≤ D)
    (hc : c + n ≤ D)
    (hsing :
      (codimensionTwoDeparturePencil (K := K)
        (D : K) (p : K) (a : K) (1 : K) (c : K) (n : K)).det = 0) :
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
        ((D : K) - 1)^2 * ((a : K) - (c : K))^2 = 0 := by
      calc
        ((D : K) - 1)^2 * ((a : K) - (c : K))^2 =
            (((codimensionTwoDeparturePencil (K := K)
              (D : K) (p : K) (a : K) 1 (c : K) 1).det).coeff 2).coeff 2 := by
                symm
                exact
                  coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_primitive
                    (K := K) (D : K) (p : K) (a : K) (c : K)
        _ = 0 := by rw [hsing]; simp
    have hleft : ((D : K) - 1)^2 ≠ 0 := pow_ne_zero 2 hD1K
    have hsq : ((a : K) - (c : K))^2 = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_left hleft
    have hdiff : (a : K) - (c : K) = 0 := by
      rw [pow_two] at hsq
      rcases mul_eq_zero.mp hsq with h | h <;> exact h
    have hacast : (a : K) = (c : K) := sub_eq_zero.mp hdiff
    exact_mod_cast hacast

  · right
    have hn2 : 1 < n := by omega
    refine ⟨hn2, ?_⟩
    have hnK : (n : K) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hn1K : (n : K) - 1 ≠ 0 := by
      intro hz
      have hcast : (n : K) = 1 := sub_eq_zero.mp hz
      have hnat : n = 1 := by exact_mod_cast hcast
      exact hn1 hnat
    have hmid : (n : K) * ((D : K) - 1) * ((n : K) - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hnK hD1K) hn1K

    have hcube :
        (a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
            ((D : K) - (a : K) - 1) = 0 := by
      calc
        (a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
              ((D : K) - (a : K) - 1) =
            (((codimensionTwoDeparturePencil (K := K)
              (D : K) (p : K) (a : K) 1 (c : K) (n : K)).det).coeff 3).coeff 1 := by
                symm
                exact
                  coeff_s_cube_t_det_codimensionTwoDeparturePencil_leftPrimitive
                    (K := K) (D : K) (p : K) (a : K) (c : K) (n : K)
        _ = 0 := by rw [hsing]; simp
    have hacore :
        (a : K) * ((D : K) - (a : K) - 1) = 0 := by
      have hrearr :
          ((a : K) * ((D : K) - (a : K) - 1)) *
              ((n : K) * ((D : K) - 1) * ((n : K) - 1)) = 0 := by
        calc
          ((a : K) * ((D : K) - (a : K) - 1)) *
                ((n : K) * ((D : K) - 1) * ((n : K) - 1)) =
              (a : K) * (n : K) * ((D : K) - 1) * ((n : K) - 1) *
                ((D : K) - (a : K) - 1) := by ring
          _ = 0 := hcube
      exact (mul_eq_zero.mp hrearr).resolve_right hmid

    rcases mul_eq_zero.mp hacore with ha0K | haTopK
    · left
      have ha0 : a = 0 := by exact_mod_cast ha0K
      subst a
      have hcoeffP :
          -((n : K) * ((n : K) - 1) * (p : K) *
              ((D : K) - 1)^2 * ((p : K) - 1)) = 0 := by
        calc
          -((n : K) * ((n : K) - 1) * (p : K) *
                ((D : K) - 1)^2 * ((p : K) - 1)) =
              (((codimensionTwoDeparturePencil (K := K)
                (D : K) (p : K) 0 1 (c : K) (n : K)).det).coeff 2).coeff 1 := by
                  symm
                  exact
                    coeff_s_sq_t_det_codimensionTwoDeparturePencil_leftZero
                      (K := K) (D : K) (p : K) (c : K) (n : K)
          _ = 0 := by rw [hsing]; simp
      have hpK : (p : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
      have hknownP :
          (n : K) * ((n : K) - 1) * (p : K) * ((D : K) - 1)^2 ≠ 0 :=
        mul_ne_zero
          (mul_ne_zero (mul_ne_zero hnK hn1K) hpK)
          (pow_ne_zero 2 hD1K)
      have hpSub : (p : K) - 1 = 0 := by
        have hprod :
            ((n : K) * ((n : K) - 1) * (p : K) * ((D : K) - 1)^2) *
                ((p : K) - 1) = 0 := by
          have := neg_eq_zero.mp hcoeffP
          simpa [mul_assoc] using this
        exact (mul_eq_zero.mp hprod).resolve_left hknownP
      have hpCast : (p : K) = 1 := sub_eq_zero.mp hpSub
      have hp1 : p = 1 := by exact_mod_cast hpCast
      subst p

      have hcoeffC :
          (c : K) * (n : K) * ((D : K) - 1)^2 *
              ((c : K) + (n : K) - 1) = 0 := by
        calc
          (c : K) * (n : K) * ((D : K) - 1)^2 *
                ((c : K) + (n : K) - 1) =
              (((codimensionTwoDeparturePencil (K := K)
                (D : K) 1 0 1 (c : K) (n : K)).det).coeff 2).coeff 2 := by
                  symm
                  exact
                    coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_leftZero_baseOne
                      (K := K) (D : K) (c : K) (n : K)
          _ = 0 := by rw [hsing]; simp
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
          (n : K) * ((D : K) - 1)^2 * ((c : K) + (n : K) - 1) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hnK (pow_ne_zero 2 hD1K)) hlastC
      have hcK : (c : K) = 0 := by
        have hrearr :
            (c : K) *
                ((n : K) * ((D : K) - 1)^2 * ((c : K) + (n : K) - 1)) = 0 := by
          simpa [mul_assoc] using hcoeffC
        exact (mul_eq_zero.mp hrearr).resolve_right hknownC
      have hc0 : c = 0 := by exact_mod_cast hcK
      exact ⟨rfl, rfl, hc0⟩

    · right
      have haCast : (a : K) = (D : K) - 1 := by
        linear_combination haTopK
      have hDm1Cast : ((D - 1 : ℕ) : K) = (D : K) - 1 := by
        rw [Nat.cast_sub hD1Nat]
        norm_num
      have haCast' : (a : K) = ((D - 1 : ℕ) : K) := by
        rw [hDm1Cast]
        exact haCast
      have haTop : a = D - 1 := by exact_mod_cast haCast'
      subst a

      have hcoeffP :
          -((n : K) * ((n : K) - 1) * ((D : K) - 1)^2 *
              ((p : K) - (D : K)) * ((p : K) - (D : K) + 1)) = 0 := by
        calc
          -((n : K) * ((n : K) - 1) * ((D : K) - 1)^2 *
                ((p : K) - (D : K)) * ((p : K) - (D : K) + 1)) =
              (((codimensionTwoDeparturePencil (K := K)
                (D : K) (p : K) ((D : K)-1) 1 (c : K) (n : K)).det).coeff 2).coeff 1 := by
                  symm
                  exact
                    coeff_s_sq_t_det_codimensionTwoDeparturePencil_leftTop
                      (K := K) (D : K) (p : K) (c : K) (n : K)
          _ = 0 := by
            have hsing' := hsing
            simpa [hDm1Cast] using congrArg
              (fun Q : Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) => Q.det)
              (by rfl :
                codimensionTwoDeparturePencil (K := K)
                  (D : K) (p : K) ((D - 1 : ℕ) : K) 1 (c : K) (n : K) =
                codimensionTwoDeparturePencil (K := K)
                  (D : K) (p : K) ((D - 1 : ℕ) : K) 1 (c : K) (n : K))
              |>.trans hsing'
      have hpDne : p ≠ D := by omega
      have hpDcast : (p : K) - (D : K) ≠ 0 := by
        intro hz
        have heq : (p : K) = (D : K) := sub_eq_zero.mp hz
        have : p = D := by exact_mod_cast heq
        exact hpDne this
      have hknownP :
          (n : K) * ((n : K) - 1) * ((D : K) - 1)^2 *
              ((p : K) - (D : K)) ≠ 0 :=
        mul_ne_zero
          (mul_ne_zero (mul_ne_zero hnK hn1K) (pow_ne_zero 2 hD1K))
          hpDcast
      have hpTopEq : (p : K) - (D : K) + 1 = 0 := by
        have hprod :
            ((n : K) * ((n : K) - 1) * ((D : K) - 1)^2 *
                ((p : K) - (D : K))) *
                ((p : K) - (D : K) + 1) = 0 := by
          have := neg_eq_zero.mp hcoeffP
          simpa [mul_assoc] using this
        exact (mul_eq_zero.mp hprod).resolve_left hknownP
      have hpCast : (p : K) = (D : K) - 1 := by
        linear_combination hpTopEq
      have hpCast' : (p : K) = ((D - 1 : ℕ) : K) := by
        rw [hDm1Cast]
        exact hpCast
      have hpTop : p = D - 1 := by exact_mod_cast hpCast'
      subst p

      have hcoeffC :
          (n : K) * ((D : K) - 1)^2 *
              ((c : K) + 1 - (D : K)) *
              ((c : K) + (n : K) - (D : K)) = 0 := by
        calc
          (n : K) * ((D : K) - 1)^2 *
                ((c : K) + 1 - (D : K)) *
                ((c : K) + (n : K) - (D : K)) =
              (((codimensionTwoDeparturePencil (K := K)
                (D : K) ((D : K)-1) ((D : K)-1) 1 (c : K) (n : K)).det).coeff 2).coeff 2 := by
                  symm
                  exact
                    coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_leftTop_baseTop
                      (K := K) (D : K) (c : K) (n : K)
          _ = 0 := by
            simpa [hDm1Cast] using hsing
      have hc1ltD : c + 1 < D := by omega
      have hc1neD : c + 1 ≠ D := by omega
      have hc1Cast : (c : K) + 1 - (D : K) ≠ 0 := by
        intro hz
        have heq : (c : K) + 1 = (D : K) := sub_eq_zero.mp hz
        have hnat : c + 1 = D := by exact_mod_cast heq
        exact hc1neD hnat
      have hknownC :
          (n : K) * ((D : K) - 1)^2 * ((c : K) + 1 - (D : K)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hnK (pow_ne_zero 2 hD1K)) hc1Cast
      have hcTopEq : (c : K) + (n : K) - (D : K) = 0 := by
        have hprod :
            ((n : K) * ((D : K) - 1)^2 * ((c : K) + 1 - (D : K))) *
                ((c : K) + (n : K) - (D : K)) = 0 := by
          simpa [mul_assoc] using hcoeffC
        exact (mul_eq_zero.mp hprod).resolve_left hknownC
      have hcSumCast : (c : K) + (n : K) = (D : K) := sub_eq_zero.mp hcTopEq
      have hcSum : c + n = D := by exact_mod_cast hcSumCast
      have hnD : n ≤ D := by omega
      have hcFinal : c = D - n := by omega
      exact ⟨rfl, rfl, hcFinal⟩

end

end HC4.Polynomial
