import HC4.Polynomial.MonomialHessian
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# Principal Hessian minors of a monomial

For a monomial `c x^d`, evaluation at the all-ones point turns a principal
`2 x 2` Hessian minor in distinct coordinates `i,j` into

    c^2 * d_i * d_j * (1 - d_i - d_j).

Hence over a characteristic-zero field any two distinct coordinates occurring
positively in the monomial already give a nonzero principal Hessian minor.
This is the local algebra used to simplify the A19.55 codimension-two exposed
vertex branch: only a pure-axis exposed vertex can fail to provide rank-two
Hessian geometry immediately.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

/-- Evaluation at one of a monomial principal Hessian minor in two distinct
coordinates. -/
theorem eval_one_hessianPrincipalMinor_monomial
    {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) (c : K) (i j : Fin 4)
    (hij : i ≠ j) :
    MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (hessianPrincipalMinor (MvPolynomial.monomial d c) i j) =
      c ^ 2 * (d i : K) * (d j : K) *
        (1 - (d i : K) - (d j : K)) := by
  unfold hessianPrincipalMinor
  have hh := eval_one_hessian_monomial (K := K) d c
  have hii := congrFun (congrFun hh i) i
  have hjj := congrFun (congrFun hh j) j
  have hij' := congrFun (congrFun hh i) j
  have hji := congrFun (congrFun hh j) i
  change MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
      (hessian (MvPolynomial.monomial d c) i i) =
        (c • exponentHessianCore (K := K) d) i i at hii
  change MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
      (hessian (MvPolynomial.monomial d c) j j) =
        (c • exponentHessianCore (K := K) d) j j at hjj
  change MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
      (hessian (MvPolynomial.monomial d c) i j) =
        (c • exponentHessianCore (K := K) d) i j at hij'
  change MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
      (hessian (MvPolynomial.monomial d c) j i) =
        (c • exponentHessianCore (K := K) d) j i at hji
  simp only [map_sub, map_mul]
  rw [hii, hjj, hij', hji]
  simp [exponentHessianCore, hij, Ne.symm hij]
  ring

/-- Any two distinct positive exponent coordinates of a nonzero monomial give
a nonzero principal `2 x 2` Hessian minor in characteristic zero. -/
theorem hessianPrincipalMinor_monomial_ne_zero_of_two_positive
    {K : Type*} [Field K] [CharZero K]
    {d : Fin 4 →₀ ℕ} {c : K} {i j : Fin 4}
    (hc : c ≠ 0)
    (hij : i ≠ j)
    (hi : 0 < d i)
    (hj : 0 < d j) :
    hessianPrincipalMinor (MvPolynomial.monomial d c) i j ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun _ : Fin 4 => (1 : K))) hzero
  rw [eval_one_hessianPrincipalMinor_monomial (K := K) d c i j hij] at heval
  simp only [map_zero] at heval
  have hci : c ^ 2 * (d i : K) * (d j : K) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero 2 hc
      · exact_mod_cast (Nat.ne_of_gt hi)
    · exact_mod_cast (Nat.ne_of_gt hj)
  have hsumNat : 1 < d i + d j := by omega
  have hlast : 1 - (d i : K) - (d j : K) ≠ 0 := by
    intro hz
    have heq : (d i : K) + (d j : K) = 1 := by
      calc
        (d i : K) + (d j : K) =
            1 - (1 - (d i : K) - (d j : K)) := by ring
        _ = 1 := by rw [hz]; ring
    have hnat : d i + d j = 1 := by exact_mod_cast heq
    omega
  exact (mul_ne_zero hci hlast) heval

end

end HC4.Polynomial
