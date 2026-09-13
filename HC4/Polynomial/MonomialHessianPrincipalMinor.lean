import HC4.Polynomial.MonomialHessian
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# Principal Hessian minors of a monomial

For a monomial `c x^d`, evaluation at the all-ones point turns a principal
`2 x 2` Hessian minor in coordinates `i,j` into

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

/-- Evaluation at one of a monomial principal Hessian minor. -/
theorem eval_one_hessianPrincipalMinor_monomial
    {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) (c : K) (i j : Fin 4) :
    MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (hessianPrincipalMinor (MvPolynomial.monomial d c) i j) =
      c ^ 2 * (d i : K) * (d j : K) *
        (1 - (d i : K) - (d j : K)) := by
  unfold hessianPrincipalMinor
  have hh := eval_one_hessian_monomial (K := K) d c
  have hii := congrFun (congrFun hh i) i
  have hjj := congrFun (congrFun hh j) j
  have hij := congrFun (congrFun hh i) j
  have hji := congrFun (congrFun hh j) i
  simp only [Matrix.map_apply, smul_eq_mul] at hii hjj hij hji
  simp only [map_sub, map_mul]
  rw [hii, hjj, hij, hji]
  by_cases hijEq : i = j
  · subst j
    simp [exponentHessianCore]
  · simp [exponentHessianCore, hijEq, Ne.symm hijEq]
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
  rw [eval_one_hessianPrincipalMinor_monomial] at heval
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
    have heq : (d i : K) + (d j : K) = 1 := by linear_combination hz
    have hnat : d i + d j = 1 := by exact_mod_cast heq
    omega
  exact (mul_ne_zero hci hlast) heval

end

end HC4.Polynomial
