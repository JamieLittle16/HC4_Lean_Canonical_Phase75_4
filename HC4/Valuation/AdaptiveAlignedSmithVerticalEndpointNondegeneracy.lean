import HC4.Valuation.AdaptiveAlignedSmithVerticalFiber
import HC4.Newton.InteriorVertex
import HC4.RationalRigidity.RankThreeVerticalLineTerminal
import Mathlib.Tactic

/-!
# A18.5.14: automatic endpoint nondegeneracy for vertical rank-three lines

The vertical terminal theorem A18.5.12 was deliberately stated with the two
one-variable endpoint hypotheses needed by the rational-rigidity stack:

* `phi.coeff 0 ≠ 0`;
* `0 < phi.natDegree`.

For the actual stationary Smith fibre these are not additional hypotheses.

If the three fixed transverse exponents `b,c,d` are positive and the honest
vertical polynomial

    x₁^b x₂^c x₃^d * phi(x₀)

has zero Hessian determinant, then the least occupied longitudinal exponent
cannot be positive.  Indeed the negative `x₀`-order weight exposes that least
term as a single nonlinear monomial.  The existing interior-vertex theorem
forces every such exposed monomial of a zero-Hessian polynomial onto the
boundary of the four-variable exponent cone.  Positivity of `b,c,d` leaves
only coordinate `0` available to vanish, so the least longitudinal exponent
is exactly zero.

Likewise two occupied longitudinal coefficients at orders `n` and `n+q`,
with `q>0`, force positive polynomial degree.  Consequently the stationary
support-pair geometry can feed A18.5.12 without separately supplying either
one-variable endpoint condition.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Weight which orders a vertical line by *least* longitudinal exponent. -/
def rankThreeVerticalTrailingWeight (i : Fin 4) : ℤ :=
  if i = 0 then -1 else 0

@[simp] theorem rankThreeVerticalTrailingWeight_zero :
    rankThreeVerticalTrailingWeight (0 : Fin 4) = -1 := by
  simp [rankThreeVerticalTrailingWeight]

@[simp] theorem rankThreeVerticalTrailingWeight_succ (j : Fin 3) :
    rankThreeVerticalTrailingWeight j.succ = 0 := by
  simp [rankThreeVerticalTrailingWeight]

/-- The trailing weight is exactly minus the longitudinal exponent. -/
theorem weight_rankThreeVerticalTrailingWeight
    (q : Fin 4 →₀ ℕ) :
    Finsupp.weight rankThreeVerticalTrailingWeight q =
      -(q (0 : Fin 4) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [rankThreeVerticalTrailingWeight]
  · intro i
    simp

/-- Positive fixed transverse exponents make a vertical support monomial
nonlinear regardless of its longitudinal exponent. -/
theorem rankThreeVerticalExponent_ordinaryDegree_ge_three
    {b c d j : ℕ}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    3 ≤ ordinaryDegree4 (rankThreeVerticalExponentFinsupp b c d j) := by
  simp [ordinaryDegree4, rankThreeVerticalExponentFinsupp_apply]
  omega

/-- **A singular vertical rank-three line has a genuine rank-three constant
endpoint.**

If `b,c,d` are positive, a nonzero vertical coefficient polynomial cannot
start at positive `x₀` order while the four-variable Hessian determinant
vanishes. -/
theorem rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
    {b c d : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphi : phi ≠ 0)
    (hdet :
      hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    phi.coeff 0 ≠ 0 := by
  intro hzero
  let m : ℕ := phi.natTrailingDegree
  have hm : 0 < m := by
    exact Nat.pos_of_ne_zero
      ((Polynomial.natTrailingDegree_ne_zero).2 ⟨hphi, hzero⟩)
  have hcm : phi.coeff m ≠ 0 := by
    exact (Polynomial.coeff_natTrailingDegree_ne_zero).2 hphi

  let F : MvPolynomial (Fin 4) K :=
    rankThreeVerticalPolynomial b c d phi
  let w : Fin 4 → ℤ := rankThreeVerticalTrailingWeight

  have hbound : IsWeightLE w (-(m : ℤ)) F := by
    intro q hq
    have hcoeff : MvPolynomial.coeff q F ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hq
    dsimp [F] at hcoeff
    rw [coeff_rankThreeVerticalPolynomial] at hcoeff
    by_cases htrans :
        q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
    · rw [if_pos htrans] at hcoeff
      have hmq : m ≤ q (0 : Fin 4) := by
        by_contra hnot
        have hlt : q (0 : Fin 4) < m := by omega
        exact hcoeff
          (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt)
      have hmqZ : (m : ℤ) ≤ (q (0 : Fin 4) : ℤ) := by
        exact_mod_cast hmq
      dsimp [w]
      rw [weight_rankThreeVerticalTrailingWeight]
      omega
    · rw [if_neg htrans] at hcoeff
      exact (hcoeff rfl).elim

  have hinit :
      initialForm w (-(m : ℤ)) F =
        MvPolynomial.monomial
          (rankThreeVerticalExponentFinsupp b c d m) (phi.coeff m) := by
    apply MvPolynomial.ext
    intro q
    rw [coeff_initialForm]
    dsimp [F]
    rw [coeff_rankThreeVerticalPolynomial]
    rw [MvPolynomial.coeff_monomial]
    by_cases heq : rankThreeVerticalExponentFinsupp b c d m = q
    · subst q
      have hw :
          Finsupp.weight w (rankThreeVerticalExponentFinsupp b c d m) =
            -(m : ℤ) := by
        dsimp [w]
        rw [weight_rankThreeVerticalTrailingWeight]
        simp [rankThreeVerticalExponentFinsupp_apply]
      have htrans :
          rankThreeVerticalExponentFinsupp b c d m (1 : Fin 4) = b ∧
          rankThreeVerticalExponentFinsupp b c d m (2 : Fin 4) = c ∧
          rankThreeVerticalExponentFinsupp b c d m (3 : Fin 4) = d := by
        simp [rankThreeVerticalExponentFinsupp_apply]
      simp [hw, htrans]
    · rw [if_neg heq]
      by_cases hw : Finsupp.weight w q = -(m : ℤ)
      · rw [if_pos hw]
        by_cases htrans :
            q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
        · rw [if_pos htrans]
          have hq0 : q (0 : Fin 4) = m := by
            dsimp [w] at hw
            rw [weight_rankThreeVerticalTrailingWeight] at hw
            omega
          exfalso
          apply heq
          ext i
          fin_cases i
          · simpa [rankThreeVerticalExponentFinsupp_apply] using hq0.symm
          · simpa [rankThreeVerticalExponentFinsupp_apply] using htrans.1.symm
          · simpa [rankThreeVerticalExponentFinsupp_apply] using htrans.2.1.symm
          · simpa [rankThreeVerticalExponentFinsupp_apply] using htrans.2.2.symm
        · simp [htrans]
      · simp [hw]

  have hboundary :
      MvExponentOnBoundary (rankThreeVerticalExponentFinsupp b c d m) := by
    apply exposed_monomial_on_boundary_of_zero_hessian
      (F := F) (w := w) (level := -(m : ℤ))
      hbound
    · simpa [F] using hdet
    · exact hinit
    · exact hcm
    · exact rankThreeVerticalExponent_ordinaryDegree_ge_three hb hc hd

  rw [mvExponentOnBoundary_iff_coordinate_zero] at hboundary
  simp [rankThreeVerticalExponentFinsupp_apply] at hboundary
  omega

/-- A genuinely later occupied coefficient forces positive univariate degree. -/
theorem polynomial_natDegree_pos_of_later_coeff_ne_zero
    {phi : Polynomial K}
    {n q : ℕ}
    (hq : 0 < q)
    (hnq : phi.coeff (n + q) ≠ 0) :
    0 < phi.natDegree := by
  have hmem : n + q ∈ phi.support :=
    Polynomial.mem_support_iff.mpr hnq
  have hle : n + q ≤ phi.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hmem
  omega

/-- **Two occupied layers plus singular vertical geometry automatically give
the complete polynomial rank-three terminal certificate.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_vertical_support_pair
    [IsAlgClosed K]
    {b c d n q : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hq : 0 < q)
    (hn : phi.coeff n ≠ 0)
    (hnq : phi.coeff (n + q) ≠ 0)
    (hdet :
      hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := phi) (b : K) (c : K) (d : K) 1 0 0 0 := by
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hn
  have hconst : phi.coeff 0 ≠ 0 :=
    rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
      hb hc hd hphi hdet
  have hdegree : 0 < phi.natDegree :=
    polynomial_natDegree_pos_of_later_coeff_ne_zero hq hnq
  exact
    HC4.RationalRigidity.hasRankThreePolynomialTerminalCertificate_of_vertical_line
      hb hc hd hdegree hconst hdet

end

end HC4.Valuation
