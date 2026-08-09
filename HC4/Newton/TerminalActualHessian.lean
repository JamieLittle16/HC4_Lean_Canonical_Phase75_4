import HC4.Newton.TerminalQuadraticHessian
import HC4.Newton.ExactCollisionFirstWall
import Mathlib.Tactic

/-!
# Actual terminal Hessian at the origin

Phase 93.23 gives a coefficient-level quadratic Hessian and shows that a
nondegenerate such matrix supplies the quadratic coefficient witness needed
by the scalar terminal weight theorem.

For the restart application it is cleaner to connect directly to the
*actual* Hessian at the terminal base point.

Define

    Hess(F, point)_{ij}
      = eval_point (pderiv i (pderiv j F)).

The key local observation is that a nonzero second derivative at the
origin can only receive a contribution from the quadratic monomial
`X_i X_j`.  We prove this from the exact `pderiv_monomial` formula, without
using any unavailable coefficient-of-derivative convenience theorem.

Consequently,

    det (actual Hess F at 0) != 0

implies that some genuine quadratic coefficient `[X_i X_j]F` is nonzero.
This is exactly the witness required by the green Phase 93.22 scalar
terminal theorem.

Thus the scalar terminal branch now accepts the actual Hessian determinant
supplied by determinant closure directly.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- One entry of the actual polynomial Hessian evaluated at a point. -/
def mvHessianComponentAt
    (point : σ -> K)
    (F : MvPolynomial σ K)
    (i j : σ) : K :=
  MvPolynomial.eval point
    (MvPolynomial.pderiv i
      (MvPolynomial.pderiv j F))

/-- Contribution of one support monomial to one evaluated Hessian entry. -/
def hessianMonomialContributionAt
    (point : σ -> K)
    (F : MvPolynomial σ K)
    (i j : σ)
    (d : σ →₀ ℕ) : K :=
  MvPolynomial.eval point
    (MvPolynomial.pderiv i
      (MvPolynomial.pderiv j
        (MvPolynomial.monomial d
          (MvPolynomial.coeff d F))))

/-- The evaluated Hessian entry is the finite sum of the Hessian
contributions of the support monomials. -/
theorem mvHessianComponentAt_eq_sum_support
    (point : σ -> K)
    (F : MvPolynomial σ K)
    (i j : σ) :
    mvHessianComponentAt point F i j =
      F.support.sum
        (fun d =>
          hessianMonomialContributionAt
            point F i j d) := by
  classical
  unfold mvHessianComponentAt
  calc
    MvPolynomial.eval point
        (MvPolynomial.pderiv i
          (MvPolynomial.pderiv j F)) =
      MvPolynomial.eval point
        (MvPolynomial.pderiv i
          (MvPolynomial.pderiv j
            (F.support.sum
              (fun d =>
                MvPolynomial.monomial d
                  (MvPolynomial.coeff d F))))) := by
        exact congrArg
          (fun P : MvPolynomial σ K =>
            MvPolynomial.eval point
              (MvPolynomial.pderiv i
                (MvPolynomial.pderiv j P)))
          F.as_sum
    _ =
      F.support.sum
        (fun d =>
          hessianMonomialContributionAt
            point F i j d) := by
        rw [map_sum
          (MvPolynomial.pderiv j)
          (fun d =>
            MvPolynomial.monomial d
              (MvPolynomial.coeff d F))
          F.support]
        rw [map_sum
          (MvPolynomial.pderiv i)
          (fun d =>
            MvPolynomial.pderiv j
              (MvPolynomial.monomial d
                (MvPolynomial.coeff d F)))
          F.support]
        rw [map_sum
          (MvPolynomial.eval point)
          (fun d =>
            MvPolynomial.pderiv i
              (MvPolynomial.pderiv j
                (MvPolynomial.monomial d
                  (MvPolynomial.coeff d F))))
          F.support]
        rfl

/-- If one monomial makes a nonzero contribution to the `(i,j)` Hessian
entry at the origin, then its exponent is exactly the quadratic exponent
`X_i X_j`. -/
theorem hessianMonomialContributionAt_origin_ne_zero_exponent_eq
    (F : MvPolynomial σ K)
    (i j : σ)
    (d : σ →₀ ℕ)
    (hne :
      hessianMonomialContributionAt
        (fun _ => (0 : K)) F i j d ≠ 0) :
    d = quadraticExponent i j := by
  classical
  unfold hessianMonomialContributionAt at hne
  simp only [MvPolynomial.pderiv_monomial] at hne
  rw [MvPolynomial.eval_zero'] at hne
  rw [MvPolynomial.constantCoeff_monomial] at hne

  have hsub :
      (d - Finsupp.single j 1) -
          Finsupp.single i 1 = 0 := by
    by_contra hsubne
    rw [if_neg hsubne] at hne
    exact hne rfl

  rw [if_pos hsub] at hne

  let dAfterJ : σ →₀ ℕ :=
    d - Finsupp.single j 1

  have hsubAfter :
      dAfterJ - Finsupp.single i 1 = 0 := by
    simpa [dAfterJ] using hsub

  have hneAfter :
      MvPolynomial.coeff d F *
          (d j : K) *
          (dAfterJ i : K) ≠ 0 := by
    simpa [dAfterJ] using hne

  have hdjK : (d j : K) ≠ 0 := by
    intro hz
    apply hneAfter
    simp [hz]

  have hdiAfterK :
      (dAfterJ i : K) ≠ 0 := by
    intro hz
    apply hneAfter
    simp [hz]

  have hdj : d j ≠ 0 := by
    intro hz
    apply hdjK
    simp [hz]

  have hdiAfter :
      dAfterJ i ≠ 0 := by
    intro hz
    apply hdiAfterK
    simp [hz]

  by_cases hij : i = j
  · subst j
    have hafterPos :
        0 < dAfterJ i :=
      Nat.pos_of_ne_zero hdiAfter
    apply Finsupp.ext
    intro k
    have hk :=
      congrArg
        (fun e : σ →₀ ℕ => e k)
        hsubAfter
    by_cases hki : k = i
    · subst k
      simp [dAfterJ, quadraticExponent] at hk ⊢
      have hafter :
          0 < d i - 1 := by
        simpa [dAfterJ] using hafterPos
      omega
    · simp [dAfterJ, quadraticExponent,
        hki, Ne.symm hki] at hk ⊢
      omega
  · have hdi : d i ≠ 0 := by
      simpa [dAfterJ, hij, Ne.symm hij] using hdiAfter
    have hdiPos : 0 < d i :=
      Nat.pos_of_ne_zero hdi
    have hdjPos : 0 < d j :=
      Nat.pos_of_ne_zero hdj
    apply Finsupp.ext
    intro k
    have hk :=
      congrArg
        (fun e : σ →₀ ℕ => e k)
        hsubAfter
    by_cases hki : k = i
    · subst k
      simp [dAfterJ, quadraticExponent,
        hij, Ne.symm hij] at hk ⊢
      omega
    · by_cases hkj : k = j
      · subst k
        simp [dAfterJ, quadraticExponent,
          hij, Ne.symm hij] at hk ⊢
        omega
      · simp [dAfterJ, quadraticExponent,
          hki, hkj,
          Ne.symm hki, Ne.symm hkj] at hk ⊢
        omega

/-- A nonzero actual Hessian entry at the origin forces the corresponding
quadratic coefficient to be nonzero. -/
theorem mvHessianComponentAt_origin_ne_zero_quadraticCoeff
    (F : MvPolynomial σ K)
    (i j : σ)
    (hentry :
      mvHessianComponentAt
        (fun _ => (0 : K)) F i j ≠ 0) :
    MvPolynomial.coeff
      (quadraticExponent i j) F ≠ 0 := by
  rw [mvHessianComponentAt_eq_sum_support] at hentry
  have hex :
      ∃ d ∈ F.support,
        hessianMonomialContributionAt
          (fun _ => (0 : K)) F i j d ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hentry
    exact
      Finset.sum_eq_zero
        (fun d hd => hnone d hd)
  rcases hex with ⟨d, hd, hcontrib⟩
  have hdq :
      d = quadraticExponent i j :=
    hessianMonomialContributionAt_origin_ne_zero_exponent_eq
      F i j d hcontrib
  rw [← hdq]
  exact MvPolynomial.mem_support_iff.mp hd

/-- The actual Hessian at the origin in the four selected terminal
coordinates. -/
def terminalActualHessianMatrix
    (x y z w : σ)
    (F : MvPolynomial σ K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun r c =>
    mvHessianComponentAt
      (fun _ => (0 : K))
      F
      (terminalFourCoordinate x y z w r)
      (terminalFourCoordinate x y z w c)

/-- Determinant-closing nondegeneracy of the actual terminal Hessian. -/
def HasNondegenerateTerminalActualHessian
    (x y z w : σ)
    (F : MvPolynomial σ K) : Prop :=
  Matrix.det
    (terminalActualHessianMatrix x y z w F) ≠ 0

/-- Nonzero determinant of the actual terminal Hessian supplies a genuine
quadratic coefficient witness. -/
theorem nondegenerateTerminalActualHessian_exists_quadraticCoeff
    (x y z w : σ)
    (F : MvPolynomial σ K)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    ∃ i j : σ,
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0 := by
  unfold HasNondegenerateTerminalActualHessian at hdet
  rcases
      matrix4_det_ne_zero_exists_entry_ne_zero
        (terminalActualHessianMatrix x y z w F)
        hdet with
    ⟨r, c, hentry⟩
  let i := terminalFourCoordinate x y z w r
  let j := terminalFourCoordinate x y z w c
  refine ⟨i, j, ?_⟩
  apply
    mvHessianComponentAt_origin_ne_zero_quadraticCoeff
      F i j
  exact hentry

/-- The actual determinant-closing Hessian also proves that the terminal
polynomial is nonzero. -/
theorem nondegenerateTerminalActualHessian_polynomial_ne_zero
    (x y z w : σ)
    (F : MvPolynomial σ K)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    F ≠ 0 := by
  rcases
      nondegenerateTerminalActualHessian_exists_quadraticCoeff
        x y z w F hdet with
    ⟨i, j, hcoeff⟩
  intro hF
  subst F
  simpa using hcoeff

/-- **Scalar terminal endpoint from the actual Hessian.**
No coefficient-Hessian identification is required as an extra hypothesis:
determinant closure of the actual Hessian directly supplies the quadratic
coefficient witness used by the scalar weighted-homogeneous theorem. -/
theorem scalarTerminal_actualHessian_nondegenerate_endpoint
    (x y z w : σ)
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (ha : a ≠ 0)
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    F ≠ 0 ∧ HasPureQuadraticSupport F := by
  rcases
      nondegenerateTerminalActualHessian_exists_quadraticCoeff
        x y z w F hdet with
    ⟨i, j, hquad⟩
  constructor
  · exact
      nondegenerateTerminalActualHessian_polynomial_ne_zero
        x y z w F hdet
  · exact
      scalarWeightedHomogeneous_hasPureQuadraticSupport
        ha hhom i j hquad

end

end HC4.Newton
