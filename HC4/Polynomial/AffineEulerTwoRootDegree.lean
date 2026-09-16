import HC4.Polynomial.AffineEulerTwoRootRigidity
import Mathlib.Tactic

/-!
# Degree rigidity for affine two-root Euler solutions

The existing affine two-root theorem says that after translation to the root
of the affine linear coefficient, a solution is supported only in the two
adjacent indicial degrees `j,j+1`.

Translation by a constant preserves ordinary polynomial degree.  Therefore a
nonzero affine solution itself has natural degree exactly `j` or `j+1`.

This small state-free consequence is useful when the same source profile is
seen from two different endpoint linearisations.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero solution of the affine adjacent-root Euler equation has ordinary
degree equal to one of its two indicial roots. -/
theorem natDegree_eq_root_or_succ_of_affineTwoRoot
    (c d : K) (j : ℕ) (phi : Polynomial K)
    (hd : d ≠ 0)
    (hphi : phi ≠ 0)
    (hzero : affineTwoRootEulerOperator c d j phi = 0) :
    phi.natDegree = j ∨ phi.natDegree = j + 1 := by
  let alpha : K := -c / d
  let psi : Polynomial K := translatePolynomial alpha phi
  have hsupp : psi.support ⊆ {j, j + 1} := by
    dsimp [psi, alpha]
    exact translated_support_subset_of_affineTwoRoot c d j phi hd hzero
  have hpsi : psi ≠ 0 := by
    intro hz
    have hback := congrArg (translatePolynomial (-alpha)) hz
    have hinv : translatePolynomial (-alpha) psi = phi := by
      dsimp [psi]
      simp [translatePolynomial, Polynomial.comp_assoc]
    rw [hinv] at hback
    simp [translatePolynomial] at hback
    exact hphi hback
  have hdeg : psi.natDegree = phi.natDegree := by
    dsimp [psi, translatePolynomial]
    rw [Polynomial.natDegree_comp]
    simp
  have hmem : psi.natDegree ∈ psi.support :=
    Polynomial.natDegree_mem_support_of_nonzero hpsi
  have hallowed := hsupp hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hallowed
  rw [hdeg] at hallowed
  exact hallowed

end

end HC4.Polynomial
