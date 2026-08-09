import HC4.Newton.RestartClassification
import HC4.Newton.TerminalCoordinatePermutation
import HC4.Newton.TerminalScalarGradient
import Mathlib.Tactic

/-!
# Terminal associated-graded endpoint interface

The restart proof reaches determinant closure through a Newton/Schur clock.
The clock itself is matrix-valued; the terminal endpoint theorems, however,
are statements about an actual polynomial associated-graded fibre.

This module isolates the exact *consumer* expected from the final closing
extraction.  It deliberately does not identify a Schur matrix with a
potential.

A terminal fibre is certified in one of two ways:

* the terminal weight is scalar, in which case the already-green scalar
  actual-Hessian theorem gives gradient injectivity directly;
* after a coordinate permutation the fibre is one of the already-green
  positive / one-zero / two-zero certified endpoints.

The second alternative is phrased up to permutation because the lattice
normal form naturally chooses its own coordinate ordering.  The coordinate
permutation module already proves that gradient injectivity is invariant
under this relabelling.

The final theorem says that a distinct exact collision on any such terminal
associated-graded fibre is impossible under `JC₂`.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- A terminal direct-jump endpoint, allowing the standard endpoint
certificate to be reached after an arbitrary coordinate permutation.

The scalar branch is kept explicit because `CertifiedTerminalEndpoint`
contains only the non-scalar positive / one-zero / two-zero endpoint
families. -/
inductive CertifiedTerminalDirectJumpEndpoint
    (F : MvPolynomial (Fin 4) K) : Prop
  | scalar
      (lambda : Fin 4 -> ℤ)
      (d : ℤ)
      (hscalar : IsScalarIntegralWeight lambda)
      (hnontrivial : IsNontrivialIntegralWeight lambda)
      (hhom : IsIntegralWeightedHomogeneous lambda d F)
      (hdet :
        HasNondegenerateTerminalActualHessian
          (0 : Fin 4) 1 2 3 F) :
      CertifiedTerminalDirectJumpEndpoint F
  | permuted
      (rho : Equiv.Perm (Fin 4))
      (hendpoint :
        CertifiedTerminalEndpoint
          (MvPolynomial.rename rho F)) :
      CertifiedTerminalDirectJumpEndpoint F

/-- Every certified terminal direct-jump endpoint has injective gradient
under `JC₂`.  The only invariant step needed in the permuted branch is the
already-green coordinate-permutation conjugacy theorem. -/
theorem certifiedTerminalDirectJumpEndpoint_gradient_injective_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {F : MvPolynomial (Fin 4) K}
    (hterminal : CertifiedTerminalDirectJumpEndpoint F) :
    Function.Injective (mvGradientMap F) := by
  cases hterminal with
  | scalar lambda d hscalar hnontrivial hhom hdet =>
      exact
        scalarTerminal_actualHessian_gradient_injective
          hscalar hnontrivial hhom hdet
  | permuted rho hendpoint =>
      exact
        mvGradientMap_injective_of_rename_perm
          rho F
          (certifiedTerminalEndpoint_gradient_injective_of_JC2
            hJC2 hendpoint)

/-- A distinct exact collision cannot survive a certified terminal
associated-graded endpoint under `JC₂`. -/
theorem certifiedTerminalDirectJumpEndpoint_collision_impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {F : MvPolynomial (Fin 4) K}
    (hterminal : CertifiedTerminalDirectJumpEndpoint F)
    {p q : Fin 4 -> K}
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    False := by
  exact
    exactGradientCollision_impossible_of_injective
      F p q hpq
      (certifiedTerminalDirectJumpEndpoint_gradient_injective_of_JC2
        hJC2 hterminal)
      hcoll

/-- The exact polynomial-level datum that the determinant-closing Newton
extraction must produce.

Notice that the matrix Schur clock is *not* a field of this structure.  The
construction theorem from the closing clock to this datum is precisely the
remaining geometric adapter; once such a datum exists the terminal
contradiction is automatic. -/
structure TerminalAssociatedGradedCollisionData (K : Type*) [Field K] where
  fibre : MvPolynomial (Fin 4) K
  leftPoint : Fin 4 -> K
  rightPoint : Fin 4 -> K
  distinct : leftPoint ≠ rightPoint
  exactCollision :
    HasExactGradientCollision fibre leftPoint rightPoint
  endpoint : CertifiedTerminalDirectJumpEndpoint fibre

/-- **Terminal endpoint closure.**
Any terminal associated-graded collision datum is contradictory under
`JC₂`.  No additional terminal classification appears at the restart
assembly site. -/
theorem TerminalAssociatedGradedCollisionData.impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (T : TerminalAssociatedGradedCollisionData K) :
    False := by
  exact
    certifiedTerminalDirectJumpEndpoint_collision_impossible_of_JC2
      hJC2 T.endpoint T.distinct T.exactCollision

end

end HC4.Newton
