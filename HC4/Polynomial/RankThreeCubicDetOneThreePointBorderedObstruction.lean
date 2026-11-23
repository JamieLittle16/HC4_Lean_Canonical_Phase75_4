import HC4.Polynomial.RankThreeCubicPrincipalCofactorThreeScale
import Mathlib.Tactic

/-!
# Three determinant-one evaluations exclude a rank-two leading transverse pencil

An algebraic bridge for the remaining source cubic-pole obstruction.

Suppose three symmetric bordered 4x4 matrices Bzero, Bplus,
Bminus have determinant one and the SAME nonzero transverse
kernel direction w. Their transverse blocks are respectively
T, T+A and T-A, and their longitudinal responses to w all
equal one scalar g.

Then at every index k with w[k] != 0 the leading cubic
cofactor adj(A)[k,k] must vanish.

The proof only uses:
* determinant-one bordered kernel/cofactor square identity;
* nonzero longitudinal response of an invertible border;
* three-scale polarization of the principal cofactor.

The next source bridge must instantiate these three matrices by
the original Hessian of F at (a,0), (a,z) and (a,-z) for z on
the ACTUAL linear pole plane. No such extra assumption is
made in this standalone algebra lemma.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev BI (K : Type*) [Field K] :=
  Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K

/-- An exact finite-evaluation obstruction: the quadratic
principal cofactor of A cannot survive if the full Hessian
has det=1 at three symmetric transverse scales with a
fixed kernel and fixed longitudinal coupling. -/
theorem detOne_threePoint_borderedKernel_leadingCofactor_zero
    (Bzero Bplus Bminus : BI K)
    (hSym0 : Bzero.IsSymm)
    (hSymPlus : Bplus.IsSymm)
    (hSymMinus : Bminus.IsSymm)
    (hdet0 : Bzero.det = 1)
    (hdetPlus : Bplus.det = 1)
    (hdetMinus : Bminus.det = 1)
    (T A : Matrix (Fin 3) (Fin 3) K)
    (hT0 : Bzero.submatrix Sum.inr Sum.inr = T)
    (hTplus : Bplus.submatrix Sum.inr Sum.inr = T + A)
    (hTminus : Bminus.submatrix Sum.inr Sum.inr = T - A)
    (w : Fin 3 → K) (hw : w ≠ 0)
    (hrows0 : ∀ i : Fin 3,
      (∑ j : Fin 3, Bzero (.inr i) (.inr j) * w j) = 0)
    (hrowsPlus : ∀ i : Fin 3,
      (∑ j : Fin 3, Bplus (.inr i) (.inr j) * w j) = 0)
    (hrowsMinus : ∀ i : Fin 3,
      (∑ j : Fin 3, Bminus (.inr i) (.inr j) * w j) = 0)
    (g : K)
    (hpair0 :
      (∑ j : Fin 3, Bzero (.inl ()) (.inr j) * w j) = g)
    (hpairPlus :
      (∑ j : Fin 3, Bplus (.inl ()) (.inr j) * w j) = g)
    (hpairMinus :
      (∑ j : Fin 3, Bminus (.inl ()) (.inr j) * w j) = g)
    (k : Fin 3) (hwk : w k ≠ 0) :
    A.adjugate k k = 0 := by
  classical
  have hB0ne : Bzero.det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hg : g ≠ 0 := by
    have hcouple :=
      borderedInvertible_transverseKernel_longitudinalPairing_ne_zero
        Bzero hB0ne w hw hrows0
    simpa only [hpair0] using hcouple
  obtain ⟨_, h0⟩ :=
    detOne_borderedKernel_principalCofactor_couplingSquare
      Bzero hSym0 hdet0 w hw hrows0 k hwk
  obtain ⟨_, hplus⟩ :=
    detOne_borderedKernel_principalCofactor_couplingSquare
      Bplus hSymPlus hdetPlus w hw hrowsPlus k hwk
  obtain ⟨_, hminus⟩ :=
    detOne_borderedKernel_principalCofactor_couplingSquare
      Bminus hSymMinus hdetMinus w hw hrowsMinus k hwk
  have h0' : T.adjugate k k * g ^ 2 = -(w k ^ 2) := by
    simpa only [hT0, hpair0] using h0
  have hp' : (T + A).adjugate k k * g ^ 2 = -(w k ^ 2) := by
    simpa only [hTplus, hpairPlus] using hplus
  have hm' : (T - A).adjugate k k * g ^ 2 = -(w k ^ 2) := by
    simpa only [hTminus, hpairMinus] using hminus
  exact principalCofactor_threeScale_square_forces_zero
    T A k g (w k) hg h0' hp' hm'

end
end HC4.Polynomial.RankThreeCubic
