import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import HC4.Polynomial.RankThreeAffineLineRealisation
import HC4.Polynomial.FourExponent
import Mathlib.Tactic

/-!
# A18.5.36: the far endpoint of a genuine affine rank-three edge is on the toric boundary

A18.5.35 writes the polynomial autonomous target as

    T(rho) = rho + A₂ rho²,
    A₂ * D + 1 = 0,

where `D = natDegree phi`.  Hence `T(D)=0`.  The exact raw-target identity
`T * D_raw = N_raw` then gives `N_raw(D)=0`.

For an honest affine rank-three line, `rho=D` is the exponent of the top
supported coefficient.  The raw numerator is

    (product of its four exponent coordinates) *
      (1 - sum of its four exponent coordinates).

If that natural exponent were interior, all four coordinates would be
positive, so the product would be nonzero and the sum would be at least four.
The displayed vanishing would instead force the sum to be one, a
contradiction.  Thus the far endpoint is again on the toric boundary.

This recovers the boundary-to-boundary Newton edge directly from the terminal
ODE, without an analytic infinity argument.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Top endpoint boundary theorem for an honest affine rank-three edge.** -/
theorem rankThreeAffineLine_topExponent_on_boundary_of_certificate
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C P Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    MvExponentOnBoundary (L.exponent phi.natDegree) := by
  have hpackage := exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
    hA hB hC hP hphiDeg hphi0 hcert
  rcases hpackage with
    ⟨hPone, hphi1, b, hb, hden, hidentity, hdegT, hT0, hT1, htop⟩

  let D : ℕ := phi.natDegree
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b

  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphiDeg
  have hDmem : D ∈ phi.support := by
    rw [Polynomial.mem_support_iff]
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi

  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)

  have hTD : Polynomial.eval (D : K) T = 0 := by
    rw [hshape]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
    have htop' : T.coeff 2 * (D : K) + 1 = 0 := by
      simpa [T, D] using htop
    rw [hT1']
    linear_combination (D : K) * htop'

  have hraw := rankThreeAutonomousPolynomial_mul_rawDenominator
    (K := K) hA hB hC hP hb hden
  have hev := congrArg (Polynomial.eval (D : K)) hraw
  have hNzero :
      Polynomial.eval (D : K)
        (rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S) = 0 := by
    simpa [T, D, hTD] using hev.symm
  rw [eval_rankThreeEtaNumeratorPolynomial] at hNzero

  let e := L.exponent D
  have haff := L.affine D hDmem
  have he0 : ((e 0 : ℕ) : K) = (D : K) * (P : K) := by
    simpa [e, rankThreeLogBaseExponent, rankThreeLogDirection] using
      congrFun haff (0 : Fin 4)
  have he1 : ((e 1 : ℕ) : K) = (A : K) + (D : K) * Q := by
    simpa [e, rankThreeLogBaseExponent, rankThreeLogDirection] using
      congrFun haff (1 : Fin 4)
  have he2 : ((e 2 : ℕ) : K) = (B : K) + (D : K) * R := by
    simpa [e, rankThreeLogBaseExponent, rankThreeLogDirection] using
      congrFun haff (2 : Fin 4)
  have he3 : ((e 3 : ℕ) : K) = (C : K) + (D : K) * S := by
    simpa [e, rankThreeLogBaseExponent, rankThreeLogDirection] using
      congrFun haff (3 : Fin 4)

  have hNexp :
      (((e 0 : ℕ) : K) * ((e 1 : ℕ) : K) *
          ((e 2 : ℕ) : K) * ((e 3 : ℕ) : K)) *
        (1 - ((e 0 : ℕ) : K) - ((e 1 : ℕ) : K) -
          ((e 2 : ℕ) : K) - ((e 3 : ℕ) : K)) = 0 := by
    unfold rankThreeEtaNumerator rankThreeLogProduct rankThreeLogSum at hNzero
    rw [← he0, ← he1, ← he2, ← he3] at hNzero
    ring_nf at hNzero ⊢
    exact hNzero

  rw [mvExponentOnBoundary_iff_coordinate_zero]
  by_contra hboundary
  push_neg at hboundary
  rcases hboundary with ⟨he0ne, he1ne, he2ne, he3ne⟩
  have he0K : ((e 0 : ℕ) : K) ≠ 0 := by exact_mod_cast he0ne
  have he1K : ((e 1 : ℕ) : K) ≠ 0 := by exact_mod_cast he1ne
  have he2K : ((e 2 : ℕ) : K) ≠ 0 := by exact_mod_cast he2ne
  have he3K : ((e 3 : ℕ) : K) ≠ 0 := by exact_mod_cast he3ne
  have hprod :
      ((e 0 : ℕ) : K) * ((e 1 : ℕ) : K) *
          ((e 2 : ℕ) : K) * ((e 3 : ℕ) : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero he0K he1K) he2K) he3K
  have hsum :
      (1 : K) - ((e 0 : ℕ) : K) - ((e 1 : ℕ) : K) -
          ((e 2 : ℕ) : K) - ((e 3 : ℕ) : K) = 0 :=
    (mul_eq_zero.mp hNexp).resolve_left hprod
  have hsumK :
      (((e 0 + e 1 + e 2 + e 3 : ℕ) : K)) = 1 := by
    push_cast
    linear_combination -hsum
  have hsumNat : e 0 + e 1 + e 2 + e 3 = 1 := by
    exact_mod_cast hsumK
  have hp0 : 0 < e 0 := Nat.pos_of_ne_zero he0ne
  have hp1 : 0 < e 1 := Nat.pos_of_ne_zero he1ne
  have hp2 : 0 < e 2 := Nat.pos_of_ne_zero he2ne
  have hp3 : 0 < e 3 := Nat.pos_of_ne_zero he3ne
  omega

end

end HC4.RationalRigidity
