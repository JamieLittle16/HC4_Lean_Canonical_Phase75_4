import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeHighestDirectionRelation
import HC4.RationalRigidity.RankThreeUnitLongitudinalStep
import Mathlib.Tactic

/-!
# Line-supported Hessian rigidity in the locked-ray direction

This is the state-free rigidity theorem needed by the A19 planar highest-slice
adapter.

The general rank-three rational-rigidity stack already turns an honest affine
support line with singular Hessian into a polynomial autonomous terminal and
proves the highest-direction relation

    (D - 1) Q R S (1 + Q + R + S) = 0,

where `D = natDegree phi` and `(1,Q,R,S)` is the primitive affine direction.
For the locked-ray orientation used by the A19 planar slices,

    (1,Q,R,S) = (1,-1,-1,-V),   V > 0,

the direction factor is `V(V+1)`, hence is nonzero in characteristic zero.
Therefore `D = 1`.  The already-formalised unit-longitudinal-step theorem also
shows that the coefficient at index `1` is nonzero; together with the assumed
nonzero index `0`, the coefficient support is exactly the two adjacent indices
`{0,1}`.

No A19 state object appears in this file.  In particular this result does not
use balance, a repair tag, a blocker clock, or a JC2 hypothesis.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Locked-ray degree-one rigidity.**

An honest singular rank-three affine line in primitive locked-ray direction
`(1,-1,-1,-V)`, with `V > 0`, has coefficient polynomial of natural degree
exactly one. -/
theorem lockedRay_affine_line_natDegree_eq_one
    {A B C u1 V : ℕ} {phi : Polynomial K}
    (L : RankThreeAffineLineData
      A B C u1 (-1 : K) (-1 : K) (-(V : K)) phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1) (hV : 0 < V)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    phi.natDegree = 1 := by
  have hcert := hasRankThreePolynomialTerminalCertificate_of_affine_line
    L hA hB hC hu1 hphiDeg hphi0 hdet
  have hrel := rankThree_terminal_highest_direction_relation
    (K := K) (A := A) (B := B) (C := C) (P := u1)
    (Q := (-1 : K)) (R := (-1 : K)) (S := (-(V : K)))
    (phi := phi)
    hA hB hC hu1 hphiDeg hphi0 hcert
  have hdir :
      ((-1 : K) * (-1 : K) * (-(V : K)) *
          (1 + (-1 : K) + (-1 : K) + (-(V : K)))) =
        (V : K) * ((V : K) + 1) := by
    ring
  rw [hdir] at hrel
  have hV0 : (V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hV)
  have hVp1Nat : V + 1 ≠ 0 := by omega
  have hVp1 : (V : K) + 1 ≠ 0 := by
    have hcast : ((V + 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast hVp1Nat
    simpa using hcast
  have hdir0 : (V : K) * ((V : K) + 1) ≠ 0 :=
    mul_ne_zero hV0 hVp1
  have hdegsub : (phi.natDegree : K) - 1 = 0 :=
    (mul_eq_zero.mp hrel).resolve_right hdir0
  have hdegcast : (phi.natDegree : K) = 1 := sub_eq_zero.mp hdegsub
  exact_mod_cast hdegcast

/-- **Exact adjacent coefficient support.**

Under the same hypotheses the one-variable line parameter has precisely the
occupied layers `0` and `1`.  This is the coefficient-level statement consumed
by the source-facing primitive-slice adapter. -/
theorem lockedRay_affine_line_support_eq_zero_one
    {A B C u1 V : ℕ} {phi : Polynomial K}
    (L : RankThreeAffineLineData
      A B C u1 (-1 : K) (-1 : K) (-(V : K)) phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1) (hV : 0 < V)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    phi.support = {0, 1} := by
  have hcert := hasRankThreePolynomialTerminalCertificate_of_affine_line
    L hA hB hC hu1 hphiDeg hphi0 hdet
  have hunit := rankThree_unit_longitudinal_step_of_certificate
    (K := K) (A := A) (B := B) (C := C) (P := u1)
    (Q := (-1 : K)) (R := (-1 : K)) (S := (-(V : K)))
    (phi := phi)
    hA hB hC hu1 hphiDeg hphi0 hcert
  have hphi1 : phi.coeff 1 ≠ 0 := hunit.2
  have hdeg : phi.natDegree = 1 :=
    lockedRay_affine_line_natDegree_eq_one
      L hA hB hC hu1 hV hphiDeg hphi0 hdet
  ext n
  constructor
  · intro hn
    have hnle : n ≤ phi.natDegree :=
      Polynomial.le_natDegree_of_mem_supp n hn
    rw [hdeg] at hnle
    interval_cases n <;> simp
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact Polynomial.mem_support_iff.mpr hphi0
    · exact Polynomial.mem_support_iff.mpr hphi1

end

end HC4.RationalRigidity
