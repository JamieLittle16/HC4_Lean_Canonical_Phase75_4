import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import Mathlib.Tactic

/-!
# A18.5.52: a single vanishing transverse direction forces a second one or homogeneity

After A18.5.35 the autonomous target is

    T(rho) = rho + T₂ rho²,       T₂ * D + 1 = 0.

A18.5.41 used the highest raw coefficient.  If one transverse affine direction
already vanishes, the next coefficient is decisive.  For example `Q=0` gives

    -A R S (1+R+S) (A*T₂ - T₂ - 1).

The final factor cannot vanish when `A>0` and `D>0`, because together with
`T₂*D+1=0` it would force `A+D=1`.  Hence `Q=0` forces `R=0`, `S=0`, or
`1+R+S=0`.  The other two statements are cyclic.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 8000000

/-- Raw fourth-coefficient identity when `Q=0`. -/
theorem coeff_four_rankThree_raw_Q_zero
    (A B C R S t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 0 R S -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 0 R S).coeff 4) =
      -(A * R * S * (1 + R + S) * (A * t - t - 1)) := by
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
      HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

/-- Raw fourth-coefficient identity when `R=0`. -/
theorem coeff_four_rankThree_raw_R_zero
    (A B C Q S t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 Q 0 S -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 Q 0 S).coeff 4) =
      -(B * Q * S * (1 + Q + S) * (B * t - t - 1)) := by
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
      HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

/-- Raw fourth-coefficient identity when `S=0`. -/
theorem coeff_four_rankThree_raw_S_zero
    (A B C Q R t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 Q R 0 -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 Q R 0).coeff 4) =
      -(C * Q * R * (1 + Q + R) * (C * t - t - 1)) := by
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
      HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

/-- The factor `N*T₂-T₂-1` is nonzero under the terminal top relation. -/
theorem terminal_quadratic_aux_factor_ne_zero
    {N D : ℕ} {t : K}
    (hN : 0 < N) (hD : 0 < D)
    (htop : t * (D : K) + 1 = 0) :
    (N : K) * t - t - 1 ≠ 0 := by
  intro hfactor
  have hsum : (N : K) + (D : K) = 1 := by
    linear_combination
      - (D : K) * hfactor + ((N : K) - 1) * htop
  have hsumNat : N + D = 1 := by
    exact_mod_cast hsum
  omega

/-- A terminal with `Q=0` has a second zero transverse direction or preserves
ordinary degree. -/
theorem rankThree_terminal_Q_zero_refines
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hQ : Q = 0) :
    R = 0 ∨ S = 0 ∨ 1 + R + S = 0 := by
  subst Q
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R S
  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw :=
    (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hzero :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw = 0 :=
    sub_eq_zero.mpr hrawShape
  have hcoeff :
      ((Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw).coeff 4 = 0 := by
    rw [hzero]
    simp
  dsimp [Draw, Nraw] at hcoeff
  have hformula := coeff_four_rankThree_raw_Q_zero
    (A : K) (B : K) (C : K) R S (T.coeff 2)
  rw [hformula] at hcoeff
  simp only [neg_eq_zero] at hcoeff
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have haux : (A : K) * T.coeff 2 - T.coeff 2 - 1 ≠ 0 :=
    terminal_quadratic_aux_factor_ne_zero hA hphiDeg htop'
  rcases mul_eq_zero.mp hcoeff with hleft | haux0
  · rcases mul_eq_zero.mp hleft with hleft | hsum
    · rcases mul_eq_zero.mp hleft with hleft | hS
      · rcases mul_eq_zero.mp hleft with hA' | hR
        · exact (hA0 hA').elim
        · exact Or.inl hR
      · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr hsum)
  · exact (haux haux0).elim

/-- Cyclic refinement when `R=0`. -/
theorem rankThree_terminal_R_zero_refines
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hR : R = 0) :
    Q = 0 ∨ S = 0 ∨ 1 + Q + S = 0 := by
  subst R
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 S
  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw :=
    (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hzero :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw = 0 :=
    sub_eq_zero.mpr hrawShape
  have hcoeff :
      ((Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw).coeff 4 = 0 := by
    rw [hzero]
    simp
  dsimp [Draw, Nraw] at hcoeff
  have hformula := coeff_four_rankThree_raw_R_zero
    (A : K) (B : K) (C : K) Q S (T.coeff 2)
  rw [hformula] at hcoeff
  simp only [neg_eq_zero] at hcoeff
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have haux : (B : K) * T.coeff 2 - T.coeff 2 - 1 ≠ 0 :=
    terminal_quadratic_aux_factor_ne_zero hB hphiDeg htop'
  rcases mul_eq_zero.mp hcoeff with hleft | haux0
  · rcases mul_eq_zero.mp hleft with hleft | hsum
    · rcases mul_eq_zero.mp hleft with hleft | hS
      · rcases mul_eq_zero.mp hleft with hB' | hQ
        · exact (hB0 hB').elim
        · exact Or.inl hQ
      · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr hsum)
  · exact (haux haux0).elim

/-- Cyclic refinement when `S=0`. -/
theorem rankThree_terminal_S_zero_refines
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hS : S = 0) :
    Q = 0 ∨ R = 0 ∨ 1 + Q + R = 0 := by
  subst S
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R 0 b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R 0
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R 0
  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw :=
    (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hzero :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw = 0 :=
    sub_eq_zero.mpr hrawShape
  have hcoeff :
      ((Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw).coeff 4 = 0 := by
    rw [hzero]
    simp
  dsimp [Draw, Nraw] at hcoeff
  have hformula := coeff_four_rankThree_raw_S_zero
    (A : K) (B : K) (C : K) Q R (T.coeff 2)
  rw [hformula] at hcoeff
  simp only [neg_eq_zero] at hcoeff
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have haux : (C : K) * T.coeff 2 - T.coeff 2 - 1 ≠ 0 :=
    terminal_quadratic_aux_factor_ne_zero hC hphiDeg htop'
  rcases mul_eq_zero.mp hcoeff with hleft | haux0
  · rcases mul_eq_zero.mp hleft with hleft | hsum
    · rcases mul_eq_zero.mp hleft with hleft | hR
      · rcases mul_eq_zero.mp hleft with hC' | hQ
        · exact (hC0 hC').elim
        · exact Or.inl hQ
      · exact Or.inr (Or.inl hR)
    · exact Or.inr (Or.inr hsum)
  · exact (haux haux0).elim

end

end HC4.RationalRigidity