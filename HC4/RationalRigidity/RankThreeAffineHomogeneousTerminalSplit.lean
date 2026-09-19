import HC4.RationalRigidity.RankThreeHomogeneousDirectionFixed
import HC4.RationalRigidity.RankThreeHomogeneousOtherFixedRelations
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import HC4.Polynomial.FourExponent
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# Balance-free homogeneous affine terminal split

The coefficient relation proved in the homogeneous rank-three endgame is
itself independent of torus balance.  For a genuine affine terminal with
primitive omitted-coordinate step one it says

    Q R S (A+B+C-1) (A+B+C-D) = 0,

where `D = natDegree phi`.

If the honest affine support stays in the ordinary degree of its rank-three
base exponent, then the last exceptional factor has a direct geometric
meaning.  When `A+B+C=D`, the top supported exponent already spends the
entire degree in coordinate zero, so all three transverse coordinates vanish.
Otherwise one of the three transverse affine directions is fixed.

This is the balance-free scalar split needed by the final top-face consumer.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Homogeneous affine terminal: fixed transverse direction or codimension
two.**

Only the degree equalities for the first and top supported exponents are
needed.  A genuinely homogeneous carrier supplies these automatically. -/
theorem rankThree_affineTerminal_homogeneous_fixed_or_codimensionTwo
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C 1 Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S)
    (hdegreeOne :
      ordinaryDegree4 (L.exponent 1) = A + B + C)
    (hdegreeTop :
      ordinaryDegree4 (L.exponent phi.natDegree) = A + B + C) :
    Q = 0 ∨ R = 0 ∨ S = 0 ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary
        (L.exponent phi.natDegree) := by
  have hcertNat :
      HasRankThreePolynomialTerminalCertificate
        (phi := phi) (A : K) (B : K) (C : K) ((1 : ℕ) : K) Q R S := by
    simpa using hcert
  have hstep :=
    rankThree_unit_longitudinal_step_of_certificate
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC (by norm_num) hphiDeg hphi0 hcertNat
  have hphi1 : phi.coeff 1 ≠ 0 := hstep.2
  have h1mem : 1 ∈ phi.support := Polynomial.mem_support_iff.mpr hphi1

  have haff1 := L.affine 1 h1mem
  have hdeg1K := congrArg (fun n : ℕ => (n : K)) hdegreeOne
  have he0 := congrFun haff1 (0 : Fin 4)
  have he1 := congrFun haff1 (1 : Fin 4)
  have he2 := congrFun haff1 (2 : Fin 4)
  have he3 := congrFun haff1 (3 : Fin 4)
  have hsum : (1 : K) + Q + R + S = 0 := by
    simp [ordinaryDegree4, Nat.cast_add] at hdeg1K
    simp [rankThreeLogBaseExponent, rankThreeLogDirection] at he0 he1 he2 he3
    rw [he0, he1, he2, he3] at hdeg1K
    push_cast at hdeg1K
    linear_combination hdeg1K

  have hrel :=
    rankThree_terminal_homogeneous_direction_relation
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC (by norm_num) hphiDeg hphi0 hcertNat hsum

  have hbaseOne :
      (A : K) + (B : K) + (C : K) - 1 ≠ 0 := by
    intro hz
    have heqK : (A : K) + (B : K) + (C : K) = 1 :=
      sub_eq_zero.mp hz
    have heqNat : A + B + C = 1 := by
      exact_mod_cast heqK
    omega

  by_cases hbaseDegree :
      (A : K) + (B : K) + (C : K) - (phi.natDegree : K) = 0
  · have heqK :
        (A : K) + (B : K) + (C : K) = (phi.natDegree : K) :=
      sub_eq_zero.mp hbaseDegree
    have heqNat : A + B + C = phi.natDegree := by
      exact_mod_cast heqK

    have hphi : phi ≠ 0 := by
      intro hz
      rw [hz] at hphi0
      simp at hphi0
    have htopMem : phi.natDegree ∈ phi.support := by
      rw [Polynomial.mem_support_iff]
      change phi.leadingCoeff ≠ 0
      exact (Polynomial.leadingCoeff_ne_zero).2 hphi

    let e := L.exponent phi.natDegree
    have he0Nat : e (0 : Fin 4) = phi.natDegree := by
      dsimp [e]
      simpa using L.exponent_zero_eq htopMem
    have hdegTop' :
        e 0 + e 1 + e 2 + e 3 = A + B + C := by
      simpa [e, ordinaryDegree4] using hdegreeTop
    have htransverse : e 1 + e 2 + e 3 = 0 := by
      rw [heqNat] at hdegTop'
      rw [he0Nat] at hdegTop'
      omega
    have he1zero : e (1 : Fin 4) = 0 := by omega
    have he2zero : e (2 : Fin 4) = 0 := by omega
    exact Or.inr (Or.inr (Or.inr
      ⟨(1 : Fin 4), (2 : Fin 4), by decide, he1zero, he2zero⟩))
  · have hprod :
        (Q * R * S) *
            ((A : K) + (B : K) + (C : K) - 1) *
            ((A : K) + (B : K) + (C : K) -
              (phi.natDegree : K)) = 0 := by
      simpa [mul_assoc] using hrel
    have hleft :
        (Q * R * S) *
            ((A : K) + (B : K) + (C : K) - 1) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hbaseDegree
    have hqrs : Q * R * S = 0 :=
      (mul_eq_zero.mp hleft).resolve_right hbaseOne
    rcases mul_eq_zero.mp hqrs with hqr | hS
    · rcases mul_eq_zero.mp hqr with hQ | hR
      · exact Or.inl hQ
      · exact Or.inr (Or.inl hR)
    · exact Or.inr (Or.inr (Or.inl hS))



/-- **Homogeneous affine terminal: codimension two or an extreme binary
edge.**

Once ordinary degree is preserved, the generic fixed-direction alternative
has only three genuinely rank-three possibilities.  Outside the
codimension-two case, two transverse slopes are zero and the remaining slope
is exactly `-1`.  Thus the terminal edge is binary in one of the three
coordinate orientations. -/
theorem rankThree_affineTerminal_homogeneous_extreme_or_codimensionTwo
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C 1 Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S)
    (hdegreeOne :
      ordinaryDegree4 (L.exponent 1) = A + B + C)
    (hdegreeTop :
      ordinaryDegree4 (L.exponent phi.natDegree) = A + B + C) :
    HC4.Newton.MvExponentOnCodimensionTwoBoundary
        (L.exponent phi.natDegree) ∨
      (Q = 0 ∧ R = 0 ∧ S + 1 = 0) ∨
      (Q = 0 ∧ S = 0 ∧ R + 1 = 0) ∨
      (R = 0 ∧ S = 0 ∧ Q + 1 = 0) := by
  have hcertNat :
      HasRankThreePolynomialTerminalCertificate
        (phi := phi) (A : K) (B : K) (C : K) ((1 : ℕ) : K) Q R S := by
    simpa using hcert
  have hstep :=
    rankThree_unit_longitudinal_step_of_certificate
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC (by norm_num) hphiDeg hphi0 hcertNat
  have hphi1 : phi.coeff 1 ≠ 0 := hstep.2
  have h1mem : 1 ∈ phi.support := Polynomial.mem_support_iff.mpr hphi1
  have haff1 := L.affine 1 h1mem
  have hdeg1K := congrArg (fun n : ℕ => (n : K)) hdegreeOne
  have he01 := congrFun haff1 (0 : Fin 4)
  have he11 := congrFun haff1 (1 : Fin 4)
  have he21 := congrFun haff1 (2 : Fin 4)
  have he31 := congrFun haff1 (3 : Fin 4)
  have hsum : (1 : K) + Q + R + S = 0 := by
    simp [ordinaryDegree4, Nat.cast_add] at hdeg1K
    simp [rankThreeLogBaseExponent, rankThreeLogDirection] at he01 he11 he21 he31
    rw [he01, he11, he21, he31] at hdeg1K
    push_cast at hdeg1K
    linear_combination hdeg1K

  have hbaseOne :
      (A : K) + (B : K) + (C : K) - 1 ≠ 0 := by
    intro hz
    have heqK : (A : K) + (B : K) + (C : K) = 1 :=
      sub_eq_zero.mp hz
    have heqNat : A + B + C = 1 := by
      exact_mod_cast heqK
    omega

  have hphi : phi ≠ 0 := by
    intro hz
    rw [hz] at hphi0
    simp at hphi0
  have htopMem : phi.natDegree ∈ phi.support := by
    rw [Polynomial.mem_support_iff]
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  let e := L.exponent phi.natDegree
  have haffTop := L.affine phi.natDegree htopMem
  have he0Nat : e (0 : Fin 4) = phi.natDegree := by
    dsimp [e]
    simpa using L.exponent_zero_eq htopMem
  have hdegTop' : e 0 + e 1 + e 2 + e 3 = A + B + C := by
    simpa [e, ordinaryDegree4] using hdegreeTop

  have fixed :=
    rankThree_affineTerminal_homogeneous_fixed_or_codimensionTwo
      (K := K) L hA hB hC hphiDeg hphi0 hcert
      hdegreeOne hdegreeTop
  rcases fixed with hQ | hR | hS | hcodim
  · have hrel :=
      rankThree_terminal_homogeneous_Q_zero_relation
        (K := K) (A := A) (B := B) (C := C) (P := 1)
        (Q := Q) (R := R) (S := S) (phi := phi)
        hA hB hC (by norm_num) hphiDeg hphi0 hcertNat hsum hQ
    rcases mul_eq_zero.mp hrel with h0 | htail
    · rcases mul_eq_zero.mp h0 with h0 | hbase
      · rcases mul_eq_zero.mp h0 with h0 | hRp1
        · rcases mul_eq_zero.mp h0 with hA0 | hR0
          · have hAne : (A : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA
            exact (hAne hA0).elim
          · have hSp1 : S + 1 = 0 := by
              linear_combination hsum
            exact Or.inr (Or.inl ⟨hQ, hR0, hSp1⟩)
        · have hS0 : S = 0 := by
            linear_combination hsum + hRp1
          exact Or.inr (Or.inr (Or.inl ⟨hQ, hS0, hRp1⟩))
      · exact (hbaseOne hbase).elim
    · have hBC_K :
          (B : K) + (C : K) = (phi.natDegree : K) :=
        sub_eq_zero.mp htail
      have hBC : B + C = phi.natDegree := by exact_mod_cast hBC_K
      have he1Nat : e (1 : Fin 4) = A := by
        have h := congrFun haffTop (1 : Fin 4)
        dsimp [e] at h ⊢
        simp [rankThreeLogBaseExponent, rankThreeLogDirection, hQ] at h
        exact_mod_cast h
      have he23 : e 2 + e 3 = 0 := by
        omega
      have he2zero : e (2 : Fin 4) = 0 := by omega
      have he3zero : e (3 : Fin 4) = 0 := by omega
      exact Or.inl
        ⟨(2 : Fin 4), (3 : Fin 4), by decide, he2zero, he3zero⟩

  · have hrel :=
      rankThree_terminal_homogeneous_R_zero_relation
        (K := K) (A := A) (B := B) (C := C) (P := 1)
        (Q := Q) (R := R) (S := S) (phi := phi)
        hA hB hC (by norm_num) hphiDeg hphi0 hcertNat hsum hR
    rcases mul_eq_zero.mp hrel with h0 | htail
    · rcases mul_eq_zero.mp h0 with h0 | hbase
      · rcases mul_eq_zero.mp h0 with h0 | hQp1
        · rcases mul_eq_zero.mp h0 with hB0 | hQ0
          · have hBne : (B : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
            exact (hBne hB0).elim
          · have hSp1 : S + 1 = 0 := by
              linear_combination hsum
            exact Or.inr (Or.inl ⟨hQ0, hR, hSp1⟩)
        · have hS0 : S = 0 := by
            linear_combination hsum + hQp1
          exact Or.inr (Or.inr (Or.inr ⟨hR, hS0, hQp1⟩))
      · exact (hbaseOne hbase).elim
    · have hAC_K :
          (A : K) + (C : K) = (phi.natDegree : K) :=
        sub_eq_zero.mp htail
      have hAC : A + C = phi.natDegree := by exact_mod_cast hAC_K
      have he2Nat : e (2 : Fin 4) = B := by
        have h := congrFun haffTop (2 : Fin 4)
        dsimp [e] at h ⊢
        simp [rankThreeLogBaseExponent, rankThreeLogDirection, hR] at h
        exact_mod_cast h
      have he13 : e 1 + e 3 = 0 := by
        omega
      have he1zero : e (1 : Fin 4) = 0 := by omega
      have he3zero : e (3 : Fin 4) = 0 := by omega
      exact Or.inl
        ⟨(1 : Fin 4), (3 : Fin 4), by decide, he1zero, he3zero⟩

  · have hrel :=
      rankThree_terminal_homogeneous_S_zero_relation
        (K := K) (A := A) (B := B) (C := C) (P := 1)
        (Q := Q) (R := R) (S := S) (phi := phi)
        hA hB hC (by norm_num) hphiDeg hphi0 hcertNat hsum hS
    rcases mul_eq_zero.mp hrel with h0 | htail
    · rcases mul_eq_zero.mp h0 with h0 | hbase
      · rcases mul_eq_zero.mp h0 with h0 | hQp1
        · rcases mul_eq_zero.mp h0 with hC0 | hQ0
          · have hCne : (C : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hC
            exact (hCne hC0).elim
          · have hRp1 : R + 1 = 0 := by
              linear_combination hsum
            exact Or.inr (Or.inr (Or.inl ⟨hQ0, hS, hRp1⟩))
        · have hR0 : R = 0 := by
            linear_combination hsum + hQp1
          exact Or.inr (Or.inr (Or.inr ⟨hR0, hS, hQp1⟩))
      · exact (hbaseOne hbase).elim
    · have hAB_K :
          (A : K) + (B : K) = (phi.natDegree : K) :=
        sub_eq_zero.mp htail
      have hAB : A + B = phi.natDegree := by exact_mod_cast hAB_K
      have he3Nat : e (3 : Fin 4) = C := by
        have h := congrFun haffTop (3 : Fin 4)
        dsimp [e] at h ⊢
        simp [rankThreeLogBaseExponent, rankThreeLogDirection, hS] at h
        exact_mod_cast h
      have he12 : e 1 + e 2 = 0 := by
        omega
      have he1zero : e (1 : Fin 4) = 0 := by omega
      have he2zero : e (2 : Fin 4) = 0 := by omega
      exact Or.inl
        ⟨(1 : Fin 4), (2 : Fin 4), by decide, he1zero, he2zero⟩

  · exact Or.inl hcodim

/-- **The honest top exponent of a normalized affine terminal leaves the
starting `.qs` facet.**

The terminal ODE puts the top supported exponent on the coordinate boundary.
Its longitudinal coordinate is exactly `natDegree phi`, hence is positive;
therefore that boundary point cannot lie back on the contact-`0` facet
`.qs`.  It is either rank three on one of the other coordinate facets or is
already codimension two. -/
theorem rankThree_affineTerminal_top_otherFacet_or_codimensionTwo
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C 1 Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S) :
    (∃ next : HC4.Toric.ToricFacet,
        next ≠ .qs ∧
          HC4.Newton.MvRankThreeOnFacet next
            (L.exponent phi.natDegree)) ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary
        (L.exponent phi.natDegree) := by
  have hcertNat :
      HasRankThreePolynomialTerminalCertificate
        (phi := phi) (A : K) (B : K) (C : K) ((1 : ℕ) : K) Q R S := by
    simpa using hcert
  have hboundary :
      HC4.Polynomial.MvExponentOnBoundary
        (L.exponent phi.natDegree) :=
    rankThreeAffineLine_topExponent_on_boundary_of_certificate
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      L hA hB hC (by norm_num) hphiDeg hphi0 hcertNat
  rcases HC4.Newton.mvBoundary_rankThreeFacet_or_codimensionTwo hboundary with
    hthree | hcodim
  · rcases hthree with ⟨next, hnext⟩
    left
    refine ⟨next, ?_, hnext⟩
    intro hqs
    subst next
    have hzero :
        (L.exponent phi.natDegree) (0 : Fin 4) = 0 :=
      (HC4.Newton.mvRankThreeOnFacet_qs hnext).1
    have hphi : phi ≠ 0 := by
      intro hz
      rw [hz] at hphi0
      simp at hphi0
    have htopMem : phi.natDegree ∈ phi.support := by
      rw [Polynomial.mem_support_iff]
      change phi.leadingCoeff ≠ 0
      exact (Polynomial.leadingCoeff_ne_zero).2 hphi
    have hlong :
        (L.exponent phi.natDegree) (0 : Fin 4) = phi.natDegree := by
      simpa using L.exponent_zero_eq htopMem
    rw [hlong] at hzero
    omega
  · exact Or.inr hcodim

end

end HC4.RationalRigidity
