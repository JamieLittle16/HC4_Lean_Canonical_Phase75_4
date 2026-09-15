import HC4.Polynomial.FiniteStaircaseCrossRoofArithmetic
import HC4.RationalRigidity.RankThreeHighestDirectionRelation
import HC4.RationalRigidity.RankThreeSingleDirectionRefinement
import HC4.RationalRigidity.RankThreeHomogeneousOtherFixedRelations
import Mathlib.Tactic

/-!
# Cross-roof rank-three terminal rigidity

Consider two distinct points on the live left finite staircase.  The lower
pair-degree point is on the `y=0` roof and has positive residual

    q = jLo + 1 - kLo,

while the higher pair-degree point is on the `z=0` roof and has positive
residual

    v = kHi - jHi - 1.

Index an honest exposed affine line from the `y=0` endpoint by its `y`
coordinate.  Its primitive direction is then

    (1,
      (jHi+1-kLo)/v,
      -q/v,
      V*(kHi-1-jLo)/v).

The mature rank-three terminal stack says that degree bigger than one forces a
fixed transverse direction or ordinary homogeneity.  The staircase arithmetic
eliminates every such exceptional direction.  The remaining homogeneous
`w`-fixed case is killed by the already-verified next-coefficient relation
`A+B=D`.  Hence the opposite-roof residual `v` is exactly one.

This theorem is state-free: the future A19 adapter only has to construct the
terminal certificate of the exposed cross-roof face.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Cross-roof terminal forces unit high-side residual.** -/
theorem finiteStaircase_crossRoof_highResidual_eq_one
    {n ell V kLo jLo kHi jHi q v : ℕ}
    {phi : Polynomial K}
    (hn : 2 ≤ n) (hnell : n ≤ ell)
    (hV : 0 < V)
    (hkLo : 0 < kLo) (hjLo : 0 < jLo)
    (hk : kLo < kHi)
    (hLo :
      ((n : ℤ) - 1) * (jLo : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kLo : ℤ)))
    (hHi :
      ((n : ℤ) - 1) * (jHi : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kHi : ℤ)))
    (hq : q = jLo + 1 - kLo) (hqpos : 0 < q)
    (hv : v = kHi - jHi - 1) (hvpos : 0 < v)
    (hphiDeg : phi.natDegree = v)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert :
      HasRankThreePolynomialTerminalCertificate
        (phi := phi)
        (kLo : K) (q : K) ((V * jLo : ℕ) : K) 1
        ((((jHi + 1 : ℕ) : K) - (kLo : K)) / (v : K))
        (-((q : K) / (v : K)))
        ((V : K) * ((((kHi : K) - 1) - (jLo : K)) / (v : K)))) :
    v = 1 := by
  let Q : K :=
    ((((jHi + 1 : ℕ) : K) - (kLo : K)) / (v : K))
  let R : K := -((q : K) / (v : K))
  let S : K :=
    (V : K) * ((((kHi : K) - 1) - (jLo : K)) / (v : K))

  have hvK : (v : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hvpos)
  have hqK0 : (q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hVK : (V : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hV)
  have hkLoK : (kLo : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkLo)
  have hjLoK : (jLo : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hjLo)
  have hCK : ((V * jLo : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hV) (Nat.ne_of_gt hjLo))

  have hkLo_le : kLo ≤ jLo + 1 := by omega
  have hjHi_le : jHi + 1 ≤ kHi := by omega
  have hqK : (q : K) = (jLo : K) + 1 - (kLo : K) := by
    rw [hq, Nat.cast_sub hkLo_le]
    push_cast
    ring
  have hvK_eq : (v : K) = (kHi : K) - (jHi : K) - 1 := by
    have hsub : kHi - (jHi + 1) = kHi - jHi - 1 := by omega
    rw [hv, ← hsub, Nat.cast_sub hjHi_le]
    push_cast
    ring

  have hRne : R ≠ 0 := by
    dsimp [R]
    exact neg_ne_zero.mpr (div_ne_zero hqK0 hvK)

  have hQzero_fixedX : Q = 0 → jHi + 1 = kLo := by
    intro hQ
    dsimp [Q] at hQ
    have hnum : (((jHi + 1 : ℕ) : K) - (kLo : K)) = 0 := by
      have := (div_eq_zero_iff).mp hQ
      exact this.resolve_right hvK
    have hcast : (((jHi + 1 : ℕ) : K)) = (kLo : K) := sub_eq_zero.mp hnum
    exact_mod_cast hcast

  have hSzero_fixedW : S = 0 → kHi = jLo + 1 := by
    intro hS
    dsimp [S] at hS
    have hfrac : ((((kHi : K) - 1) - (jLo : K)) / (v : K)) = 0 := by
      exact (mul_eq_zero.mp hS).resolve_left hVK
    have hnum : ((kHi : K) - 1) - (jLo : K) = 0 := by
      have := (div_eq_zero_iff).mp hfrac
      exact this.resolve_right hvK
    have hcast : (kHi : K) = (jLo : K) + 1 := by linear_combination hnum
    exact_mod_cast hcast

  have hsum_zero_fixedW : 1 + Q + R + S = 0 → kHi = jLo + 1 := by
    intro hsum
    have hscaled := congrArg (fun z : K => z * (v : K)) hsum
    dsimp [Q, R, S] at hscaled
    field_simp [hvK] at hscaled
    rw [hqK, hvK_eq] at hscaled
    push_cast at hscaled
    have hfactor :
        ((V : K) + 1) * ((kHi : K) - (jLo : K) - 1) = 0 := by
      linear_combination hscaled
    have hVp1 : (V : K) + 1 ≠ 0 := by
      have hnat : V + 1 ≠ 0 := by omega
      have hcast : ((V + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hnat
      simpa [Nat.cast_add] using hcast
    have hlast : (kHi : K) - (jLo : K) - 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hVp1
    have hcast : (kHi : K) = (jLo : K) + 1 := by linear_combination hlast
    exact_mod_cast hcast

  have himpossible_fixedW : kHi = jLo + 1 → False := by
    intro hw
    have hQne : Q ≠ 0 := by
      intro hQ
      have hx := hQzero_fixedX hQ
      exact no_crossRoof_fixed_x_and_fixed_w
        hn hnell hk hLo hHi hx hw
    have hQp1 : Q + 1 ≠ 0 := by
      have hformula : Q + 1 = (q : K) / (v : K) := by
        dsimp [Q]
        field_simp [hvK]
        rw [hqK, hvK_eq]
        have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
        rw [hwK]
        push_cast
        ring
      rw [hformula]
      exact div_ne_zero hqK0 hvK
    have hsum : 1 + Q + R + S = 0 := by
      dsimp [Q, R, S]
      field_simp [hvK]
      rw [hqK, hvK_eq]
      have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
      rw [hwK]
      push_cast
      ring
    have hS : S = 0 := by
      dsimp [S]
      have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
      rw [hwK]
      ring
    have hdegPos : 0 < phi.natDegree := by omega
    have hrel := rankThree_terminal_homogeneous_S_zero_relation
      (K := K)
      (A := kLo) (B := q) (C := V * jLo) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hkLo hqpos (Nat.mul_pos hV hjLo) (by omega)
      hdegPos hphi0 (by simpa [Q, R, S] using hcert) hsum hS
    have hbaseMinus :
        (kLo : K) + (q : K) + ((V * jLo : ℕ) : K) - 1 ≠ 0 := by
      intro hz
      have heq :
          (kLo : K) + (q : K) + ((V * jLo : ℕ) : K) = 1 := by
        linear_combination hz
      have heqNat : kLo + q + V * jLo = 1 := by exact_mod_cast heq
      omega
    have hpref :
        ((V * jLo : ℕ) : K) * Q * (Q + 1) *
          ((kLo : K) + (q : K) + ((V * jLo : ℕ) : K) - 1) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero hCK hQne) hQp1) hbaseMinus
    have hlast :
        (kLo : K) + (q : K) - (phi.natDegree : K) = 0 := by
      exact (mul_eq_zero.mp hrel).resolve_left hpref
    have hdegK : (kLo : K) + (q : K) = (v : K) := by
      rw [hphiDeg] at hlast
      linear_combination hlast
    have hdegNat : kLo + q = v := by exact_mod_cast hdegK
    exact no_crossRoof_fixed_w_terminal_degree_relation
      hq hqpos hv hw hdegNat

  have hdegPos : 0 < phi.natDegree := by omega
  by_contra hvone
  have hvgt : 1 < v := by omega
  have hDne : (phi.natDegree : K) - 1 ≠ 0 := by
    rw [hphiDeg]
    intro hz
    have hvKone : (v : K) = 1 := sub_eq_zero.mp hz
    have hvNat : v = 1 := by exact_mod_cast hvKone
    omega
  have hrel := rankThree_terminal_highest_direction_relation
    (K := K)
    (A := kLo) (B := q) (C := V * jLo) (P := 1)
    (Q := Q) (R := R) (S := S) (phi := phi)
    hkLo hqpos (Nat.mul_pos hV hjLo) (by omega)
    hdegPos hphi0 (by simpa [Q, R, S] using hcert)
  have hdir : Q * R * S * (1 + Q + R + S) = 0 :=
    (mul_eq_zero.mp hrel).resolve_left hDne
  rcases mul_eq_zero.mp hdir with hQRS | hsum
  · rcases mul_eq_zero.mp hQRS with hQR | hS
    · rcases mul_eq_zero.mp hQR with hQ | hR
      · have hx := hQzero_fixedX hQ
        rcases rankThree_terminal_Q_zero_refines
            (K := K)
            (A := kLo) (B := q) (C := V * jLo) (P := 1)
            (Q := Q) (R := R) (S := S) (phi := phi)
            hkLo hqpos (Nat.mul_pos hV hjLo) (by omega)
            hdegPos hphi0 (by simpa [Q, R, S] using hcert) hQ with
          hR0 | hS0 | hhom
        · exact hRne hR0
        · exact no_crossRoof_fixed_x_and_fixed_w
            hn hnell hk hLo hHi hx (hSzero_fixedW hS0)
        · have hfull : 1 + Q + R + S = 0 := by rw [hQ]; simpa using hhom
          exact no_crossRoof_fixed_x_and_fixed_w
            hn hnell hk hLo hHi hx (hsum_zero_fixedW hfull)
      · exact hRne hR
    · exact himpossible_fixedW (hSzero_fixedW hS)
  · exact himpossible_fixedW (hsum_zero_fixedW hsum)

end

end HC4.RationalRigidity