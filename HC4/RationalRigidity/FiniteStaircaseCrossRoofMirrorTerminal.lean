import HC4.Polynomial.FiniteStaircaseCrossRoofMirrorArithmetic
import HC4.RationalRigidity.FiniteStaircaseCrossRoofTerminal
import Mathlib.Tactic

/-!
# Mirrored cross-roof rank-three terminal rigidity

`FiniteStaircaseCrossRoofTerminal` indexes an exposed cross-roof line from the
lower `y = 0` endpoint and forces the high-side residual `v` to be one.  The
same honest line can be indexed in the opposite direction, from the high
`z = 0` endpoint by its `z` coordinate.  The coefficient-polynomial degree is
then the low-side residual `q`.

The exceptional highest-direction factors have the same geometric meanings:
fixed `x`, fixed `w`, or ordinary homogeneity.  Fixed `x` together with fixed
`w` is already arithmetically impossible.  In the homogeneous fixed-`w` case
the terminal relation forces

    (jHi + 1) + v = q,

which contradicts `q = jLo + 1 - kLo`, `kLo > 0`, and
`kHi = jLo + 1`.

Thus the mirror orientation forces `q = 1`.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Cross-roof mirror terminal forces unit low-side residual.** -/
theorem finiteStaircase_crossRoof_lowResidual_eq_one
    {n ell V kLo jLo kHi jHi q v : ℕ}
    {phi : Polynomial K}
    (hn : 2 ≤ n) (hnell : n ≤ ell)
    (hV : 0 < V)
    (hkLo : 0 < kLo)
    (hk : kLo < kHi)
    (hLo :
      ((n : ℤ) - 1) * (jLo : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kLo : ℤ)))
    (hHi :
      ((n : ℤ) - 1) * (jHi : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (kHi : ℤ)))
    (hq : q = jLo + 1 - kLo) (hqpos : 0 < q)
    (hv : v = kHi - jHi - 1) (hvpos : 0 < v)
    (hphiDeg : phi.natDegree = q)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert :
      HasRankThreePolynomialTerminalCertificate
        (phi := phi)
        (jHi + 1 : K) (v : K) ((V * (kHi - 1) : ℕ) : K) 1
        (((kLo : K) - ((jHi + 1 : ℕ) : K)) / (q : K))
        (-((v : K) / (q : K)))
        ((V : K) * ((jLo : K) - ((kHi : K) - 1)) / (q : K))) :
    q = 1 := by
  let Q : K :=
    (((kLo : K) - ((jHi + 1 : ℕ) : K)) / (q : K))
  let R : K := -((v : K) / (q : K))
  let S : K :=
    (V : K) * ((jLo : K) - ((kHi : K) - 1)) / (q : K)

  have hqK0 : (q : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hvK0 : (v : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hvpos)
  have hVK : (V : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hV)
  have hkHi1pos : 0 < kHi - 1 := by omega
  have hAK : ((jHi + 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (show jHi + 1 ≠ 0 by omega)
  have hCK : ((V * (kHi - 1) : ℕ) : K) ≠ 0 := by
    exact_mod_cast
      (Nat.mul_ne_zero (Nat.ne_of_gt hV) (Nat.ne_of_gt hkHi1pos))

  have hkLo_le : kLo ≤ jLo + 1 := by omega
  have hjHi_le : jHi + 1 ≤ kHi := by omega
  have hqK : (q : K) = (jLo : K) + 1 - (kLo : K) := by
    rw [hq, Nat.cast_sub hkLo_le]
    push_cast
    ring
  have hvK : (v : K) = (kHi : K) - (jHi : K) - 1 := by
    have hsub : kHi - (jHi + 1) = kHi - jHi - 1 := by omega
    rw [hv, ← hsub, Nat.cast_sub hjHi_le]
    push_cast
    ring

  have hRne : R ≠ 0 := by
    dsimp [R]
    exact neg_ne_zero.mpr (div_ne_zero hvK0 hqK0)

  have hQzero_fixedX : Q = 0 → jHi + 1 = kLo := by
    intro hQ
    dsimp [Q] at hQ
    have hnum : (kLo : K) - ((jHi + 1 : ℕ) : K) = 0 := by
      have h := (div_eq_zero_iff).mp hQ
      exact h.resolve_right hqK0
    have hcast : (kLo : K) = ((jHi + 1 : ℕ) : K) := sub_eq_zero.mp hnum
    exact_mod_cast hcast.symm

  have hSzero_fixedW : S = 0 → kHi = jLo + 1 := by
    intro hS
    dsimp [S] at hS
    have hfrac :
        (((jLo : K) - ((kHi : K) - 1)) / (q : K)) = 0 := by
      exact (mul_eq_zero.mp hS).resolve_left hVK
    have hnum : (jLo : K) - ((kHi : K) - 1) = 0 := by
      have h := (div_eq_zero_iff).mp hfrac
      exact h.resolve_right hqK0
    have hcast : (kHi : K) = (jLo : K) + 1 := by linear_combination hnum
    exact_mod_cast hcast

  have hsum_zero_fixedW : 1 + Q + R + S = 0 → kHi = jLo + 1 := by
    intro hsum
    have hscaled := congrArg (fun z : K => z * (q : K)) hsum
    dsimp [Q, R, S] at hscaled
    field_simp [hqK0] at hscaled
    rw [hqK, hvK] at hscaled
    have hfactor :
        ((V : K) + 1) * ((jLo : K) - (kHi : K) + 1) = 0 := by
      linear_combination hscaled
    have hVp1 : (V : K) + 1 ≠ 0 := by
      have hnat : V + 1 ≠ 0 := by omega
      have hcast : ((V + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hnat
      simpa [Nat.cast_add] using hcast
    have hlast : (jLo : K) - (kHi : K) + 1 = 0 :=
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
      have hformula : Q + 1 = (v : K) / (q : K) := by
        dsimp [Q]
        field_simp [hqK0]
        rw [hqK, hvK]
        have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
        rw [hwK]
        ring
      rw [hformula]
      exact div_ne_zero hvK0 hqK0
    have hsum : 1 + Q + R + S = 0 := by
      dsimp [Q, R, S]
      field_simp [hqK0]
      rw [hqK, hvK]
      have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
      rw [hwK]
      ring
    have hS : S = 0 := by
      dsimp [S]
      have hwK : (kHi : K) = (jLo : K) + 1 := by exact_mod_cast hw
      rw [hwK]
      ring
    have hdegPos : 0 < phi.natDegree := by omega
    have hrel := rankThree_terminal_homogeneous_S_zero_relation
      (K := K)
      (A := jHi + 1) (B := v) (C := V * (kHi - 1)) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      (by omega) hvpos (Nat.mul_pos hV hkHi1pos) (by omega)
      hdegPos hphi0 (by simpa [Q, R, S] using hcert) hsum hS
    have hbaseMinus :
        ((jHi + 1 : ℕ) : K) + (v : K) +
            ((V * (kHi - 1) : ℕ) : K) - 1 ≠ 0 := by
      intro hz
      have heq :
          ((jHi + 1 : ℕ) : K) + (v : K) +
              ((V * (kHi - 1) : ℕ) : K) = 1 := by
        linear_combination hz
      have heqNat : jHi + 1 + v + V * (kHi - 1) = 1 := by
        exact_mod_cast heq
      omega
    have hpref :
        ((V * (kHi - 1) : ℕ) : K) * Q * (Q + 1) *
          (((jHi + 1 : ℕ) : K) + (v : K) +
            ((V * (kHi - 1) : ℕ) : K) - 1) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero hCK hQne) hQp1) hbaseMinus
    have hlast :
        ((jHi + 1 : ℕ) : K) + (v : K) - (phi.natDegree : K) = 0 := by
      exact (mul_eq_zero.mp hrel).resolve_left hpref
    have hdegK : ((jHi + 1 : ℕ) : K) + (v : K) = (q : K) := by
      rw [hphiDeg] at hlast
      linear_combination hlast
    have hdegNat : jHi + 1 + v = q := by exact_mod_cast hdegK
    exact no_crossRoof_fixed_w_mirror_terminal_degree_relation
      hkLo hq hv hw hdegNat

  have hdegPos : 0 < phi.natDegree := by omega
  by_contra hqone
  have hqgt : 1 < q := by omega
  have hDne : (phi.natDegree : K) - 1 ≠ 0 := by
    rw [hphiDeg]
    intro hz
    have hqKone : (q : K) = 1 := sub_eq_zero.mp hz
    have hqNat : q = 1 := by exact_mod_cast hqKone
    omega
  have hrel := rankThree_terminal_highest_direction_relation
    (K := K)
    (A := jHi + 1) (B := v) (C := V * (kHi - 1)) (P := 1)
    (Q := Q) (R := R) (S := S) (phi := phi)
    (by omega) hvpos (Nat.mul_pos hV hkHi1pos) (by omega)
    hdegPos hphi0 (by simpa [Q, R, S] using hcert)
  have hdir : Q * R * S * (1 + Q + R + S) = 0 :=
    (mul_eq_zero.mp hrel).resolve_left hDne
  rcases mul_eq_zero.mp hdir with hQRS | hsum
  · rcases mul_eq_zero.mp hQRS with hQR | hS
    · rcases mul_eq_zero.mp hQR with hQ | hR
      · have hx := hQzero_fixedX hQ
        rcases rankThree_terminal_Q_zero_refines
            (K := K)
            (A := jHi + 1) (B := v) (C := V * (kHi - 1)) (P := 1)
            (Q := Q) (R := R) (S := S) (phi := phi)
            (by omega) hvpos (Nat.mul_pos hV hkHi1pos) (by omega)
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