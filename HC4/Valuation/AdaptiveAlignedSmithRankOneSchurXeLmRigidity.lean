import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyInterface
import Mathlib.Tactic

/-!
# RS2 rigidity for a general `x^e L^m` first Schur key

The first-key interface isolates the genuinely new source-to-Schur provenance
problem.  The algebra after that provenance step should not be reproved inside
the carrier theorem.

This file formalises the general calculation already identified on paper.
For a binary homogeneous key

    c x^e L^m,     e,m >= 1,

a degree-zero projective kernel ratio gives the Euler relation

    u + v = 0,

where `u = x * rho_x` and `v = L * rho_L`.  The null RS2 second-order source
equation is

    m(m-1) u^2 - 2 e m u v + e(e-1) v^2 = 0.

On the Euler line `v = -u`, its coefficient is

    (e+m)(e+m-1),

which is nonzero in characteristic zero because `e,m >= 1`.  Hence `u=v=0`.
If the two active coordinates are nonzero in the ambient field, the two
projective derivatives themselves vanish.

The statements are deliberately independent of the HC4 carrier.  They can be
instantiated in whatever fraction/rational-function field the eventual
projective-motion theorem uses.  Thus Stage 4B only has to manufacture the
Euler and RS2 identities from the first source key; the rigidity algebra is
finished here once and for all.
-/

namespace HC4.Valuation

noncomputable section

variable {F : Type*} [Field F] [CharZero F]

/-- The scalar left after restricting the `x^e L^m` RS2 quadratic to the
Euler line is nonzero for positive exponents. -/
theorem xeLm_rs2EulerCoefficient_ne_zero
    (e m : ℕ)
    (he : 0 < e)
    (hm : 0 < m) :
    ((e : F) + (m : F)) * ((e : F) + (m : F) - 1) ≠ 0 := by
  have hsumNat : 0 < e + m := by omega
  have hsumNat0 : e + m ≠ 0 := Nat.ne_of_gt hsumNat
  have hsumCast0 : ((e + m : ℕ) : F) ≠ 0 := by
    exact_mod_cast hsumNat0
  have hsum0 : (e : F) + (m : F) ≠ 0 := by
    simpa using hsumCast0

  have hpredNat : 0 < e + m - 1 := by omega
  have hpredNat0 : e + m - 1 ≠ 0 := Nat.ne_of_gt hpredNat
  have hpredCast0 : ((e + m - 1 : ℕ) : F) ≠ 0 := by
    exact_mod_cast hpredNat0
  have hnat : e + m = (e + m - 1) + 1 := by omega
  have hcast :
      (e : F) + (m : F) = ((e + m - 1 : ℕ) : F) + 1 := by
    exact_mod_cast hnat
  have hpredEq :
      (e : F) + (m : F) - 1 = ((e + m - 1 : ℕ) : F) := by
    linear_combination hcast
  have hpred0 : (e : F) + (m : F) - 1 ≠ 0 := by
    rw [hpredEq]
    exact hpredCast0

  exact mul_ne_zero hsum0 hpred0

/-- **General `x^e L^m` null-RS2 rigidity.**

If `(u,v)` lies on the degree-zero Euler line and satisfies the null RS2
quadratic attached to positive exponents `e,m`, then both components vanish.
This includes the transverse-linear case `m=1`; no square hypothesis is used.
-/
theorem xeLm_rs2EulerPair_eq_zero
    (e m : ℕ)
    (he : 0 < e)
    (hm : 0 < m)
    (u v : F)
    (hEuler : u + v = 0)
    (hRS2 :
      (m : F) * ((m : F) - 1) * u ^ 2 -
          2 * (e : F) * (m : F) * u * v +
          (e : F) * ((e : F) - 1) * v ^ 2 = 0) :
    u = 0 ∧ v = 0 := by
  have hv : v = -u := by
    linear_combination hEuler

  have hfactor :
      (((e : F) + (m : F)) *
          ((e : F) + (m : F) - 1)) * u ^ 2 = 0 := by
    calc
      (((e : F) + (m : F)) *
            ((e : F) + (m : F) - 1)) * u ^ 2 =
          (m : F) * ((m : F) - 1) * u ^ 2 -
            2 * (e : F) * (m : F) * u * v +
            (e : F) * ((e : F) - 1) * v ^ 2 := by
              rw [hv]
              ring
      _ = 0 := hRS2

  have hcoeff :
      ((e : F) + (m : F)) *
          ((e : F) + (m : F) - 1) ≠ 0 :=
    xeLm_rs2EulerCoefficient_ne_zero e m he hm
  have huSq : u ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hcoeff
  have hu : u = 0 := by
    have hmul : u * u = 0 := by
      simpa [pow_two] using huSq
    rcases mul_eq_zero.mp hmul with hu | hu
    · exact hu
    · exact hu
  have hv0 : v = 0 := by
    rw [hv, hu]
    simp
  exact ⟨hu, hv0⟩

/-- Source-coordinate form of `xeLm_rs2EulerPair_eq_zero`.

Here `u = x * rho_x` and `v = L * rho_L`.  Nonvanishing of the active binary
coordinates cancels the harmless coordinate factors after the RS2/Euler
argument and leaves `rho_x = rho_L = 0` exactly as required by the
projective-constancy step. -/
theorem xeLm_rs2ProjectiveDerivatives_eq_zero
    (e m : ℕ)
    (he : 0 < e)
    (hm : 0 < m)
    (x L rhoX rhoL : F)
    (hx : x ≠ 0)
    (hL : L ≠ 0)
    (hEuler : x * rhoX + L * rhoL = 0)
    (hRS2 :
      (m : F) * ((m : F) - 1) * (x * rhoX) ^ 2 -
          2 * (e : F) * (m : F) * (x * rhoX) * (L * rhoL) +
          (e : F) * ((e : F) - 1) * (L * rhoL) ^ 2 = 0) :
    rhoX = 0 ∧ rhoL = 0 := by
  have huv :=
    xeLm_rs2EulerPair_eq_zero
      e m he hm (x * rhoX) (L * rhoL) hEuler hRS2
  exact
    ⟨(mul_eq_zero.mp huv.1).resolve_left hx,
      (mul_eq_zero.mp huv.2).resolve_left hL⟩

end

end HC4.Valuation
