import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyXeLmNormalForm
import Mathlib.Tactic

/-!
# Stage 4B25: the exact RS2-ready frontier

Stage 4B24 gives the complete surviving first spatial key in the exact form

    a * x₀^e * L^m,

outside the already-certified rank-two repair branch.  Stage 4B2 stated the
RS2 algebra under the sufficient hypotheses `e > 0` and `m > 0`, but its
actual coefficient is

    (e + m) (e + m - 1).

Hence the true nondegeneracy condition is only `2 ≤ e + m`.  Since the first
transverse degree always satisfies `m > 0`, failure of that condition is the
single corner

    e = 0,  m = 1.

This file records that sharper algebra and packages the B24 normal form into
an exact three-way frontier:

* rank-two repair;
* the lone pure-transverse-linear corner `(e,m)=(0,1)`;
* an `x₀^e L^m` packet already satisfying the numerical hypothesis needed by
  the Euler/RS2 rigidity calculation.

Thus there is no genuine `e = 0` branch left: only one degree-one corner must
be discharged before the source-to-Schur provenance theorem can invoke RS2
uniformly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {F : Type*} [Field F] [CharZero F]

/-- The RS2 Euler coefficient is nonzero as soon as the *total* active degree
is at least two.  Positivity of the longitudinal exponent is unnecessary. -/
theorem xeLm_rs2EulerCoefficient_ne_zero_of_totalDegree_two_le
    (e m : ℕ)
    (hdeg : 2 ≤ e + m) :
    ((e : F) + (m : F)) * ((e : F) + (m : F) - 1) ≠ 0 := by
  have hsumNat0 : e + m ≠ 0 := by omega
  have hsumCast0 : ((e + m : ℕ) : F) ≠ 0 := by
    exact_mod_cast hsumNat0
  have hsum0 : (e : F) + (m : F) ≠ 0 := by
    simpa using hsumCast0

  have hpredNat0 : e + m - 1 ≠ 0 := by omega
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

/-- Sharp form of the general `x^e L^m` null-RS2 rigidity theorem.

The former assumptions `e > 0` and `m > 0` are replaced by the exact
condition `2 ≤ e + m`. -/
theorem xeLm_rs2EulerPair_eq_zero_of_totalDegree_two_le
    (e m : ℕ)
    (hdeg : 2 ≤ e + m)
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
    xeLm_rs2EulerCoefficient_ne_zero_of_totalDegree_two_le e m hdeg
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

/-- Sharp source-coordinate projective form of the RS2 calculation. -/
theorem xeLm_rs2ProjectiveDerivatives_eq_zero_of_totalDegree_two_le
    (e m : ℕ)
    (hdeg : 2 ≤ e + m)
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
    xeLm_rs2EulerPair_eq_zero_of_totalDegree_two_le
      e m hdeg (x * rhoX) (L * rhoL) hEuler hRS2
  exact
    ⟨(mul_eq_zero.mp huv.1).resolve_left hx,
      (mul_eq_zero.mp huv.2).resolve_left hL⟩

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A B24 normal form together with the exact numerical hypothesis needed by
the sharp RS2 theorem above. -/
structure FirstKeyXeLmRS2ReadyData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) where
  normalForm : C.FirstKeyXeLmNormalFormData D
  totalDegree_two_le : 2 ≤ D.sourceExponent + D.transverseDegree

/-- Since the first transverse degree is positive, the only way the active
total degree can fail to be at least two is `(e,m)=(0,1)`. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.linearCorner_or_totalDegree_two_le
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    (D.sourceExponent = 0 ∧ D.transverseDegree = 1) ∨
      2 ≤ D.sourceExponent + D.transverseDegree := by
  have hmpos := D.transverseDegree_pos
  omega

/-- Promote any nondegenerate B24 normal form to an RS2-ready packet. -/
def FirstKeyXeLmNormalFormData.toRS2ReadyData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmNormalFormData D)
    (hdeg : 2 ≤ D.sourceExponent + D.transverseDegree) :
    C.FirstKeyXeLmRS2ReadyData D :=
  {
    normalForm := N
    totalDegree_two_le := hdeg
  }

/-- **Stage 4B25 sharp first-key frontier.**

Outside certified rank-two repair, the only packet not immediately eligible
for the sharp Euler/RS2 rigidity theorem is the single pure-transverse-linear
corner `sourceExponent = 0`, `transverseDegree = 1`. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.rankTwoRepair_or_linearCorner_or_rs2Ready
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      (D.sourceExponent = 0 ∧ D.transverseDegree = 1) ∨
      Nonempty (C.FirstKeyXeLmRS2ReadyData D) := by
  rcases D.rankTwoRepair_or_xeLmNormalForm F complexity with hrepair | hnormal
  · exact Or.inl hrepair
  · rcases hnormal with ⟨N⟩
    rcases D.linearCorner_or_totalDegree_two_le with hcorner | hdeg
    · exact Or.inr (Or.inl hcorner)
    · exact Or.inr (Or.inr ⟨N.toRS2ReadyData hdeg⟩)

/-- Carrier-specialised use of the sharp algebra.  Once the source-to-Schur
provenance layer supplies the Euler and RS2 identities, an RS2-ready packet
has no remaining scalar projective motion. -/
theorem FirstKeyXeLmRS2ReadyData.eulerPair_eq_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (u v : K)
    (hEuler : u + v = 0)
    (hRS2 :
      (D.transverseDegree : K) * ((D.transverseDegree : K) - 1) * u ^ 2 -
          2 * (D.sourceExponent : K) * (D.transverseDegree : K) * u * v +
          (D.sourceExponent : K) * ((D.sourceExponent : K) - 1) * v ^ 2 = 0) :
    u = 0 ∧ v = 0 := by
  exact xeLm_rs2EulerPair_eq_zero_of_totalDegree_two_le
    D.sourceExponent D.transverseDegree N.totalDegree_two_le u v hEuler hRS2

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
