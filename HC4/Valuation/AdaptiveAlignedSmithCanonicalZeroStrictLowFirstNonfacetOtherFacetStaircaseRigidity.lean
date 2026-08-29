import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralSourceContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# A19.98a: source-neutral staircase profile contradiction

The actual-source contact layer already supplies the integral staircase step and
the weighted support/contact arithmetic.  The stationary staircase profile
rigidity theorem is itself source-neutral: once the represented four-dimensional
source has been converted into its one-variable finite profile, no planar
reduction is needed.

This file packages the terminal algebraic contradiction.  The remaining
geometric bridge only has to construct a profile with nonzero constant term,
the inherited weighted support bound, zero staircase residual, and degree at
least two.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A finite staircase profile satisfying the source-derived stationary
residual cannot still contain a genuinely nonlinear layer. -/
theorem binaryStaircaseProfile_degree_ge_two_impossible
    (D r : ℕ)
    (hr : 2 ≤ r)
    (h : Polynomial K)
    (h0 : h.coeff 0 ≠ 0)
    (hsupport : h.natDegree * r ≤ D)
    (hres : binaryStaircaseProfileResidual D r h = 0)
    (hdegree : 2 ≤ h.natDegree) :
    False := by
  have hle : h.natDegree ≤ 1 :=
    binaryStaircaseProfile_natDegree_le_one
      (K := K) D r hr h h0 hsupport hres
  omega

end

end HC4.Valuation
