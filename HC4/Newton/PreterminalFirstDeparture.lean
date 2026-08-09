import HC4.Newton.FiniteRepairTermination
import Mathlib.Tactic

/-!
# Preterminal first-departure algebra

This file formalises the algebraic core of the remaining restart-exhaustion
adapter identified in the v5 audit.

At a constant rank-one Schur line choose kernel coordinates `(U,V)` so that
the leading binary Schur block is

    B0 = [[b,0],[0,0]],   b != 0.

Let `P` be the first later kernel potential appearing strictly before the
determinant-closing order.  The coefficient linear in `Hess P` is

    tr(adj(B0) Hess P) = b * P_VV.

Since that determinant coefficient must vanish and `b != 0`, necessarily

    P_VV = 0.

The binary Hessian determinant then collapses to

    det Hess_(U,V) P = -(P_UV)^2.

Thus there are exactly two algebraic channels:

* `P_UV != 0`: a nonzero negative-square mixed pivot source;
* `P_UV = 0`: no binary mixed curvature, the affine/separated channel.

This is deliberately stated directly in terms of partial derivatives.  It
does not yet guess or duplicate the higher-level data structure expected by
the existing finite repair theorem.  Once this module is green, the final
`MixedDepartureAdapter` only has to package the nonzero mixed derivative
into those existing hypotheses.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Second derivative in one source direction. -/
def directionalSecondDerivative
    (V : σ)
    (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.pderiv V
    (MvPolynomial.pderiv V P)

/-- Mixed second derivative in two source directions. -/
def directionalMixedDerivative
    (U V : σ)
    (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.pderiv U
    (MvPolynomial.pderiv V P)

/-- Binary Hessian determinant in the `(U,V)` directions. -/
def binaryDirectionalHessianDet
    (U V : σ)
    (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  directionalSecondDerivative U P *
      directionalSecondDerivative V P -
    (directionalMixedDerivative U V P)^2

/-- The determinant coefficient linear in a new binary Hessian when the
old rank-one Schur block is `diag(b,0)`. -/
def preterminalSchurLinearSource
    (b : K)
    (V : σ)
    (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.C b *
    directionalSecondDerivative V P

/-- **First preterminal departure.**
If the linear determinant source vanishes against a nonzero leading Schur
entry `b`, then the new potential has zero second derivative in the null
direction. -/
theorem preterminal_secondDerivative_zero
    (b : K)
    (hb : b ≠ 0)
    (V : σ)
    (P : MvPolynomial σ K)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    directionalSecondDerivative V P = 0 := by
  unfold preterminalSchurLinearSource at hsource
  have hCb :
      (MvPolynomial.C b : MvPolynomial σ K) ≠ 0 := by
    intro hC
    apply hb
    have hcoeff :=
      congrArg
        (MvPolynomial.coeff (0 : σ →₀ ℕ))
        hC
    simpa using hcoeff
  exact
    (mul_eq_zero.mp hsource).resolve_left hCb

/-- Once `P_VV=0`, the binary Hessian determinant is exactly the negative
square of the mixed derivative. -/
theorem binaryDirectionalHessianDet_eq_neg_sq_of_second_zero
    (U V : σ)
    (P : MvPolynomial σ K)
    (hVV :
      directionalSecondDerivative V P = 0) :
    binaryDirectionalHessianDet U V P =
      -(directionalMixedDerivative U V P)^2 := by
  unfold binaryDirectionalHessianDet
  rw [hVV]
  ring

/-- The full preterminal determinant identity, directly from the vanishing
linear Schur source. -/
theorem preterminal_binaryDet_eq_neg_sq
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    binaryDirectionalHessianDet U V P =
      -(directionalMixedDerivative U V P)^2 := by
  apply
    binaryDirectionalHessianDet_eq_neg_sq_of_second_zero
  exact
    preterminal_secondDerivative_zero
      b hb V P hsource

/-- In the genuinely mixed branch, the new binary Hessian determinant is
nonzero.  This is the algebraic mixed-pivot source required by restart
termination. -/
theorem preterminal_binaryDet_ne_zero_of_mixed
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (hsource :
      preterminalSchurLinearSource b V P = 0)
    (hmixed :
      directionalMixedDerivative U V P ≠ 0) :
    binaryDirectionalHessianDet U V P ≠ 0 := by
  rw [preterminal_binaryDet_eq_neg_sq
    b hb U V P hsource]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hmixed)

/-- Certificate for the no-mixed-curvature channel. -/
def IsPreterminalAffineSeparatedChannel
    (U V : σ)
    (P : MvPolynomial σ K) : Prop :=
  directionalSecondDerivative V P = 0 ∧
  directionalMixedDerivative U V P = 0

/-- Certificate for the mixed repair channel. -/
def IsPreterminalMixedPivotChannel
    (U V : σ)
    (P : MvPolynomial σ K) : Prop :=
  directionalSecondDerivative V P = 0 ∧
  directionalMixedDerivative U V P ≠ 0 ∧
  binaryDirectionalHessianDet U V P ≠ 0

/-- **Preterminal departure dichotomy.**
Below determinant closure, a departure from a constant rank-one Schur line
is either a genuine mixed pivot with nonzero negative-square determinant
source, or it has no mixed binary curvature. -/
theorem preterminal_departure_dichotomy
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    IsPreterminalMixedPivotChannel U V P ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  have hVV :
      directionalSecondDerivative V P = 0 :=
    preterminal_secondDerivative_zero
      b hb V P hsource
  by_cases hmixed :
      directionalMixedDerivative U V P = 0
  · right
    exact ⟨hVV, hmixed⟩
  · left
    refine ⟨hVV, hmixed, ?_⟩
    exact
      preterminal_binaryDet_ne_zero_of_mixed
        b hb U V P hsource hmixed

/-- The mixed branch exposes the exact negative-square source, not merely
a nonvanishing certificate. -/
theorem preterminal_mixedPivot_exact_source
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (hsource :
      preterminalSchurLinearSource b V P = 0)
    (hmixed :
      directionalMixedDerivative U V P ≠ 0) :
    IsPreterminalMixedPivotChannel U V P ∧
      binaryDirectionalHessianDet U V P =
        -(directionalMixedDerivative U V P)^2 := by
  constructor
  · exact
      ⟨preterminal_secondDerivative_zero
          b hb V P hsource,
       hmixed,
       preterminal_binaryDet_ne_zero_of_mixed
          b hb U V P hsource hmixed⟩
  · exact
      preterminal_binaryDet_eq_neg_sq
        b hb U V P hsource

end

end HC4.Newton
