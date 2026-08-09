import HC4.RationalRigidity.CanonicalReducedFraction
import Mathlib.Tactic

/-!
# Regular logarithmic derivative on the canonical reduced source chart

The manuscript's autonomous ODE uses

    rho = E(phi) / phi,
    eta = E(rho),

where `E = X d/dX`.  At a zero of `phi`, the raw presentation

    eta = logarithmicEtaNumerator(phi) / phi^2

can display a removable pole.  For pole removal on the autonomous target we
instead need a presentation which is manifestly regular at every finite point
where the *reduced* source rational function `rho` is finite.

Let

    rho = N / D

be Mathlib's canonical reduced presentation from Phase 84.  The equality with
`E(phi) / phi` gives the exact polynomial identity

    N * phi = E(phi) * D.

Euler differentiating and eliminating this cross relation yields

    ((E N) D - N (E D)) * phi^2
      = (E(E phi) * phi - (E phi)^2) * D^2.

Thus the reduced numerator

    (E N) D - N (E D)

represents `eta` over `D^2`.  In particular it has a perfectly regular scalar
value at every finite source-chart point `D(x) != 0`, even if the raw
`phi^2` denominator cancelled there.

This is the algebraic form of the regularity input in the manuscript sentence
"a finite pole of R would have a preimage at which t rho' is regular".
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Euler differentiation satisfies the product rule. -/
theorem eulerDerivative_mul
    (P Q : Polynomial K) :
    HC4.Polynomial.eulerDerivative (P * Q) =
      HC4.Polynomial.eulerDerivative P * Q +
        P * HC4.Polynomial.eulerDerivative Q := by
  unfold HC4.Polynomial.eulerDerivative
  rw [Polynomial.derivative_mul]
  ring

/-- Cleared numerator of `E(N/D)` over the denominator `D^2`. -/
def reducedLogarithmicEtaNumerator
    (N D : Polynomial K) : Polynomial K :=
  HC4.Polynomial.eulerDerivative N * D -
    N * HC4.Polynomial.eulerDerivative D

/-- Scalar value of the reduced logarithmic derivative at a finite chart
point.  It is intended to be used under the hypothesis `D.eval x != 0`. -/
def reducedLogarithmicEtaValue
    (N D : Polynomial K) (x : K) : K :=
  (reducedLogarithmicEtaNumerator N D).eval x / (D.eval x) ^ 2

/-- The canonical reduced source pair satisfies the exact cross identity with
the raw logarithmic presentation `E(phi) / phi`. -/
theorem logarithmicSource_cross_identity
    (phi : Polynomial K) (hphi : phi ≠ 0) :
    logarithmicSourceNumerator phi * phi =
      HC4.Polynomial.eulerDerivative phi *
        logarithmicSourceDenominator phi := by
  have h :
      (logarithmicSourceRatFunc phi).num * phi =
        HC4.Polynomial.eulerDerivative phi *
          (logarithmicSourceRatFunc phi).denom := by
    apply
      (RatFunc.num_mul_eq_mul_denom_iff
        (x := logarithmicSourceRatFunc phi) hphi).2
    simp [logarithmicSourceRatFunc, polynomialPairRatFunc]
  simpa [logarithmicSourceNumerator, logarithmicSourceDenominator,
    canonicalReducedNumerator, canonicalReducedDenominator] using h

/-- Generic algebraic cancellation lemma behind reduced logarithmic
regularity.  If `N/ D = E(phi)/phi` in cleared form, then the two cleared
presentations of `eta = E(rho)` agree. -/
theorem reducedLogarithmicEta_cross_of_source_cross
    {phi N D : Polynomial K}
    (hcross :
      N * phi = HC4.Polynomial.eulerDerivative phi * D) :
    reducedLogarithmicEtaNumerator N D * phi ^ 2 =
      HC4.Polynomial.logarithmicEtaNumerator phi * D ^ 2 := by
  have hder := congrArg HC4.Polynomial.eulerDerivative hcross
  rw [eulerDerivative_mul, eulerDerivative_mul] at hder
  unfold reducedLogarithmicEtaNumerator
  unfold HC4.Polynomial.logarithmicEtaNumerator
  linear_combination
    D * phi * hder -
      (D * HC4.Polynomial.eulerDerivative phi +
        HC4.Polynomial.eulerDerivative D * phi) * hcross

/-- Reduced numerator for the logarithmic `eta` attached to `phi`. -/
def logarithmicSourceEtaNumerator
    (phi : Polynomial K) : Polynomial K :=
  reducedLogarithmicEtaNumerator
    (logarithmicSourceNumerator phi)
    (logarithmicSourceDenominator phi)

/-- Exact polynomial identity relating the regular reduced presentation of
`eta` to the raw `phi^2` presentation. -/
theorem logarithmicSource_eta_cross_identity
    (phi : Polynomial K) (hphi : phi ≠ 0) :
    logarithmicSourceEtaNumerator phi * phi ^ 2 =
      HC4.Polynomial.logarithmicEtaNumerator phi *
        (logarithmicSourceDenominator phi) ^ 2 := by
  unfold logarithmicSourceEtaNumerator
  exact reducedLogarithmicEta_cross_of_source_cross
    (logarithmicSource_cross_identity phi hphi)

/-- The regular scalar value of `rho` on the canonical finite source chart. -/
def logarithmicSourceValue
    (phi : Polynomial K) (x : K) : K :=
  (logarithmicSourceNumerator phi).eval x /
    (logarithmicSourceDenominator phi).eval x

/-- The regular scalar value of `eta = E(rho)` on the canonical finite source
chart. -/
def logarithmicSourceEtaValue
    (phi : Polynomial K) (x : K) : K :=
  reducedLogarithmicEtaValue
    (logarithmicSourceNumerator phi)
    (logarithmicSourceDenominator phi) x

/-- A finite source-chart point gives a nonzero denominator for the reduced
`eta` presentation as well. -/
theorem logarithmicSourceEta_denominator_ne_zero
    {phi : Polynomial K} {x : K}
    (hD : (logarithmicSourceDenominator phi).eval x ≠ 0) :
    ((logarithmicSourceDenominator phi).eval x) ^ 2 ≠ 0 :=
  pow_ne_zero 2 hD

/-- Evaluating the polynomial cross identity gives the corresponding scalar
cross identity at every point, including cancelled roots of the raw
presentation. -/
theorem logarithmicSource_eta_eval_cross_identity
    (phi : Polynomial K) (hphi : phi ≠ 0) (x : K) :
    (logarithmicSourceEtaNumerator phi).eval x * (phi.eval x) ^ 2 =
      (HC4.Polynomial.logarithmicEtaNumerator phi).eval x *
        ((logarithmicSourceDenominator phi).eval x) ^ 2 := by
  have h := logarithmicSource_eta_cross_identity phi hphi
  simpa using congrArg (Polynomial.eval x) h

/-- Away from an actual raw zero of `phi`, the regular reduced value of `rho`
is the familiar value `E(phi)/phi`. -/
theorem logarithmicSourceValue_eq_raw
    (phi : Polynomial K) (hphi : phi ≠ 0) {x : K}
    (hphiEval : phi.eval x ≠ 0)
    (hDEval : (logarithmicSourceDenominator phi).eval x ≠ 0) :
    logarithmicSourceValue phi x =
      (HC4.Polynomial.eulerDerivative phi).eval x / phi.eval x := by
  have h := logarithmicSource_cross_identity phi hphi
  have heval := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_mul] at heval
  unfold logarithmicSourceValue
  apply (div_eq_div_iff hDEval hphiEval).2
  exact heval

/-- Away from an actual raw zero of `phi`, the regular reduced value of `eta`
is exactly the raw `logarithmicEtaNumerator(phi)/phi^2` value. -/
theorem logarithmicSourceEtaValue_eq_raw
    (phi : Polynomial K) (hphi : phi ≠ 0) {x : K}
    (hphiEval : phi.eval x ≠ 0)
    (hDEval : (logarithmicSourceDenominator phi).eval x ≠ 0) :
    logarithmicSourceEtaValue phi x =
      (HC4.Polynomial.logarithmicEtaNumerator phi).eval x /
        (phi.eval x) ^ 2 := by
  have heval := logarithmicSource_eta_eval_cross_identity phi hphi x
  unfold logarithmicSourceEtaValue reducedLogarithmicEtaValue
  apply
    (div_eq_div_iff
      (pow_ne_zero 2 hDEval)
      (pow_ne_zero 2 hphiEval)).2
  exact heval

end

end HC4.RationalRigidity
