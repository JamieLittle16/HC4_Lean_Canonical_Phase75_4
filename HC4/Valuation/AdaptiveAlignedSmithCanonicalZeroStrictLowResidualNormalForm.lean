import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBlocker
import HC4.Newton.MixedDegreeFirstWallCompetition
import Mathlib.Tactic

/-!
# A19.49: concrete normal forms for the final strict-low blocker

A19.48 made the *actual* strict-low support exponent into a blocker on the
same aligned endpoint.  The mixed-degree axis-collision library already gives
more than a pattern label for each of the three remaining shapes: it gives the
honest longitudinal coefficient polynomial together with its two-endpoint
factorisation.

This file exposes those three concrete normal forms directly.  There is no
surviving or `w`-linear constructor here.

* pure longitudinal: `A' = X (X-1) C`, with `C != 0`;
* low-negative-first: `A = X (X-1) B`, with `B != 0`;
* low-negative-second: the symmetric factorisation.

These are exactly the source polynomials from which the final first-contact /
two-zero construction must be made.  No JC2 hypothesis or terminal endpoint
is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Concrete residual data attached to one of the three genuinely strict-low
Smith patterns on a normalized terminal special fibre. -/
inductive AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent) : Prop
  | pureLongitudinal
      (A C : Polynomial K)
      (hpattern : IsPureLongitudinalSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalAxisRestriction F)
      (hC : C ≠ 0)
      (hfactor :
        A.derivative =
          (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * C)
      (hdegree : C.natDegree < A.derivative.natDegree)
  | lowNegativeFirst
      (A B : Polynomial K)
      (hpattern : IsLowNegativeFirstSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalCoefficientPolynomial e.b e.c e.d F)
      (hB : B ≠ 0)
      (hfactor :
        A = (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
      (hdegree : B.natDegree + 2 = A.natDegree)
  | lowNegativeSecond
      (A B : Polynomial K)
      (hpattern : IsLowNegativeSecondSmithPattern e)
      (hA : A ≠ 0)
      (hAeq : A = longitudinalCoefficientPolynomial e.b e.c e.d F)
      (hB : B ≠ 0)
      (hfactor :
        A = (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * B)
      (hdegree : B.natDegree + 2 = A.natDegree)

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- **A19.49 final strict-low residual normal form.**

The represented terminal special fibre already has the normalized axis
collision data, so the existing two-endpoint residual theorems apply directly
to whichever of the three strict-low patterns is actually present. -/
theorem zeroStrictLow_residualNormalForm
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
      (polynomialFamilySpecialFiber D.presented.family) e := by
  let F := polynomialFamilySpecialFiber D.presented.family
  have heRaw :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        D.blocker.aligned.endpoint.rawSpecialFiber := by
    simpa [F, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq]
      using he
  have haxis := D.blocker.aligned.rawSpecialFiber_axisData
  rcases haxis with ⟨hcollRaw, hzeroRaw, hvalueRaw⟩
  have hF : F = D.blocker.aligned.endpoint.rawSpecialFiber := by
    simp [F, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq]
  have hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [hF] using hcollRaw
  have hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0 := by
    simpa [hF] using hzeroRaw
  have hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0 := by
    simpa [hF] using hvalueRaw
  rcases hpattern with hpure | hfirst | hsecond
  · rcases projectedSupport_pureLongitudinal_twoEndpointResidualData
        F e (by simpa [F, hF] using heRaw) hpure hcoll hzero hvalue with
      ⟨A, C, hA, hAeq, hC, hfactor, hdegree⟩
    exact .pureLongitudinal A C hpure hA hAeq hC hfactor hdegree
  · rcases projectedSupport_transverseLinear_twoEndpointResidualData
        F e (by simpa [F, hF] using heRaw) 1
        (smithTransverseExponent_eq_single_one_of_lowNegativeFirst e hfirst)
        hcoll hzero with
      ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩
    exact .lowNegativeFirst A B hfirst hA hAeq hB hfactor hdegree
  · rcases projectedSupport_transverseLinear_twoEndpointResidualData
        F e (by simpa [F, hF] using heRaw) 0
        (smithTransverseExponent_eq_single_zero_of_lowNegativeSecond e hsecond)
        hcoll hzero with
      ⟨A, B, hA, hAeq, hB, hfactor, hdegree⟩
    exact .lowNegativeSecond A B hsecond hA hAeq hB hfactor hdegree

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
