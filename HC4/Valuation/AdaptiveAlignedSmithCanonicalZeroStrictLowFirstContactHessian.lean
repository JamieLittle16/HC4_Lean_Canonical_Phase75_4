import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowZeroClockPacket
import HC4.Valuation.AdaptiveAlignedSmithCanonicalLinearFirstContactMixedHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRightRecenteredKernelExit
import Mathlib.Tactic

/-!
# A19.52: zero-clock strict-low first departure has honest Hessian geometry

A19.51 retains a canonical first later longitudinal layer on the literal
right-recentered represented special fibre.  The older A18 first-contact
library already contains the only algebra needed to turn such a supported
later layer into Hessian geometry, provided the source-linear jet vanishes.

That zero-linear-jet hypothesis is also already available: the canonical
blocker endpoint carries a zero source jet, the exact collision transports it
to the right endpoint, and A17.3E records that every linear coefficient of the
honest right-recentered special fibre is zero.

Consequently the final strict-low zero-clock branch needs no terminal
cocharacter merely to expose first-contact curvature.  Its retained first
longitudinal departure itself contains a supported monomial with positive
longitudinal exponent, and A18.4.64 turns that monomial into either a nonzero
longitudinal diagonal Hessian entry or a nonzero mixed Hessian entry.

No new Hessian calculation, progress claim, terminal endpoint, or JC2 input is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- **A19.52 first-contact Hessian adapter.**

The canonical later longitudinal support monomial supplied by A19.51 is a
positive contact in coordinate `0`.  Since the right-recentered blocker fibre
has no linear source terms, the already-green A18.4.64 first-contact lemma
turns it into genuine diagonal-or-mixed Hessian geometry. -/
theorem zeroStrictLow_firstContactHessianGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hzero : source.rawDefect = 0)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
      (longitudinalRightRecenterHom
        (K := K) (polynomialFamilySpecialFiber D.presented.family))
      (0 : Fin 4) := by
  let G := longitudinalRightRecenterHom
    (K := K) (polynomialFamilySpecialFiber D.presented.family)

  have hpacket := D.zeroStrictLow_zeroClockPacket hzero e he hpattern
  have hdeparture :
      HasFirstExactSmithExponentLongitudinalDeparture G e := by
    simpa [G] using hpacket.2.2.2.2

  rcases hdeparture.support_pair with ⟨n, q, hq, _hn, hnq⟩
  let d : Fin 4 →₀ ℕ :=
    (smithTransverseExponent e.b e.c e.d).cons (n + q)

  have hlinear :
      ∀ i : Fin 4,
        MvPolynomial.coeff (Finsupp.single i 1) G = 0 := by
    intro i
    have hi := D.blocker.rightRecenteredSpecialFiber_linearCoeff_zero i
    rw [D.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber] at hi
    simpa [G, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq]
      using hi

  have hd : d ∈ G.support := by
    simpa [d, G] using hnq

  have hdpos : 0 < d (0 : Fin 4) := by
    have hnqpos : 0 < n + q := by omega
    simpa [d] using hnqpos

  exact firstContactHessianGeometry_of_linearCoeff_zero
    G hlinear (0 : Fin 4) d hd hdpos

/-- Lossless A19.51 packet with the first-contact Hessian event appended.
This is the assembly-facing zero-clock strict-low interface: all previous
normal-form and departure data remain available beside the actual curvature
witness. -/
theorem zeroStrictLow_zeroClockFirstContactPacket
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hzero : source.rawDefect = 0)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    D.presented.rawDefect = 0 ∧
      D.blocker.aligned.endpoint.defect = 0 ∧
      AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
        (polynomialFamilySpecialFiber D.presented.family) e ∧
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e ∧
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e ∧
      AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family))
        (0 : Fin 4) := by
  have hpacket := D.zeroStrictLow_zeroClockPacket hzero e he hpattern
  exact ⟨
    hpacket.1,
    hpacket.2.1,
    hpacket.2.2.1,
    hpacket.2.2.2.1,
    hpacket.2.2.2.2,
    D.zeroStrictLow_firstContactHessianGeometry hzero e he hpattern
  ⟩

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
