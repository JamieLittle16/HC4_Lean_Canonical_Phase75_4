import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurRawBinaryProjectiveLine
import HC4.Valuation.SeparatedRightWallScaleDescent
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import Mathlib.Tactic

/-!
# Stage 4B33: realise the spatial transverse filtration as an honest Rees parameter

The remaining early-Schur theorem is an associated-graded statement in the
three Smith-transverse source variables.  There is no need to formalise a
second weighted Schur calculus: the existing `unitTransverseInflateFamily`
already performs the honest diagonal substitution

    x₀ |-> x₀,
    xᵢ |-> τ xᵢ    (i = 1,2,3).

Consequently a source monomial of total transverse degree `m` acquires the
ordinary parameter factor `τ^m`.  This file identifies the exact parameter
layer of that Rees family with the existing weighted initial form

    initialForm pureLongitudinalTransverseWeight (-m) F.

Thus the first spatial key used throughout B8--B32 is literally an ordinary
first Rees coefficient potential.  The already-green parameter-layer Hessian
bridge may therefore be reused verbatim in the final Schur calculation.

This is only an identification theorem: it introduces no new geometric
hypothesis, no repair claim, and no relation with the original closing-family
parameter clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The honest one-parameter Rees family obtained by multiplying each of the
three transverse source variables by the new parameter once. -/
noncomputable def transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  unitTransverseInflateFamily (K := K) (MvPolynomial.map Polynomial.C F)

/-- Coefficient formula for the transverse Rees family.  The parameter
exponent is exactly the total exponent in source variables `1,2,3`. -/
theorem coeff_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (transverseSourceReesFamily F) =
      Polynomial.X ^ pureLongitudinalTransverseDegree d *
        Polynomial.C (MvPolynomial.coeff d F) := by
  rw [transverseSourceReesFamily, coeff_unitTransverseInflateFamily]
  rw [MvPolynomial.coeff_map]
  rfl

/-- Scalar coefficient of one Rees source coefficient. -/
theorem coeff_coeff_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (n : ℕ) :
    (MvPolynomial.coeff d (transverseSourceReesFamily F)).coeff n =
      if pureLongitudinalTransverseDegree d = n then
        MvPolynomial.coeff d F
      else 0 := by
  rw [coeff_transverseSourceReesFamily]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hdn : pureLongitudinalTransverseDegree d = n
  · subst n
    simp
  · have hlt_or_gt :
        n < pureLongitudinalTransverseDegree d ∨
          pureLongitudinalTransverseDegree d < n := by
      omega
    rcases hlt_or_gt with hlt | hgt
    · simp [Nat.not_le.mpr hlt, hdn]
    · have hle : pureLongitudinalTransverseDegree d ≤ n := Nat.le_of_lt hgt
      have hsubpos : 0 < n - pureLongitudinalTransverseDegree d := by omega
      simp [hle, hdn, Polynomial.coeff_C, Nat.ne_of_gt hsubpos]

/-- **Spatial/Rees identification.**

The exact `n`th coefficient potential of the honest transverse Rees family is
precisely the old negative-transverse-weight initial form of the source
polynomial. -/
theorem familyParameterLayer_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ) :
    familyParameterLayer (transverseSourceReesFamily F) n =
      initialForm pureLongitudinalTransverseWeight (-(n : ℤ)) F := by
  ext d
  rw [familyParameterLayer_coeff]
  rw [coeff_coeff_transverseSourceReesFamily]
  rw [coeff_initialForm]
  rw [weight_pureLongitudinalTransverseWeight]
  by_cases hdeg : pureLongitudinalTransverseDegree d = n
  · rw [if_pos hdeg]
    have hw :
        -(pureLongitudinalTransverseDegree d : ℤ) = -(n : ℤ) := by
      exact congrArg (fun q : ℕ => -(q : ℤ)) hdeg
    simp [hw]
  · rw [if_neg hdeg]
    have hw :
        -(pureLongitudinalTransverseDegree d : ℤ) ≠ -(n : ℤ) := by
      intro h
      apply hdeg
      exact_mod_cast (neg_inj.mp h)
    simp [hw]

/-- The Rees parameter Hessian layer is therefore exactly the Hessian of the
corresponding spatial initial form.  This is the key adapter that lets the
final proof reuse `FirstSchurLayerLinearization` rather than rebuilding a
weighted Schur-complement theory. -/
theorem familyParameterHessianLayer_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ) :
    familyParameterHessianLayer (transverseSourceReesFamily F) n =
      HC4.Polynomial.hessian
        (initialForm pureLongitudinalTransverseWeight (-(n : ℤ)) F) := by
  rw [familyParameterHessianLayer_eq_hessian]
  rw [familyParameterLayer_transverseSourceReesFamily]

/-- Evaluation of the Rees parameter at `1` recovers the original source
polynomial.  Hence any nonzero spatial Schur/projective expression remains a
nonzero polynomial expression in the Rees parameter before evaluation. -/
theorem map_evalOne_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K))
        (transverseSourceReesFamily F) = F := by
  ext d
  rw [MvPolynomial.coeff_map]
  rw [coeff_transverseSourceReesFamily]
  simp

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The B1 first spatial key is literally the corresponding ordinary Rees
coefficient layer.  We retain the original witness `hpos` so no clock or
choice is changed. -/
theorem HasFirstTransverseSourceKey.rees_firstKeyLayer
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    ∃ hpos :
        (positiveTransverseSourceSupport
          (polynomialFamilySpecialFiber C.family)).Nonempty,
      let F₀ := polynomialFamilySpecialFiber C.family
      let m := firstPositiveTransverseSourceDegree F₀ hpos
      familyParameterLayer (transverseSourceReesFamily F₀) m =
        initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) F₀ := by
  rcases hkey with ⟨hpos, _hm, _hQne, _hQhom, _hhess⟩
  refine ⟨hpos, ?_⟩
  dsimp only
  exact familyParameterLayer_transverseSourceReesFamily _ _

/-- Hessian form of the same statement, ready for the first-Schur departure
calculation. -/
theorem HasFirstTransverseSourceKey.rees_firstKeyHessianLayer
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    ∃ hpos :
        (positiveTransverseSourceSupport
          (polynomialFamilySpecialFiber C.family)).Nonempty,
      let F₀ := polynomialFamilySpecialFiber C.family
      let m := firstPositiveTransverseSourceDegree F₀ hpos
      familyParameterHessianLayer (transverseSourceReesFamily F₀) m =
        HC4.Polynomial.hessian
          (initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) F₀) := by
  rcases hkey with ⟨hpos, _hm, _hQne, _hQhom, _hhess⟩
  refine ⟨hpos, ?_⟩
  dsimp only
  exact familyParameterHessianLayer_transverseSourceReesFamily _ _

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
