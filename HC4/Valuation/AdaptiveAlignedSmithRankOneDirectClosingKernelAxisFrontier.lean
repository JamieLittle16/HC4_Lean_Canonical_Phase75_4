import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingKernelFreshness
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingQuadraticSupport
import Mathlib.Tactic

/-!
# Axis frontier for the fresh direct-closing kernel direction

The green kernel-freshness theorem produces a nonzero vector `v` with

    H₀ v = 0,
    vᵀ Hⱼ v ≠ 0

in the equality branch `j = Delta`.

There is one easy coordinate case which should not be hidden inside a later
source-change argument.  If `v` has no transverse component, then `v` is a
nonzero multiple of the marked longitudinal axis `e₀`.  Hence the original
source coordinates already satisfy

    (H₀)₀₀ = 0,
    (Hⱼ)₀₀ ≠ 0.

Because a diagonal Hessian entry is twice the corresponding square source
coefficient, characteristic zero turns this into an honest fresh `X₀²`
coefficient at the first actual layer.

Otherwise `v` has a nonzero transverse component.  This is exactly the case
in which the marked-axis-preserving transvections can be used to align the
fresh kernel direction without moving the marked point `-e₀`.

Thus direct closing has the sharp source-axis frontier:

* an already-coordinate fresh longitudinal square; or
* a genuinely transverse fresh kernel direction.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Exact relation between a diagonal source-origin Hessian layer and the
corresponding square source coefficient. -/
theorem sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (n : ℕ)
    (i : Fin 4) :
    sourceOriginHessianLayer C.family n i i =
      2 *
        (MvPolynomial.coeff (directClosingQuadraticExponent i i) C.family).coeff n := by
  rw [sourceOriginHessianLayer_apply]
  rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
  rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
  rw [familyParameterLayer_coeff]
  simp [directClosingQuadraticExponent]
  ring

/-- A square source coefficient which vanishes on the old special fibre and
appears at the first actual layer with exact parameter order `j`. -/
def HasFreshDirectClosingSquareAt
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i : Fin 4) : Prop :=
  let d := directClosingQuadraticExponent i i
  (MvPolynomial.coeff d C.family).coeff 0 = 0 ∧
    (MvPolynomial.coeff d C.family).coeff C.firstActualLayerOrder ≠ 0 ∧
    smithFamilyCoefficientOrder C.family d = C.firstActualLayerOrder

/-- If a coordinate axis itself is a fresh kernel direction, its square is an
honest fresh direct-closing source monomial. -/
theorem hasFreshDirectClosingSquareAt_of_axisKernelFresh
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i : Fin 4)
    (hker :
      (sourceOriginHessianLayer C.family 0).mulVec
          (coordinateAxisPoint (K := K) i) = 0)
    (hfresh :
      dotProduct (coordinateAxisPoint (K := K) i)
        ((sourceOriginHessianLayer C.family C.firstActualLayerOrder).mulVec
          (coordinateAxisPoint (K := K) i)) ≠ 0) :
    C.HasFreshDirectClosingSquareAt i := by
  let d := directClosingQuadraticExponent i i
  have hdiag0 : sourceOriginHessianLayer C.family 0 i i = 0 := by
    have hi := congrFun hker i
    simpa [Matrix.mulVec, dotProduct, coordinateAxisPoint] using hi
  have hdiagj :
      sourceOriginHessianLayer C.family C.firstActualLayerOrder i i ≠ 0 := by
    simpa [Matrix.mulVec, dotProduct, coordinateAxisPoint] using hfresh
  have hcoeff0 : (MvPolynomial.coeff d C.family).coeff 0 = 0 := by
    have h := C.sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff 0 i
    rw [show directClosingQuadraticExponent i i = d by rfl] at h
    rw [hdiag0] at h
    have htwo : (2 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h.symm).resolve_left htwo
  have hcoeffj :
      (MvPolynomial.coeff d C.family).coeff C.firstActualLayerOrder ≠ 0 := by
    intro hz
    apply hdiagj
    rw [C.sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff]
    rw [show directClosingQuadraticExponent i i = d by rfl, hz]
    simp
  have hd : d ∈ C.family.support := by
    exact C.mem_family_support_of_coeff_at_ne_zero hcoeffj
  have hnotSpecial : d ∉ (polynomialFamilySpecialFiber C.family).support := by
    intro hspecial
    exact (C.firstActualLayer_overlap_coeff_zero_ne hspecial) hcoeff0
  have hparam :
      smithFamilyCoefficientParameterOrder C.family d hd =
        C.firstActualLayerOrder := by
    exact
      (C.firstActualLayer_sourceCoefficient_fresh_iff_parameterOrder_eq_first
        hd hcoeffj).1 hnotSpecial
  refine ⟨hcoeff0, hcoeffj, ?_⟩
  rw [smithFamilyCoefficientOrder_eq C.family hd]
  exact hparam

/-- **Kernel-axis frontier at direct closing.**

At `j = Delta`, either the original marked longitudinal coordinate already
carries a fresh square coefficient, or the fresh kernel vector has a genuine
transverse component.  The second alternative is precisely the input needed
for an axis-preserving transverse alignment. -/
theorem directClosing_freshLongitudinalSquare_or_transverseKernelFresh
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.HasFreshDirectClosingSquareAt (0 : Fin 4) ∨
      ∃ (v : Fin 4 → K) (ell : Fin 4),
        v ≠ 0 ∧
        ell ≠ (0 : Fin 4) ∧
        v ell ≠ 0 ∧
        (sourceOriginHessianLayer C.family 0).mulVec v = 0 ∧
        dotProduct v
          ((sourceOriginHessianLayer C.family C.firstActualLayerOrder).mulVec v) ≠ 0 := by
  rcases C.directClosing_exists_kernelFreshDirection heq with
    ⟨v, hvne, hker, hfresh⟩
  by_cases htrans : ∃ ell : Fin 4, ell ≠ (0 : Fin 4) ∧ v ell ≠ 0
  · rcases htrans with ⟨ell, hell0, hvell⟩
    exact Or.inr ⟨v, ell, hvne, hell0, hvell, hker, hfresh⟩
  · have h1 : v (1 : Fin 4) = 0 := by
      by_contra hne
      exact htrans ⟨1, by decide, hne⟩
    have h2 : v (2 : Fin 4) = 0 := by
      by_contra hne
      exact htrans ⟨2, by decide, hne⟩
    have h3 : v (3 : Fin 4) = 0 := by
      by_contra hne
      exact htrans ⟨3, by decide, hne⟩
    have hv0 : v (0 : Fin 4) ≠ 0 := by
      intro h0
      apply hvne
      funext r
      fin_cases r <;> simp_all

    let e0 : Fin 4 → K := coordinateAxisPoint (K := K) (0 : Fin 4)
    have haxisKer :
        (sourceOriginHessianLayer C.family 0).mulVec e0 = 0 := by
      funext r
      have hr := congrFun hker r
      have hentry : sourceOriginHessianLayer C.family 0 r 0 = 0 := by
        change
          (∑ k : Fin 4, sourceOriginHessianLayer C.family 0 r k * v k) = 0 at hr
        simp [Fin.sum_univ_four, h1, h2, h3] at hr
        exact hr.resolve_right hv0
      simp [e0, Matrix.mulVec, dotProduct, coordinateAxisPoint,
        Fin.sum_univ_four, hentry]

    have haxisFresh :
        dotProduct e0
          ((sourceOriginHessianLayer C.family C.firstActualLayerOrder).mulVec e0) ≠ 0 := by
      have h00 :
          sourceOriginHessianLayer C.family C.firstActualLayerOrder 0 0 ≠ 0 := by
        intro hzero
        apply hfresh
        change
          (∑ r : Fin 4,
            v r *
              (∑ k : Fin 4,
                sourceOriginHessianLayer C.family C.firstActualLayerOrder r k * v k)) = 0
        simp [Fin.sum_univ_four, h1, h2, h3, hzero]
      simpa [e0, Matrix.mulVec, dotProduct, coordinateAxisPoint,
        Fin.sum_univ_four] using h00

    exact Or.inl
      (C.hasFreshDirectClosingSquareAt_of_axisKernelFresh
        (0 : Fin 4) haxisKer haxisFresh)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
