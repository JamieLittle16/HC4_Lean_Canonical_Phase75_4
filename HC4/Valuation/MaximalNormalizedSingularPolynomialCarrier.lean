import HC4.Valuation.MaximalCommonParameterTerminalNormalization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAffineQuadraticCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFace
import Mathlib.Tactic

/-!
# A18.5.16: a universal nonzero Hessian-singular polynomial carrier

A18.5.15 canonically removes the exact minimum parameter order from any
scale-aware family.  Its normalized special fibre is nonzero and still carries
the marked exact gradient collision.

Let the residual Hessian clock be

    Delta' = rawDefect - 4*m.

There are now only two possibilities.

* `Delta' > 0`: the nonzero normalized special fibre itself has zero Hessian
  determinant.
* `Delta' = 0`: the normalized special fibre has determinant one.  Its marked
  collision excludes ordinary degree at most two (A18.5.11), so finite support
  supplies a nonzero maximal component of degree at least three; A18.5.10 makes
  that component Hessian singular.

Thus every scale-aware state has an honest nonzero Hessian-singular polynomial
carrier.  No rank-three label, Smith chart, or terminal cocharacter is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

private def ordinaryWeight : Fin 4 → ℤ := fun _ => 1

/-- Generic determinant-one/collision top-face data, independent of restart
state packaging. -/
structure DeterminantOneCollisionSingularTopFaceData
    (F : MvPolynomial (Fin 4) K)
    (degreeCap : ℕ) : Type (u + 1) where
  degree : ℕ
  witness : Fin 4 →₀ ℕ
  witness_mem : witness ∈ F.support
  witness_degree : HC4.Polynomial.ordinaryDegree4 witness = degree
  maximal : ∀ d ∈ F.support, HC4.Polynomial.ordinaryDegree4 d ≤ degree
  degree_ge_three : 3 ≤ degree
  degree_le_cap : degree ≤ degreeCap
  face : MvPolynomial (Fin 4) K
  face_eq : face = HC4.Polynomial.initialForm ordinaryWeight (degree : ℤ) F
  face_ne_zero : face ≠ 0
  hessian_zero : HC4.Polynomial.hessianDeterminant face = 0

/-- A nonzero determinant-one polynomial with the canonical marked collision
and a nonlinear degree cap has a genuine singular maximal nonlinear face. -/
noncomputable def determinantOneCollision_singularTopFace
    (F : MvPolynomial (Fin 4) K)
    (degreeCap : ℕ)
    (hF : F ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hdegree : NonlinearDegreeBound degreeCap F)
    (hcoll : HasExactGradientCollision F
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))) :
    DeterminantOneCollisionSingularTopFaceData F degreeCap := by
  have hsupport : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  rcases Finset.exists_max_image F.support
      HC4.Polynomial.ordinaryDegree4 hsupport with ⟨d, hd, hmax⟩
  let D := HC4.Polynomial.ordinaryDegree4 d
  let G := HC4.Polynomial.initialForm ordinaryWeight (D : ℤ) F
  have hLE : HC4.Polynomial.IsWeightLE ordinaryWeight (D : ℤ) F := by
    intro q hq
    change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) q ≤ (D : ℤ)
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast hmax q hq
  have hGne : G ≠ 0 := by
    intro hG
    have hcoeff0 : MvPolynomial.coeff d G = 0 := by rw [hG]; simp
    have hw :
        Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d = (D : ℤ) := by
      rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
      rfl
    have hcoeff : MvPolynomial.coeff d G = MvPolynomial.coeff d F := by
      dsimp [G]
      rw [HC4.Polynomial.coeff_initialForm]
      simp [ordinaryWeight, hw]
    rw [hcoeff] at hcoeff0
    exact (MvPolynomial.mem_support_iff.mp hd) hcoeff0
  have hdistinct :
      (fun _ : Fin 4 => (0 : K)) ≠
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    intro h
    have h0 := congrFun h (0 : Fin 4)
    simpa [coordinateAxisPoint] using h0
  have hD3 : 3 ≤ D := by
    by_contra hnot
    have hD2 : D ≤ 2 := by omega
    have hLE2 :
        HC4.Polynomial.IsWeightLE (fun _ : Fin 4 => (1 : ℤ)) 2 F := by
      intro q hq
      have hqD := hLE hq
      change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) q ≤ 2
      exact hqD.trans (by exact_mod_cast hD2)
    exact exactGradientCollision_impossible_of_ordinaryDegree_le_two
      F
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
      hLE2 hdet hdistinct hcoll
  have hDcap : D ≤ degreeCap := hdegree d hd hD3
  have hGzero : HC4.Polynomial.hessianDeterminant G = 0 := by
    dsimp [G]
    exact hessianDeterminant_ordinaryInitial_eq_zero_of_mongeAmpere
      F D hD3 (by simpa [ordinaryWeight] using hLE) hdet
  exact {
    degree := D
    witness := d
    witness_mem := hd
    witness_degree := rfl
    maximal := fun q hq => hmax q hq
    degree_ge_three := hD3
    degree_le_cap := hDcap
    face := G
    face_eq := rfl
    face_ne_zero := hGne
    hessian_zero := hGzero
  }

/-- Exhaustive singular carrier after maximal common-parameter normalization. -/
inductive ScaleAwareMaximalNormalizedSingularFace
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (C : ScaleAwareMaximalCommonParameterFamilyData s) : Type (u + 1)
  | positiveResidual
      (residual_pos : 0 < s.rawDefect - 4 * C.core.order)
      (hessian_zero :
        HC4.Polynomial.hessianDeterminant
          (polynomialFamilySpecialFiber C.core.family) = 0)
  | zeroResidual
      (residual_zero : s.rawDefect - 4 * C.core.order = 0)
      (top : DeterminantOneCollisionSingularTopFaceData
        (polynomialFamilySpecialFiber C.core.family) s.degreeCap)

/-- Complete normalization + singular carrier package. -/
structure ScaleAwareCanonicalSingularPolynomialCarrier
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  normalized : ScaleAwareMaximalCommonParameterFamilyData s
  singular : ScaleAwareMaximalNormalizedSingularFace s normalized

/-- **Universal nonzero singular polynomial carrier.** -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.canonicalSingularPolynomialCarrier
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    ScaleAwareCanonicalSingularPolynomialCarrier s := by
  let C := s.maximalCommonParameterFamily
  let F := polynomialFamilySpecialFiber C.core.family
  let residual := s.rawDefect - 4 * C.core.order
  by_cases hzero : residual = 0
  · have hdet1 : HC4.Polynomial.hessianDeterminant F = 1 := by
      rw [hessianDeterminant_polynomialFamilySpecialFiber]
      unfold HasPolynomialFamilyHessianDefect at C.core.hessianDefect
      rw [C.core.hessianDefect]
      change MvPolynomial.map Polynomial.constantCoeff
          (MvPolynomial.C (Polynomial.X ^ residual)) = 1
      rw [hzero]
      simp
    have htop := determinantOneCollision_singularTopFace
      F s.degreeCap C.core.specialFiber_ne_zero hdet1
      (by simpa [F] using C.nonlinearDegreeBound)
      (by simpa [F] using C.specialFiberCollision)
    exact {
      normalized := C
      singular := .zeroResidual hzero htop
    }
  · have hpos : 0 < residual := Nat.pos_of_ne_zero hzero
    have hsing : HC4.Polynomial.hessianDeterminant F = 0 := by
      dsimp [F, residual]
      exact polynomialFamilySpecialFiber_hessianDeterminant_eq_zero_of_posDefect
        C.core.family (s.rawDefect - 4 * C.core.order)
        C.core.hessianDefect hpos
    exact {
      normalized := C
      singular := .positiveResidual hpos (by simpa [F] using hsing)
    }

/-- The carrier polynomial in either residual-clock branch. -/
noncomputable def ScaleAwareCanonicalSingularPolynomialCarrier.polynomial
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : ScaleAwareCanonicalSingularPolynomialCarrier s) :
    MvPolynomial (Fin 4) K := by
  cases C.singular with
  | positiveResidual _ _ =>
      exact polynomialFamilySpecialFiber C.normalized.core.family
  | zeroResidual _ top =>
      exact top.face

/-- The selected carrier is always nonzero. -/
theorem ScaleAwareCanonicalSingularPolynomialCarrier.polynomial_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : ScaleAwareCanonicalSingularPolynomialCarrier s) :
    C.polynomial ≠ 0 := by
  cases h : C.singular with
  | positiveResidual hpos hzero =>
      simpa [ScaleAwareCanonicalSingularPolynomialCarrier.polynomial, h] using
        C.normalized.core.specialFiber_ne_zero
  | zeroResidual hz top =>
      simpa [ScaleAwareCanonicalSingularPolynomialCarrier.polynomial, h] using
        top.face_ne_zero

/-- The selected carrier always has zero Hessian determinant. -/
theorem ScaleAwareCanonicalSingularPolynomialCarrier.hessian_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : ScaleAwareCanonicalSingularPolynomialCarrier s) :
    HC4.Polynomial.hessianDeterminant C.polynomial = 0 := by
  cases h : C.singular with
  | positiveResidual hpos hzero =>
      simpa [ScaleAwareCanonicalSingularPolynomialCarrier.polynomial, h] using hzero
  | zeroResidual hz top =>
      simpa [ScaleAwareCanonicalSingularPolynomialCarrier.polynomial, h] using
        top.hessian_zero

end

end HC4.Valuation
