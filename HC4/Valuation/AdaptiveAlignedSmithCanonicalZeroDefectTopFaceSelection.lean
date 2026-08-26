import HC4.Valuation.AdaptiveAlignedSmithCanonicalAffineQuadraticCollision
import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# A18.5.12: select the genuine zero-defect singular top face

A18.5.10 proves that any attained maximal ordinary component of degree at
least three in a determinant-one special fibre is Hessian singular.  A18.5.11
proves that an exact distinct collision rules out ordinary degree at most two.

This file performs the finite-support selection for an actual zero-defect
scale-aware state.  It retains an explicit supported exponent attaining the
maximum, so the resulting top face is not merely a formal component:

* the witness exponent is supported by the actual special fibre;
* its degree is the selected maximum `D`;
* every source exponent has ordinary degree at most `D`;
* `3 <= D <= degreeCap`;
* the degree-`D` initial form is nonzero; and
* that initial form has zero Hessian determinant.

The marked exact collision remains attached to the source special fibre as
provenance.  We do not claim that arbitrary initial-form extraction preserves
that collision.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

private def ordinaryWeight : Fin 4 → ℤ := fun _ => 1

/-- Lossless singular top-face data extracted from a raw-defect-zero state. -/
structure AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  source_zero : s.rawDefect = 0
  degree : ℕ
  witness : Fin 4 →₀ ℕ
  witness_mem :
    witness ∈ (polynomialFamilySpecialFiber s.family).support
  witness_degree :
    HC4.Polynomial.ordinaryDegree4 witness = degree
  maximal :
    ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
      HC4.Polynomial.ordinaryDegree4 d ≤ degree
  degree_ge_three : 3 ≤ degree
  degree_le_cap : degree ≤ s.degreeCap
  face : MvPolynomial (Fin 4) K
  face_eq :
    face = HC4.Polynomial.initialForm ordinaryWeight (degree : ℤ)
      (polynomialFamilySpecialFiber s.family)
  face_ne_zero : face ≠ 0
  hessian_zero : HC4.Polynomial.hessianDeterminant face = 0
  source_collision :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber s.family)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))

/-- **Every zero-defect scale-aware state has a genuine nonzero singular
nonlinear top face.** -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.zeroDefect_singularTopFace
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s := by
  let F := polynomialFamilySpecialFiber s.family
  have hdet1 : HC4.Polynomial.hessianDeterminant F = 1 := by
    simpa [F] using s.zeroDefect_specialFiber_hessianDeterminant_eq_one hzero
  have hFne : F ≠ 0 := by
    intro hF
    have hdet0 : HC4.Polynomial.hessianDeterminant F = 0 := by
      rw [hF]
      unfold HC4.Polynomial.hessianDeterminant HC4.Polynomial.hessian
      change (0 : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K)).det = 0
      exact Matrix.det_zero
    rw [hdet1] at hdet0
    exact one_ne_zero hdet0
  have hsupport : F.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hFne
  have hchoice : Nonempty {
      d : Fin 4 →₀ ℕ //
        d ∈ F.support ∧
          ∀ d' ∈ F.support,
            HC4.Polynomial.ordinaryDegree4 d' ≤
              HC4.Polynomial.ordinaryDegree4 d } := by
    rcases Finset.exists_max_image F.support
        HC4.Polynomial.ordinaryDegree4 hsupport with
      ⟨d, hd, hmax⟩
    exact ⟨⟨d, hd, hmax⟩⟩
  let dData := Classical.choice hchoice
  let d : Fin 4 →₀ ℕ := dData.1
  have hd : d ∈ F.support := by
    exact dData.2.1
  have hmax :
      ∀ d' ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d' ≤
          HC4.Polynomial.ordinaryDegree4 d := by
    exact dData.2.2
  let D := HC4.Polynomial.ordinaryDegree4 d
  let G := HC4.Polynomial.initialForm ordinaryWeight (D : ℤ) F
  have hLE : HC4.Polynomial.IsWeightLE ordinaryWeight (D : ℤ) F := by
    intro q hq
    change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) q ≤ (D : ℤ)
    rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast hmax q hq
  have hGne : G ≠ 0 := by
    intro hG
    have hcoeff0 : MvPolynomial.coeff d G = 0 := by
      rw [hG]
      simp
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
  have hcoll :
      HasExactGradientCollision F
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
    have h :=
      polynomialFamilyZeroCollision_specialFiber
        s.family s.movingSection s.exactCollision
    rw [s.sectionSpecial] at h
    simpa [F] using h
  have hdistinct :
      (fun _ : Fin 4 => (0 : K)) ≠
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    intro h
    have h0 := congrFun h (0 : Fin 4)
    simpa [coordinateAxisPoint] using h0
  have hD3 : 3 ≤ D := by
    by_contra hnot
    have hD2 : D ≤ 2 := by omega
    have hLE2 : HC4.Polynomial.IsWeightLE ordinaryWeight 2 F := by
      intro q hq
      exact (hLE hq).trans (by exact_mod_cast hD2)
    exact exactGradientCollision_impossible_of_ordinaryDegree_le_two
      F
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
      hLE2 hdet1 hdistinct hcoll
  have hdegreeSpecial : NonlinearDegreeBound s.degreeCap F := by
    dsimp [F]
    exact nonlinearDegreeBound_polynomialFamilySpecialFiber
      s.degreeCap s.family s.nonlinearDegreeBound
  have hDcap : D ≤ s.degreeCap := by
    exact hdegreeSpecial d hd hD3
  have hGzero : HC4.Polynomial.hessianDeterminant G = 0 := by
    dsimp [G]
    exact s.zeroDefect_ordinaryInitial_hessianDeterminant_eq_zero
      hzero D hD3 (by simpa [F] using hLE)
  exact {
    source_zero := hzero
    degree := D
    witness := d
    witness_mem := by simpa [F] using hd
    witness_degree := rfl
    maximal := by
      intro q hq
      exact hmax q (by simpa [F] using hq)
    degree_ge_three := hD3
    degree_le_cap := hDcap
    face := G
    face_eq := rfl
    face_ne_zero := hGne
    hessian_zero := hGzero
    source_collision := by simpa [F] using hcoll
  }

end

end HC4.Valuation
