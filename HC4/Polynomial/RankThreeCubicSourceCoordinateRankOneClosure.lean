import HC4.Polynomial.RankThreeCubicTensorRankOnePlane
import HC4.Polynomial.RankThreeCubicSourceDegrees
import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Actual cubic source: rank-one pole at a coordinate hyperplane is impossible

The source transverse Hessian H(y) is a matrix of homogeneous linear
polynomials. Its coefficients are a completely symmetric
three-index tensor, because the source Hessian arises from actual
third partial derivatives.

If every 2x2 cofactor of H is divisible by X₀, then after evaluating
at (0,1,0), (0,0,1), and (0,1,1) all three corresponding adjugates
vanish. The integrable tensor rank-one-plane theorem then forces
det H to vanish identically, contradicting source regularity.

This is the actual-source *coordinate-plane* rank-one contradiction.
It does not yet handle arbitrary irreducible homogeneous linear p:
for that one must supply a suitable invertible linear coordinate
change and transport the Hessian tensor and cofactor ideal.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- An honest cubic source with nonzero transverse Hessian determinant
cannot have every 2x2 Hessian cofactor divisible by the first
transverse variable. The only geometric hypothesis is the
coordinate-plane identification p=X₀. -/
theorem sourceCubic_coordinatePole_rankOne_impossible
    (F : SB K) (a : K)
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (hcof : ∀ i j : Fin 3,
      (X (0 : Fin 3) : B3 K) ∣
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F)).adjugate i j) :
    False := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let D : Fin 3 → Fin 3 → Fin 3 → K :=
    fun t i j => (pderiv t (H i j)).coeff 0
  have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F i j
  have hderConst (t i j : Fin 3) :
      pderiv t (H i j) = MvPolynomial.C (D t i j) := by
    have hdeg0 : (pderiv t (H i j)).totalDegree = 0 :=
      MvPolynomial.totalDegree_zero_iff_isHomogeneous.mpr
        ((hhom i j).pderiv)
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
  have hlinear (i j : Fin 3) :
      H i j = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * MvPolynomial.C (D t i j) := by
    have heuler := (hhom i j).sum_X_mul_pderiv
    calc
      H i j = (1 : ℕ) • (H i j) := by simp
      _ = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * pderiv t (H i j) := heuler.symm
      _ = ∑ t : Fin 3,
        (MvPolynomial.X t : B3 K) * MvPolynomial.C (D t i j) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hderConst t i j]
  have hEval (v : Fin 3 → K) (i j : Fin 3) :
      MvPolynomial.aeval v (H i j) =
        ∑ t : Fin 3, v t * D t i j := by
    rw [hlinear i j]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C]
  have hswap₂ (t i j : Fin 3) : D t i j = D t j i := by
    have hsym := sourceTransverseHessian_isSymm a L
    have h := congrArg (fun P : B3 K => (pderiv t P).coeff 0)
      (hsym.apply i j)
    exact h.symm
  have hswap₁ (t i j : Fin 3) : D t i j = D i t j := by
    have hleft :
        pderiv t (H i j) =
          referenceSlice a
            (pderiv (.inr t)
              (pderiv (.inr j) (pderiv (.inr i) L))) := by
      change pderiv t (referenceSlice a
        (pderiv (.inr j) (pderiv (.inr i) L))) = _
      exact (referenceSlice_pderiv a t _).symm
    have hright :
        pderiv i (H t j) =
          referenceSlice a
            (pderiv (.inr i)
              (pderiv (.inr j) (pderiv (.inr t) L))) := by
      change pderiv i (referenceSlice a
        (pderiv (.inr j) (pderiv (.inr t) L))) = _
      exact (referenceSlice_pderiv a i _).symm
    have hcomm :
        pderiv (.inr t)
          (pderiv (.inr j) (pderiv (.inr i) L)) =
        pderiv (.inr i)
          (pderiv (.inr j) (pderiv (.inr t) L)) := by
      rw [HC4.Newton.pderiv_comm_backport (.inr j) (.inr i) L]
      rw [HC4.Newton.pderiv_comm_backport (.inr t) (.inr i)
        (pderiv (.inr j) L)]
      rw [HC4.Newton.pderiv_comm_backport (.inr t) (.inr j) L]
    have hder : pderiv t (H i j) = pderiv i (H t j) := by
      rw [hleft, hright, hcomm]
    exact congrArg (fun P : B3 K => P.coeff 0) hder
  have hcofAt (v : Fin 3 → K) (hv : v 0 = 0) :
      (H.map (MvPolynomial.aeval v).toRingHom).adjugate = 0 := by
    let φ : B3 K →ₐ[K] K := MvPolynomial.aeval v
    have hx : φ (MvPolynomial.X (0 : Fin 3)) = 0 := by
      simpa only [MvPolynomial.aeval_X] using hv
    have hz (i j : Fin 3) : φ (H.adjugate i j) = 0 := by
      obtain ⟨u, hu⟩ := hcof i j
      rw [hu, map_mul, hx, zero_mul]
    have hmap : (H.map φ.toRingHom).adjugate =
        H.adjugate.map φ.toRingHom := (φ.toRingHom.map_adjugate H).symm
    rw [hmap]
    ext i j
    exact hz i j
  let vA : Fin 3 → K := ![0, 1, 0]
  let vB : Fin 3 → K := ![0, 0, 1]
  let vAB : Fin 3 → K := ![0, 1, 1]
  have hAmap :
      H.map (MvPolynomial.aeval vA).toRingHom =
        cubicTensorSlice D 1 := by
    ext i j
    change MvPolynomial.aeval vA (H i j) = D 1 i j
    rw [hEval vA i j]
    simp [Fin.sum_univ_three, vA]
  have hBmap :
      H.map (MvPolynomial.aeval vB).toRingHom =
        cubicTensorSlice D 2 := by
    ext i j
    change MvPolynomial.aeval vB (H i j) = D 2 i j
    rw [hEval vB i j]
    simp [Fin.sum_univ_three, vB]
  have hABmap :
      H.map (MvPolynomial.aeval vAB).toRingHom =
        cubicTensorSlice D 1 + cubicTensorSlice D 2 := by
    ext i j
    change MvPolynomial.aeval vAB (H i j) = D 1 i j + D 2 i j
    rw [hEval vAB i j]
    simp [Fin.sum_univ_three, vAB]
  have hAadj : (cubicTensorSlice D 1).adjugate = 0 := by
    rw [← hAmap]
    exact hcofAt vA (by simp [vA])
  have hBadj : (cubicTensorSlice D 2).adjugate = 0 := by
    rw [← hBmap]
    exact hcofAt vB (by simp [vB])
  have hABadj :
      (cubicTensorSlice D 1 + cubicTensorSlice D 2).adjugate = 0 := by
    rw [← hABmap]
    exact hcofAt vAB (by simp [vAB])
  have hEvalZero (v : Fin 3 → K) :
      MvPolynomial.aeval v H.det = 0 := by
    have hmat : (H.map (MvPolynomial.aeval v).toRingHom).det =
        Matrix.det (fun i j : Fin 3 =>
          v 0 * D 0 i j + v 1 * D 1 i j + v 2 * D 2 i j) := by
      congr 1
      ext i j
      change MvPolynomial.aeval v (H i j) = _
      rw [hEval v i j]
      simp only [Fin.sum_univ_three]
    have hz : (H.map (MvPolynomial.aeval v).toRingHom).det = 0 := by
      rw [hmat]
      exact integrable_ternaryTensor_det_zero_of_plane_cofactor_zero
        D hswap₁ hswap₂ hAadj hBadj hABadj (v 0) (v 1) (v 2)
    simpa only [RingHom.map_det] using hz
  have hdetZero : H.det = 0 := by
    apply (sourceCubic_transverseHessian_det_homogeneous_three a F).eq_zero_of_forall_eval_eq_zero
    intro v
    simpa only [MvPolynomial.coe_aeval_eq_eval] using hEvalZero v
  exact hregular hdetZero

end
end HC4.Polynomial.RankThreeCubic
