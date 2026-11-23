import HC4.Polynomial.RankThreeCubicPoleQuotientPointEvaluation
import HC4.Polynomial.RankThreeCubicDetOneSourceMixedAffineDegrees
import Mathlib.Tactic

/-!
# Exact three-scale original-source transverse Hessian decomposition

For a source polynomial F whose transverse degree is at most 3,
write L3 and L2 for its actual transverse cubic and quadratic
layers and Rlow = F-L3-L2.

The transverse Hessian of Rlow vanishes identically.
After specializing x=a, the transverse Hessian of L2 is a
CONSTANT matrix T and that of L3 is a homogeneous linear
matrix A(y).

Consequently, for any z in the ground field vector space,
the full original transverse Hessian at y=0,z,-z is exactly

     T,  T+A(z),  T-A(z).

This is a source-level, coefficient-by-coefficient identity;
no adapted frame or pole assumptions are involved.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual weight-two source transverse Hessian is a
constant polynomial after longitudinal specialization. -/
theorem sourceCubic_secondLayer_transverseSlice_eq_C
    (F : SB K) (a : K) (i j : Fin 3) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let Q : B3 K :=
      referenceSlice a (hessian L2 (.inr i) (.inr j))
    Q = MvPolynomial.C (Q.coeff 0) := by
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Q : B3 K :=
    referenceSlice a (hessian L2 (.inr i) (.inr j))
  have hL2 : L2.IsWeightedHomogeneous transverseCubicWeight 2 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 2 F
  have hH :
      (hessian L2 (.inr i) (.inr j)).IsWeightedHomogeneous
        transverseCubicWeight 0 := by
    have h := pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL2 (.inr i)) (.inr j)
    simpa [hessian_apply, transverseCubicWeight] using h
  have hh : Q.IsHomogeneous 0 :=
    referenceSlice_isHomogeneous_of_transverseWeight a _ 0 hH
  have hd : Q.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2 hh
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd

/-- Oddness of the genuine cubic transverse Hessian under y↦-y,
an immediate consequence of its transverse homogeneity one. -/
theorem sourceCubic_cubicTransverseHessian_eval_neg
    (F : SB K) (a : K) (z : Fin 3 → K)
    (i j : Fin 3) :
    MvPolynomial.aeval (fun m => -z m)
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F) i j) =
      -MvPolynomial.aeval z
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F) i j) := by
  let P : B3 K :=
    sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F) i j
  have hh : P.IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F i j
  have hEuler : P =
      ∑ t : Fin 3, (MvPolynomial.X t : B3 K) * pderiv t P := by
    have he := hh.sum_X_mul_pderiv
    simpa only [one_nsmul] using he.symm
  have hconst (t : Fin 3) :
      pderiv t P = MvPolynomial.C ((pderiv t P).coeff 0) := by
    have hd : (pderiv t P).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2
        hh.pderiv
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hleft :
      MvPolynomial.aeval (fun m => -z m) P =
        ∑ t : Fin 3, (-z t) * (pderiv t P).coeff 0 := by
    conv_lhs => rw [hEuler]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X,
      hconst, MvPolynomial.aeval_C]
  have hright :
      MvPolynomial.aeval z P =
        ∑ t : Fin 3, z t * (pderiv t P).coeff 0 := by
    conv_lhs => rw [hEuler]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X,
      hconst, MvPolynomial.aeval_C]
  change MvPolynomial.aeval (fun m => -z m) P =
    -MvPolynomial.aeval z P
  rw [hleft, hright, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The full original source transverse Hessian at three symmetric
transverse evaluations is T, T+A(z), T-A(z), exactly. -/
theorem sourceCubic_fullTransverseHessian_threeScale
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (z : Fin 3 → K) :
    let L3 : SB K := initialForm transverseCubicWeight 3 F
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let ev (y : Fin 3 → K) : SB K →+* K :=
      ((MvPolynomial.aeval y).toRingHom).comp
        (referenceSlice a).toRingHom
    let Bzero := (ev (fun _ => (0 : K))).mapMatrix (hessian F)
    let Bplus := (ev z).mapMatrix (hessian F)
    let Bminus := (ev (fun j => -z j)).mapMatrix (hessian F)
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (ev (fun _ => (0 : K)))
        (hessian L2 (.inr i) (.inr j))
    let A : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (ev z) (hessian L3 (.inr i) (.inr j))
    Bzero.submatrix Sum.inr Sum.inr = T ∧
      Bplus.submatrix Sum.inr Sum.inr = T + A ∧
      Bminus.submatrix Sum.inr Sum.inr = T - A := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let ev (y : Fin 3 → K) : SB K →+* K :=
    ((MvPolynomial.aeval y).toRingHom).comp
      (referenceSlice a).toRingHom
  let Bzero := (ev (fun _ => (0 : K))).mapMatrix (hessian F)
  let Bplus := (ev z).mapMatrix (hessian F)
  let Bminus := (ev (fun j => -z j)).mapMatrix (hessian F)
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (ev (fun _ => (0 : K)))
      (hessian L2 (.inr i) (.inr j))
  let A : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (ev z) (hessian L3 (.inr i) (.inr j))
  have hF : F = L3 + L2 + Rlow := by
    dsimp [Rlow, L3, L2]
    ring
  have hR (i j : Fin 3) : hessian Rlow (.inr i) (.inr j) = 0 := by
    change hessian
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F) (.inr i) (.inr j) = 0
    rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
    exact sourceCubic_belowTwo_transverseHessian_zero F hcap i j
  have hsplit (i j : Fin 3) :
      hessian F (.inr i) (.inr j) =
        hessian L3 (.inr i) (.inr j) +
          hessian L2 (.inr i) (.inr j) := by
    calc
      hessian F (.inr i) (.inr j) =
          hessian (L3 + L2 + Rlow) (.inr i) (.inr j) := by
            rw [hF]
      _ = hessian L3 (.inr i) (.inr j) +
            hessian L2 (.inr i) (.inr j) +
              hessian Rlow (.inr i) (.inr j) := by
            simp only [hessian_apply, map_add]
      _ = _ := by rw [hR i j, add_zero]
  have hQeval (i j : Fin 3) (y : Fin 3 → K) :
      (ev y) (hessian L2 (.inr i) (.inr j)) =
        T i j := by
    have hc := sourceCubic_secondLayer_transverseSlice_eq_C F a i j
    change MvPolynomial.aeval y
      (referenceSlice a (hessian L2 (.inr i) (.inr j))) =
      MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
        (referenceSlice a (hessian L2 (.inr i) (.inr j)))
    rw [hc]
    simp
  have hAorigin (i j : Fin 3) :
      (ev (fun _ => (0 : K)))
        (hessian L3 (.inr i) (.inr j)) = 0 := by
    have hh := sourceCubic_transverseHessian_homogeneous_one a F i j
    change MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (sourceTransverseHessian a L3 i j) = 0
    exact homogeneous_positive_origin_zero _ 0 hh
  have hAneg (i j : Fin 3) :
      (ev (fun m => -z m)) (hessian L3 (.inr i) (.inr j)) =
        -A i j := by
    exact sourceCubic_cubicTransverseHessian_eval_neg F a z i j
  constructor
  · ext i j
    change (ev (fun _ => (0 : K)))
      (hessian F (.inr i) (.inr j)) = T i j
    rw [hsplit i j, map_add, hAorigin i j,
      hQeval i j (fun _ => (0 : K)), zero_add]
  constructor
  · ext i j
    change (ev z) (hessian F (.inr i) (.inr j)) =
      T i j + A i j
    rw [hsplit i j, map_add, hQeval i j z, add_comm]
  · ext i j
    change (ev (fun m => -z m))
      (hessian F (.inr i) (.inr j)) =
        T i j - A i j
    rw [hsplit i j, map_add, hQeval i j (fun m => -z m),
      hAneg i j]
    ring

end
end HC4.Polynomial.RankThreeCubic
