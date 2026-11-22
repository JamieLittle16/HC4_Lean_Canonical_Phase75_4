import HC4.Polynomial.RankThreeCubicDetOnePrincipalSourceChartCofactors
import Mathlib.Tactic

/-!
# An exact square identity in the genuine source-origin Schur chart

At the original source point (x=a, y=0), let T be the weight-two
transverse Hessian of F and B0 the full Hessian of F.

If det Hess(F)=1 and det T=0, then any nonzero original
principal cofactor adj(T)[k,k] gives an active two-by-two
principal chart H with

  H.activeDet = adj(T)[k,k]
  H.schurC = 0
  H.determinantCore = 1
  H.schurB^2 = -adj(T)[k,k]

The last Schur coupling is therefore nonzero.
All quantities are evaluations of the original F; no source
coordinate shear or artificial matrix completion is used.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The true det-one source Hessian satisfies the principal
rank-two Schur square identity at its transverse origin. -/
theorem sourceCubic_detOne_originPrincipalSchur_square
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
      ev.mapMatrix (hessian F)
    T.det = 0 →
    ∀ k : Fin 3, T.adjugate k k ≠ 0 →
      let H := principalSourceFourBlock B0 k
      H.activeDet = T.adjugate k k ∧
      H.schurC = 0 ∧
      H.determinantCore = 1 ∧
      H.schurB ^ 2 = -T.adjugate k k ∧
      H.schurB ≠ 0 := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  change T.det = 0 → ∀ k : Fin 3, T.adjugate k k ≠ 0 → _
  intro hTdet k hk
  let H := principalSourceFourBlock B0 k
  obtain ⟨hdetB, hblock⟩ :=
    sourceCubic_detOne_originBordered_transverse_eq_quadratic
      F a hcap hdetOne
  have hBsym : B0.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change ev (pderiv j (pderiv i F)) =
      ev (pderiv i (pderiv j F))
    rw [HC4.Newton.pderiv_comm_backport j i F]
  have hBT : B0.submatrix Sum.inr Sum.inr = T := by
    ext i j
    exact hblock i j
  have hchart := principalSourceFourBlock_activeDet_and_schurC
    B0 hBsym k
  have hactive : H.activeDet = T.adjugate k k := by
    simpa only [H, hBT] using hchart.1
  have hC : H.schurC = 0 := by
    have htmp : H.schurC = T.det := by
      simpa only [H, hBT] using hchart.2
    exact htmp.trans hTdet
  have hdetH : H.determinantCore = 1 := by
    calc
      H.determinantCore = B0.det :=
        principalSourceFourBlock_determinantCore B0 hBsym k
      _ = 1 := hdetB
  have hsq : H.schurB ^ 2 = -T.adjugate k k := by
    rw [← hactive]
    exact detOne_principalSchur_lastZero_couplingSquare
      H hdetH hC
  have hsnz : H.schurB ≠ 0 :=
    detOne_principalSchur_lastZero_coupling_ne_zero
      H hdetH hC (by rw [hactive]; exact hk)
  exact ⟨hactive, hC, hdetH, hsq, hsnz⟩

end
end HC4.Polynomial.RankThreeCubic
