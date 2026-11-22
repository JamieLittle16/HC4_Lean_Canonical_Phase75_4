import HC4.Polynomial.RankThreeCubicDetOnePrincipalSourceKernelPairing
import HC4.Polynomial.RankThreeCubicDetOneSourceOriginSubTwoCoupling
import Mathlib.Tactic

/-!
# Exact rank-two source Schur equation in the actual below-two mixed jet

For F of transverse weight <=3 with det Hess(F)=1, suppose the
original weight-two transverse origin Hessian T has a nonzero
ground-field kernel vector w and a nonzero principal cofactor at k.

Let g be the CONSTANT scalar coefficient of the actual strictly
below-weight-two mixed longitudinal/transverse directional Hessian.

Then, in the original source principal chart H at (x=a,y=0),
  H.activeDet*g = H.schurB*w[k]
  H.activeDet*g² = -w[k]².

Both identities hold at the original source and do not require
an artificial Hessian completion or algebraic closure. The second
follows by combining the first with H.schurB²=-H.activeDet.

These equations are necessary constraints on a surviving branch,
not a contradiction by themselves.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The determinant-one source rank-two principal chart determines
the low-layer mixed longitudinal scalar up to an exact square. -/
theorem sourceCubic_detOne_originSchur_lowJetSquare
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w0 : Fin 3 → K) (hw0 : w0 ≠ 0)
    (hTker : ∀ i : Fin 3,
      (∑ j : Fin 3,
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (referenceSlice a
            (hessian (initialForm transverseCubicWeight 2 F)
              (.inr i) (.inr j)))) * w0 j) = 0)
    (k : Fin 3) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) - L2
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
      ev.mapMatrix (hessian F)
    let H0 := principalSourceFourBlock B0 k
    let flow : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)
    T.adjugate k k ≠ 0 →
    H0.activeDet * flow.coeff 0 = H0.schurB * w0 k ∧
      H0.activeDet * (flow.coeff 0) ^ 2 = -(w0 k ^ 2) := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) - L2
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  let H0 := principalSourceFourBlock B0 k
  let flow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)
  change T.adjugate k k ≠ 0 → _
  intro hk
  obtain ⟨hdetB, hblock⟩ :=
    sourceCubic_detOne_originBordered_transverse_eq_quadratic
      F a hcap hdetOne
  have hBsym : B0.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change ev (pderiv i (pderiv j F)) =
      ev (pderiv j (pderiv i F))
    rw [HC4.Newton.pderiv_comm_backport i j F]
  have hBrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B0 (.inr i) (.inr j) * w0 j) = 0 := by
    intro i
    calc
      (∑ j : Fin 3, B0 (.inr i) (.inr j) * w0 j) =
          ∑ j : Fin 3, T i j * w0 j := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun x : K => x * w0 j) (hblock i j)
      _ = 0 := hTker i
  have hpair :
      H0.activeDet *
        (∑ j : Fin 3, B0 (.inl ()) (.inr j) * w0 j) =
          H0.schurB * w0 k :=
    principalSourceFourBlock_schurB_kernelPairing
      B0 hBsym w0 hBrows k
  have hc : flow = MvPolynomial.C (flow.coeff 0) :=
    sourceCubic_subTwo_mixedDirectional_eq_C F hcap a w0
  have heq := sourceCubic_originLongitudinalPairing_eq_subTwo F a w0
  have hpairSource :
      (∑ j : Fin 3, B0 (.inl ()) (.inr j) * w0 j) =
        flow.coeff 0 := by
    calc
      _ = MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) flow := heq
      _ = flow.coeff 0 := by rw [hc]; simp
  have hprimary :
      H0.activeDet * flow.coeff 0 = H0.schurB * w0 k := by
    simpa only [hpairSource] using hpair
  have hTvec : T *ᵥ w0 = 0 := by
    funext i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hTker i
  have hTdet : T.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w0, hw0, hTvec⟩
  obtain ⟨hactive, hC, hdetH, hsq, hsnz⟩ :=
    sourceCubic_detOne_originPrincipalSchur_square
      F a hcap hdetOne hTdet k hk
  have hδ : H0.activeDet ≠ 0 := by rw [hactive]; exact hk
  have hprod :
      H0.activeDet ^ 2 * (flow.coeff 0) ^ 2 =
        -H0.activeDet * (w0 k) ^ 2 := by
    calc
      H0.activeDet ^ 2 * (flow.coeff 0) ^ 2 =
        (H0.activeDet * flow.coeff 0) ^ 2 := by ring
      _ = (H0.schurB * w0 k) ^ 2 := by rw [hprimary]
      _ = -H0.activeDet * (w0 k) ^ 2 := by rw [mul_pow, hsq, ← hactive]
  have hcancel :
      H0.activeDet * (H0.activeDet * (flow.coeff 0) ^ 2) =
        H0.activeDet * (-(w0 k ^ 2)) := by
    calc
      _ = H0.activeDet ^ 2 * (flow.coeff 0) ^ 2 := by ring
      _ = -H0.activeDet * (w0 k) ^ 2 := hprod
      _ = H0.activeDet * (-(w0 k ^ 2)) := by ring
  exact ⟨hprimary, mul_left_cancel₀ hδ hcancel⟩

end
end HC4.Polynomial.RankThreeCubic
