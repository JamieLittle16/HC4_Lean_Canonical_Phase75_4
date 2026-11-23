import HC4.Polynomial.RankThreeCubicDetOneAdjugateLowJetNormalization
import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib.Tactic

/-!
# Entire actual quadratic transverse adjugate from the source low jet

At the original source point (x=a,y=0), the transverse weight-two
Hessian T may be singular. If it has a nonzero K-rational kernel
direction w0, det Hess(F)=1 forces T to have rank precisely two,
a nonzero principal cofactor, and nonzero longitudinal coupling.

The earlier actual-source low-jet square identity, combined with
the kernel-alignment and rank-one adjugate identities, now yields
a coordinate-independent equality for EVERY cofactor:

   g^2 * adj(T)[i,j] = -w0[i]*w0[j].

Here g is the scalar constant coefficient of the ORIGINAL
strictly-below-two source mixed Hessian row paired with w0.

No extra choice of a square root, chart, or endpoint premise
appears in the theorem statement. This is a necessary constraint,
not an obstruction contradiction.
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

/-- All nine cofactors of the original quadratic transverse Hessian
are exactly normalized by one nonzero source low-jet scalar and
its nonzero transverse kernel vector. -/
theorem sourceCubic_detOne_originQuadraticAdjugate_lowJet_normalized
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w0 : Fin 3 → K) (hw0 : w0 ≠ 0)
    (hTker : ∀ i : Fin 3,
      (∑ j : Fin 3,
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (referenceSlice a
            (hessian (initialForm transverseCubicWeight 2 F)
              (.inr i) (.inr j)))) * w0 j) = 0) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) - L2
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    let flow : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)
    ∀ i j : Fin 3,
      (flow.coeff 0) ^ 2 * T.adjugate i j = -(w0 i * w0 j) := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) - L2
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  let flow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)
  have hTkerVec : T *ᵥ w0 = 0 := by
    funext i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hTker i
  have hdetT : T.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w0, hw0, hTkerVec⟩
  have hsourceSym : (sourceTransverseHessian a L2).IsSymm :=
    sourceTransverseHessian_isSymm a L2
  have hSym : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hij := hsourceSym.apply i j
    exact congrArg
      (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) hij
  obtain ⟨k, hk⟩ :=
    sourceCubic_detOne_originQuadraticKernel_principalCofactor
      F a hcap hdetOne w0 hw0 hTker
  have hwk : w0 k ≠ 0 :=
    principalCofactor_kernelVector_pivot_ne_zero
      T w0 hTkerVec hw0 k hk
  obtain ⟨_, hlowSquare⟩ :=
    sourceCubic_detOne_originSchur_lowJetSquare
      F a hcap hdetOne w0 hw0 hTker k hk
  obtain ⟨hactive, _, _, _, _⟩ :=
    sourceCubic_detOne_originPrincipalSchur_square
      F a hcap hdetOne hdetT k hk
  have hsquare :
      T.adjugate k k * (flow.coeff 0) ^ 2 =
        -(w0 k ^ 2) := by
    rw [← hactive]
    exact hlowSquare
  exact symmetricThree_kernel_adjugate_lowJet_normalized
    T hSym w0 hTkerVec hdetT (flow.coeff 0) k hk hwk hsquare

end
end HC4.Polynomial.RankThreeCubic
