import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyTotalAssembly
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurProjectiveWedgeConstancy
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# Stage 4B29: reduce nonconstant projective motion to one active RS2 witness

B28 leaves only certified rank-two repair or an RS2-ready first spatial key

    a * x₀^e * L^m,

and B27 shows that vanishing of all projective wedges of the Stage-3 full
polynomial kernel already gives the constant-projective-direction certificate
consumed by Stage 4A.

This file isolates the exact final provenance boundary.

If one projective wedge is nonzero, then because the first-key transverse
profile is nonzero, both its scalar coefficient and its transverse linear form
`L` are nonzero.  Over the infinite characteristic-zero field we may therefore
choose a source point at which simultaneously

* the chosen projective wedge is nonzero;
* `x₀` is nonzero;
* `L` is nonzero.

At such an active point the sharp B25 theorem says that any pair of projective
motion scalars satisfying the Euler and null-RS2 identities must both vanish.
Hence a nonzero projective-motion witness satisfying those identities is
impossible.

Consequently the *only* remaining mathematical theorem after this file is the
source-to-Schur provenance statement: a nonzero projective wedge must produce
such a nonzero Euler/RS2 scalar witness from the already-retained raw Schur
prefix and first-actual source/Hessian layer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Lift the transverse linear form back to the four source variables -/

/-- The canonical inclusion of a transverse polynomial in variables `1,2,3`
into the four-variable source ring. -/
def liftTransversePolynomial
    (P : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.rename (fun i : Fin 3 => i.succ) P

/-- The transverse-variable inclusion is injective. -/
theorem liftTransversePolynomial_ne_zero
    (P : MvPolynomial (Fin 3) K)
    (hP : P ≠ 0) :
    liftTransversePolynomial P ≠ 0 := by
  intro hzero
  apply hP
  have hinj : Function.Injective (fun i : Fin 3 => i.succ) := by
    intro i j hij
    exact Fin.succ_inj.mp hij
  apply
    (MvPolynomial.rename_injective
      (fun i : Fin 3 => i.succ) hinj)
  simpa using hzero

@[simp] theorem eval_liftTransversePolynomial
    (a : Fin 4 → K)
    (P : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval a (liftTransversePolynomial P) =
      MvPolynomial.eval (fun i : Fin 3 => a i.succ) P := by
  unfold liftTransversePolynomial
  rw [MvPolynomial.eval_rename]
  rfl

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- In an RS2-ready normal form the scalar coefficient is genuinely nonzero.
Otherwise the nonzero first transverse profile would vanish. -/
theorem FirstKeyXeLmRS2ReadyData.coefficient_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D) :
    N.normalForm.coefficient ≠ 0 := by
  intro hzero
  apply D.transverseSourceProfile_ne_zero
  rw [N.normalForm.transverse_eq, hzero]
  simp

/-- The transverse linear factor in an RS2-ready first key is nonzero. -/
theorem FirstKeyXeLmRS2ReadyData.linearForm_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D) :
    N.normalForm.linearForm ≠ 0 := by
  intro hzero
  apply D.transverseSourceProfile_ne_zero
  rw [N.normalForm.transverse_eq, hzero]
  simp [Nat.ne_of_gt D.transverseDegree_pos]

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- Polynomial numerator of one infinitesimal projective wedge of the Stage-3
full kernel. -/
def projectiveWedge
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) :
    MvPolynomial (Fin 4) K :=
  E.fullVector i * MvPolynomial.pderiv k (E.fullVector j) -
    E.fullVector j * MvPolynomial.pderiv k (E.fullVector i)

/-- Zero projective-wedge polynomial is exactly the denominator-free equality
used by B27. -/
theorem projectiveWedge_eq_zero_iff
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) :
    E.projectiveWedge i j k = 0 ↔
      E.fullVector i * MvPolynomial.pderiv k (E.fullVector j) =
        E.fullVector j * MvPolynomial.pderiv k (E.fullVector i) := by
  unfold projectiveWedge
  exact sub_eq_zero

/-- Active source point witnessing a genuinely nonzero projective wedge.
The same point avoids both coordinate divisors occurring in the `x₀^e L^m`
RS2 formula. -/
structure ActiveProjectiveWedgePointData
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) where
  point : Fin 4 → K
  wedge_ne_zero :
    MvPolynomial.eval point (E.projectiveWedge i j k) ≠ 0
  longitudinal_ne_zero : point 0 ≠ 0
  linearForm_ne_zero :
    MvPolynomial.eval (fun r : Fin 3 => point r.succ)
      N.normalForm.linearForm ≠ 0

/-- A nonzero projective wedge can be witnessed away from both active
coordinate hyperplanes `x₀=0` and `L=0`.

This is the generic-point reduction needed before applying the field-valued
B25 RS2 rigidity theorem. -/
theorem exists_activeProjectiveWedgePointData
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4)
    (hwedge : E.projectiveWedge i j k ≠ 0) :
    Nonempty (E.ActiveProjectiveWedgePointData N i j k) := by
  let L4 : MvPolynomial (Fin 4) K :=
    liftTransversePolynomial N.normalForm.linearForm
  have hL4 : L4 ≠ 0 := by
    dsimp [L4]
    exact liftTransversePolynomial_ne_zero
      N.normalForm.linearForm N.linearForm_ne_zero
  have hX0 : (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K) ≠ 0 := by
    simp
  have hprod :
      (E.projectiveWedge i j k * MvPolynomial.X (0 : Fin 4)) * L4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hwedge hX0) hL4
  rcases exists_source_eval_ne_zero_of_ne_zero
      ((E.projectiveWedge i j k * MvPolynomial.X (0 : Fin 4)) * L4)
      hprod with ⟨a, ha⟩
  refine ⟨{
    point := a
    wedge_ne_zero := ?_
    longitudinal_ne_zero := ?_
    linearForm_ne_zero := ?_
  }⟩
  · intro hw0
    apply ha
    simp [hw0]
  · intro hx0
    apply ha
    simp [hx0]
  · intro hL0
    apply ha
    have hL4eval : MvPolynomial.eval a L4 = 0 := by
      dsimp [L4]
      simpa using hL0
    simp [hL4eval]

/-- Scalar projective-motion data whose existence would contradict B25.

The final source-to-Schur provenance theorem only has to manufacture this
record from a nonzero wedge.  No further projectivisation or source normal
form work remains. -/
structure ActiveProjectiveRS2Witness
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (i j k : Fin 4) where
  activePoint : E.ActiveProjectiveWedgePointData N i j k
  rhoX : K
  rhoL : K
  motion_ne_zero : rhoX ≠ 0 ∨ rhoL ≠ 0
  euler :
    activePoint.point 0 * rhoX +
      MvPolynomial.eval (fun r : Fin 3 => activePoint.point r.succ)
        N.normalForm.linearForm * rhoL = 0
  rs2 :
    (D.transverseDegree : K) * ((D.transverseDegree : K) - 1) *
          (activePoint.point 0 * rhoX) ^ 2 -
        2 * (D.sourceExponent : K) * (D.transverseDegree : K) *
          (activePoint.point 0 * rhoX) *
          (MvPolynomial.eval (fun r : Fin 3 => activePoint.point r.succ)
            N.normalForm.linearForm * rhoL) +
        (D.sourceExponent : K) * ((D.sourceExponent : K) - 1) *
          (MvPolynomial.eval (fun r : Fin 3 => activePoint.point r.succ)
            N.normalForm.linearForm * rhoL) ^ 2 = 0

/-- **B25 kills every active projective RS2 witness.** -/
theorem ActiveProjectiveRS2Witness.elim
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {N : C.FirstKeyXeLmRS2ReadyData D}
    {E : DenominatorClearedSpecialSchurKernelData C}
    {i j k : Fin 4}
    (W : E.ActiveProjectiveRS2Witness N i j k) : False := by
  have hzero :=
    xeLm_rs2ProjectiveDerivatives_eq_zero_of_totalDegree_two_le
      D.sourceExponent D.transverseDegree N.totalDegree_two_le
      (W.activePoint.point 0)
      (MvPolynomial.eval (fun r : Fin 3 => W.activePoint.point r.succ)
        N.normalForm.linearForm)
      W.rhoX W.rhoL
      W.activePoint.longitudinal_ne_zero
      W.activePoint.linearForm_ne_zero
      W.euler W.rs2
  rcases W.motion_ne_zero with hx | hL
  · exact hx hzero.1
  · exact hL hzero.2

/-- Exact remaining provenance interface on an RS2-ready packet: every
nonzero projective wedge produces the active scalar Euler/RS2 witness above. -/
def HasRS2ProjectiveWedgeProvenance
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C) : Prop :=
  ∀ i j k : Fin 4,
    E.projectiveWedge i j k ≠ 0 →
      Nonempty (E.ActiveProjectiveRS2Witness N i j k)

/-- Once the final provenance interface is supplied, every projective wedge
vanishes. -/
theorem hasVanishingProjectiveWedges_of_rs2Provenance
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (hprov : E.HasRS2ProjectiveWedgeProvenance N) :
    E.HasVanishingProjectiveWedges := by
  intro i j k
  apply (E.projectiveWedge_eq_zero_iff i j k).mp
  by_contra hwedge
  rcases hprov i j k hwedge with ⟨W⟩
  exact W.elim

/-- Compose the sharp RS2 reduction with B27 and Stage 4A: provenance of the
Euler/RS2 witness already yields an honest constant special-fibre source
kernel. -/
theorem constantSpecialSourceKernel_of_rs2Provenance
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    (N : C.FirstKeyXeLmRS2ReadyData D)
    (E : DenominatorClearedSpecialSchurKernelData C)
    (hprov : E.HasRS2ProjectiveWedgeProvenance N) :
    Nonempty (ConstantSpecialSourceKernelData C) := by
  exact E.constantSpecialSourceKernel_of_vanishingProjectiveWedges
    (E.hasVanishingProjectiveWedges_of_rs2Provenance N hprov)

end DenominatorClearedSpecialSchurKernelData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
