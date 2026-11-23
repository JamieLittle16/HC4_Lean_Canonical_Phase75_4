import HC4.Valuation.QuadraticTransverseCapSourceRiccatiCoefficient
import HC4.Valuation.QuadraticTransverseCapSourceRiccatiJets
import Mathlib.Tactic

/-!
# The original source's polynomial transverse Riccati coefficient

This is the literal axis descent of the source's twice-differentiated
determinant-one equation. It uses only the actual four-variable source
F, its transverse cap two, and its constant unit Hessian determinant.

The result is the division-free form of
  det(C) C'' = 2 C' adj(C) C'
in K[x], for the ORIGINAL 3x3 transverse Hessian C(x).

No rational matrix inverse, unit determinant, Riccati assumption,
auxiliary source, marked collision, or endpoint-extractor premise
is introduced.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton
open HC4.Polynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

/-- Every quadratic-transverse-cap determinant-one source satisfies
the exact nine longitudinal-axis Riccati coefficient identities.
The explicit symmetric-three-block contraction avoids any invertibility
premise, so it remains valid in both transverse-rank branches. -/
theorem quadraticTransverseCapSource_axisRiccatiCoefficient
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (i j : Fin 3) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    let D : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
      fun k l => Polynomial.derivative (C.matrix k l)
    Polynomial.derivative (Polynomial.derivative (C.matrix i j)) *
        C.determinantCore =
      2 * (
        D 0 i * quadraticTransverseAdjugateVector0 C
          (D 0 j) (D 1 j) (D 2 j) +
        D 1 i * quadraticTransverseAdjugateVector1 C
          (D 0 j) (D 1 j) (D 2 j) +
        D 2 i * quadraticTransverseAdjugateVector2 C
          (D 0 j) (D 1 j) (D 2 j)) := by
  classical
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let Cg : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
    { a := H.d, b := H.r, c := H.s,
      d := H.x, e := H.y, f := H.z }
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let D : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun k l => Polynomial.derivative (C.matrix k l)
  let phi : MvPolynomial (Fin 4) K →+* Polynomial K :=
    longitudinalAxisRestrictionRingHom (K := K)
  have ha : phi Cg.a = C.a := rfl
  have hb : phi Cg.b = C.b := rfl
  have hc : phi Cg.c = C.c := rfl
  have hd : phi Cg.d = C.d := rfl
  have he : phi Cg.e = C.e := rfl
  have hf : phi Cg.f = C.f := rfl
  have hdetMap : phi Cg.determinantCore = C.determinantCore := by
    simp [GeneralThreeBlock.determinantCore,
      ha, hb, hc, hd, he, hf]
  have hAdj0 (v0 v1 v2 : MvPolynomial (Fin 4) K) :
      phi (quadraticTransverseAdjugateVector0 Cg v0 v1 v2) =
        quadraticTransverseAdjugateVector0 C
          (phi v0) (phi v1) (phi v2) := by
    simp [quadraticTransverseAdjugateVector0,
      ha, hb, hc, hd, he, hf]
  have hAdj1 (v0 v1 v2 : MvPolynomial (Fin 4) K) :
      phi (quadraticTransverseAdjugateVector1 Cg v0 v1 v2) =
        quadraticTransverseAdjugateVector1 C
          (phi v0) (phi v1) (phi v2) := by
    simp [quadraticTransverseAdjugateVector1,
      ha, hb, hc, hd, he, hf]
  have hAdj2 (v0 v1 v2 : MvPolynomial (Fin 4) K) :
      phi (quadraticTransverseAdjugateVector2 Cg v0 v1 v2) =
        quadraticTransverseAdjugateVector2 C
          (phi v0) (phi v1) (phi v2) := by
    simp [quadraticTransverseAdjugateVector2,
      ha, hb, hc, hd, he, hf]
  have hMix0 (t : Fin 3) :
      phi (MvPolynomial.pderiv t.succ H.b) = D 0 t := by
    exact quadraticTransverseSource_axisMixedTransverse_derivative F 0 t
  have hMix1 (t : Fin 3) :
      phi (MvPolynomial.pderiv t.succ H.p) = D 1 t := by
    exact quadraticTransverseSource_axisMixedTransverse_derivative F 1 t
  have hMix2 (t : Fin 3) :
      phi (MvPolynomial.pderiv t.succ H.q) = D 2 t := by
    exact quadraticTransverseSource_axisMixedTransverse_derivative F 2 t
  have hJet :
      phi (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ H.a)) =
        Polynomial.derivative (Polynomial.derivative (C.matrix i j)) := by
    exact quadraticTransverseCapSource_axisLongitudinal_secondTransverseJet
      F i j
  have h := congrArg phi
    (quadraticTransverseCapSource_globalRiccatiCoefficient
      F hbound hdet i j)
  have hmapped :
      phi (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ H.a)) *
          phi Cg.determinantCore =
        2 * (
          phi (MvPolynomial.pderiv i.succ H.b) *
            phi (quadraticTransverseAdjugateVector0 Cg
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q)) +
          phi (MvPolynomial.pderiv i.succ H.p) *
            phi (quadraticTransverseAdjugateVector1 Cg
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q)) +
          phi (MvPolynomial.pderiv i.succ H.q) *
            phi (quadraticTransverseAdjugateVector2 Cg
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q))) := by
    simpa only [map_mul, map_add, map_ofNat] using h
  rw [hJet, hdetMap, hMix0 i, hMix1 i, hMix2 i,
      hAdj0, hAdj1, hAdj2,
      hMix0 j, hMix1 j, hMix2 j] at hmapped
  exact hmapped

end

end HC4.Valuation
