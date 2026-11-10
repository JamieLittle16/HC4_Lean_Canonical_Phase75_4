import HC4.Valuation.QuadraticTransverseCapSourceSchurSecondJet
import Mathlib.Tactic

/-!
# SOURCE-HONEST denominator-cleared transverse Riccati identity

This is the exact y² Hessian-determinant coefficient for a REAL
four-variable polynomial potential with transverse degree at most two:

    det C(x) * C''(x) = 2 C'(x) * adj(C(x)) * C'(x),

where C(x) is the actual source's transverse 3x3 Hessian restricted
to the distinguished x-axis. The conclusion is an equality of
POLYNOMIALS in K[x], before any rational inversion.

The proof uses:
  1. the global source Schur determinant identity (det Hess F = 1),
  2. both transverse derivations of that global identity,
  3. the honest quadratic transverse cap to kill higher jets,
  4. the exact source-axis Hessian jet identities,
  5. restriction via the original longitudinal-axis ring homomorphism.

There are NO invented sources, rank-three assumptions, abstract
Riccati hypotheses, or additional endpoint producers.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The six global transverse Hessian block entries become the six
genuine axis-polynomial Hessian entries under source-axis restriction.
The source is unchanged throughout. -/
theorem quadraticTransverseCapSource_globalThreeBlock_axisEntries
    (F : MvPolynomial (Fin 4) K) :
    let G := quadraticTransverseCapSourceGlobalThreeBlock F
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    longitudinalAxisRestrictionRingHom (K := K) G.a = C.a ∧
    longitudinalAxisRestrictionRingHom (K := K) G.b = C.b ∧
    longitudinalAxisRestrictionRingHom (K := K) G.c = C.c ∧
    longitudinalAxisRestrictionRingHom (K := K) G.d = C.d ∧
    longitudinalAxisRestrictionRingHom (K := K) G.e = C.e ∧
    longitudinalAxisRestrictionRingHom (K := K) G.f = C.f := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rfl

/-- The three transverse derivatives of the genuine original-source
mixed Hessian row, after source-axis restriction, are exactly the
appropriate longitudinal derivatives of the transverse Hessian C. -/
theorem quadraticTransverseCapSource_globalMixedDerivative_axis
    (F : MvPolynomial (Fin 4) K)
    (m j : Fin 3) :
    let H := quadraticTransverseCapSourceGlobalFourBlock F
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    longitudinalAxisRestrictionRingHom (K := K)
      (MvPolynomial.pderiv j.succ
        (match m with
         | 0 => H.b
         | 1 => H.p
         | 2 => H.q)) =
      Polynomial.derivative (C.matrix m j) := by
  dsimp only
  fin_cases m <;>
    simpa [quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (show
        longitudinalAxisRestrictionRingHom (K := K)
          (MvPolynomial.pderiv j.succ
            (HC4.Polynomial.hessian F 0 (Fin.succ m))) =
          Polynomial.derivative
            ((quadraticTransverseCapSourceAxisThreeBlock F).matrix m j)
        from by
          rw [← quadraticTransverseCapSource_axisThreeBlock_entry F m j]
          exact quadraticTransverseSource_axisMixedTransverse_derivative F m j)

/-- The ACTUAL source Hessian determinant forces every
denominator-cleared transverse Riccati matrix entry in K[x].

No assumption about det C is required; that determinant can be
singular. The previously proved rank-two contradiction separately
eliminates det C=0 at the reachable quadratic E3 relevel. -/
theorem quadraticTransverseCap_two_sourceRiccati_cleared
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (i j : Fin 3) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    C.determinantCore *
        Polynomial.derivative (Polynomial.derivative (C.matrix i j)) =
      2 * (
        Polynomial.derivative (C.matrix 0 i) *
          quadraticTransverseAdjugateVector0 C
            (Polynomial.derivative (C.matrix 0 j))
            (Polynomial.derivative (C.matrix 1 j))
            (Polynomial.derivative (C.matrix 2 j)) +
        Polynomial.derivative (C.matrix 1 i) *
          quadraticTransverseAdjugateVector1 C
            (Polynomial.derivative (C.matrix 0 j))
            (Polynomial.derivative (C.matrix 1 j))
            (Polynomial.derivative (C.matrix 2 j)) +
        Polynomial.derivative (C.matrix 2 i) *
          quadraticTransverseAdjugateVector2 C
            (Polynomial.derivative (C.matrix 0 j))
            (Polynomial.derivative (C.matrix 1 j))
            (Polynomial.derivative (C.matrix 2 j))) := by
  dsimp only
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let G := quadraticTransverseCapSourceGlobalThreeBlock F
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let φ : MvPolynomial (Fin 4) K →+* Polynomial K :=
    longitudinalAxisRestrictionRingHom (K := K)
  obtain ⟨ha, hb, hc, hd, he, hf⟩ :=
    quadraticTransverseCapSource_globalThreeBlock_axisEntries F
  have hdetmap : φ G.determinantCore = C.determinantCore := by
    simp [GeneralThreeBlock.determinantCore,
      ha, hb, hc, hd, he, hf]
  have hmix₀ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.b) =
        Polynomial.derivative (C.matrix 0 k) := by
    simpa [φ, H, C,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (0 : Fin 3) k)
  have hmix₁ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.p) =
        Polynomial.derivative (C.matrix 1 k) := by
    simpa [φ, H, C,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (1 : Fin 3) k)
  have hmix₂ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.q) =
        Polynomial.derivative (C.matrix 2 k) := by
    simpa [φ, H, C,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (2 : Fin 3) k)
  have hquad :
      φ (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ H.a)) =
        Polynomial.derivative
          (Polynomial.derivative (C.matrix i j)) := by
    simpa [φ, H, C, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisLongitudinal_secondTransverseJet
        F i j)
  have hadj₀ :
      φ (quadraticTransverseAdjugateVector0 G
          (MvPolynomial.pderiv j.succ H.b)
          (MvPolynomial.pderiv j.succ H.p)
          (MvPolynomial.pderiv j.succ H.q)) =
        quadraticTransverseAdjugateVector0 C
          (Polynomial.derivative (C.matrix 0 j))
          (Polynomial.derivative (C.matrix 1 j))
          (Polynomial.derivative (C.matrix 2 j)) := by
    simp [quadraticTransverseAdjugateVector0,
      ha, hb, hc, hd, he, hf,
      hmix₀ j, hmix₁ j, hmix₂ j]
  have hadj₁ :
      φ (quadraticTransverseAdjugateVector1 G
          (MvPolynomial.pderiv j.succ H.b)
          (MvPolynomial.pderiv j.succ H.p)
          (MvPolynomial.pderiv j.succ H.q)) =
        quadraticTransverseAdjugateVector1 C
          (Polynomial.derivative (C.matrix 0 j))
          (Polynomial.derivative (C.matrix 1 j))
          (Polynomial.derivative (C.matrix 2 j)) := by
    simp [quadraticTransverseAdjugateVector1,
      ha, hb, hc, hd, he, hf,
      hmix₀ j, hmix₁ j, hmix₂ j]
  have hadj₂ :
      φ (quadraticTransverseAdjugateVector2 G
          (MvPolynomial.pderiv j.succ H.b)
          (MvPolynomial.pderiv j.succ H.p)
          (MvPolynomial.pderiv j.succ H.q)) =
        quadraticTransverseAdjugateVector2 C
          (Polynomial.derivative (C.matrix 0 j))
          (Polynomial.derivative (C.matrix 1 j))
          (Polynomial.derivative (C.matrix 2 j)) := by
    simp [quadraticTransverseAdjugateVector2,
      ha, hb, hc, hd, he, hf,
      hmix₀ j, hmix₁ j, hmix₂ j]
  have hsource :=
    quadraticTransverseCap_two_sourceGlobalSchur_secondJet
      F hbound hdet i j
  have hmapped := congrArg φ hsource
  dsimp only at hmapped
  simp only [map_mul, map_add, map_sub, map_ofNat] at hmapped
  rw [hquad, hdetmap, hmix₀ i, hmix₁ i, hmix₂ i,
      hadj₀, hadj₁, hadj₂] at hmapped
  linear_combination hmapped

end

end HC4.Valuation
