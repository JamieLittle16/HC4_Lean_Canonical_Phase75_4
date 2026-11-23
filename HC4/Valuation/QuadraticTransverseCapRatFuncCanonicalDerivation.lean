import HC4.Valuation.QuadraticTransverseCapSourceRegularPolynomialInverse
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Tactic

/-!
# The canonical rational X-derivation by square-zero polynomial jets

This is purely algebraic. Embed each polynomial as a dual-number jet
  p ↦ (p(X),p'(X)), ε²=0.
The first coordinate is its original image in K(X), so every nonzero
polynomial maps to an invertible dual number. Localization lifts the
jet homomorphism from K[X] to all of K(X).

The second coordinate is automatically a K-linear derivation, and
its value on the rational indeterminate X is 1. No quotient-rule
well-definedness calculation is needed.
-/

namespace HC4.Valuation

noncomputable section

open scoped nonZeroDivisors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 2048

variable {K : Type*} [Field K]

private abbrev DualRat (K : Type*) [Field K] :=
  TrivSqZeroExt (RatFunc K) (RatFunc K)

private abbrev polynomialEmbedding : Polynomial K →+* RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K)

/-- The first-order algebraic Taylor jet, with no formal series. -/
noncomputable def quadraticTransverse_polynomialDualJet :
    Polynomial K →+* DualRat K where
  toFun p :=
    (polynomialEmbedding (K := K) p,
      polynomialEmbedding (K := K) (Polynomial.derivative p))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [Polynomial.derivative_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp
    · change
        polynomialEmbedding (K := K) (Polynomial.derivative (p * q)) =
          polynomialEmbedding (K := K) p *
              polynomialEmbedding (K := K) (Polynomial.derivative q) +
          polynomialEmbedding (K := K) (Polynomial.derivative p) *
              polynomialEmbedding (K := K) q
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul]
      ring

private theorem quadraticTransverse_polynomialDualJet_unit
    (s : (Polynomial K)⁰) :
    IsUnit (quadraticTransverse_polynomialDualJet (K := K) (s : Polynomial K)) := by
  apply (TrivSqZeroExt.isUnit_iff_isUnit_fst).2
  change IsUnit (polynomialEmbedding (K := K) (s : Polynomial K))
  exact (isUnit_iff_ne_zero).2
    (RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero s.property))

/-- Universal localization of the polynomial jet across EVERY
nonzero denominator. It is a ring homomorphism to dual numbers. -/
noncomputable def quadraticTransverse_rationalDualJet :
    RatFunc K →+* DualRat K :=
  IsLocalization.lift (M := (Polynomial K)⁰)
    (S := RatFunc K)
    (g := quadraticTransverse_polynomialDualJet (K := K))
    (quadraticTransverse_polynomialDualJet_unit (K := K))

private theorem quadraticTransverse_rationalDualJet_poly
    (p : Polynomial K) :
    quadraticTransverse_rationalDualJet (K := K)
        (polynomialEmbedding (K := K) p) =
      quadraticTransverse_polynomialDualJet (K := K) p := by
  exact IsLocalization.lift_eq
    (M := (Polynomial K)⁰)
    (quadraticTransverse_polynomialDualJet_unit (K := K)) p

/-- The zeroth-order coefficient of the lifted jet is the
IDENTITY map on K(X). This is why its first-order coefficient
satisfies the Leibniz rule for the original rational functions. -/
theorem quadraticTransverse_rationalDualJet_fst
    (z : RatFunc K) :
    (quadraticTransverse_rationalDualJet (K := K) z).fst = z := by
  let j := quadraticTransverse_rationalDualJet (K := K)
  let p : RatFunc K →+* RatFunc K :=
    (TrivSqZeroExt.fstHom
      (RatFunc K) (RatFunc K) (RatFunc K)).toRingHom.comp j
  have heq : p = RingHom.id (RatFunc K) := by
    apply IsLocalization.ringHom_ext ((Polynomial K)⁰)
    apply RingHom.ext
    intro q
    change (j (polynomialEmbedding (K := K) q)).fst =
      polynomialEmbedding (K := K) q
    rw [quadraticTransverse_rationalDualJet_poly]
    rfl
  have hz := congrArg (fun f : RatFunc K →+* RatFunc K => f z) heq
  simpa [p] using hz

private theorem quadraticTransverse_rationalDualJet_ground (a : K) :
    quadraticTransverse_rationalDualJet (K := K)
        (algebraMap K (RatFunc K) a) =
      ((algebraMap K (RatFunc K) a), (0 : RatFunc K)) := by
  apply TrivSqZeroExt.ext
  · simp [quadraticTransverse_rationalDualJet_fst]
  · have hconstant :
        algebraMap K (RatFunc K) a =
          polynomialEmbedding (K := K) (Polynomial.C a) := by
        simp
    rw [hconstant, quadraticTransverse_rationalDualJet_poly]
    simp [quadraticTransverse_polynomialDualJet]

/-- Canonical K-derivation of K(X), obtained without differentiating
a chosen numerator/denominator representation.

This is the remaining differential-algebra input needed by
quadraticTransverseCapSource_regularPolynomialInverse_of_derivation. -/
noncomputable def quadraticTransverse_canonicalRatFuncDerivation :
    Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := fun z => (quadraticTransverse_rationalDualJet (K := K) z).snd
      map_add' := by
        intro x y
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := by
        intro a z
        change
          (quadraticTransverse_rationalDualJet (K := K) (a • z)).snd =
            a • (quadraticTransverse_rationalDualJet (K := K) z).snd
        rw [Algebra.smul_def,
          map_mul,
          quadraticTransverse_rationalDualJet_ground (K := K) a,
          TrivSqZeroExt.snd_mul]
        simp [Algebra.smul_def, smul_eq_mul, MulOpposite.op_smul] }
    (by
      intro x y
      change
        (quadraticTransverse_rationalDualJet (K := K) (x * y)).snd =
          x • (quadraticTransverse_rationalDualJet (K := K) y).snd +
          y • (quadraticTransverse_rationalDualJet (K := K) x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul]
      rw [quadraticTransverse_rationalDualJet_fst (K := K) x,
          quadraticTransverse_rationalDualJet_fst (K := K) y]
      simp [smul_eq_mul, MulOpposite.op_smul, mul_comm])

/-- The rational indeterminate has canonical derivative one. -/
theorem quadraticTransverse_canonicalRatFuncDerivation_X :
    quadraticTransverse_canonicalRatFuncDerivation (K := K)
      (RatFunc.X : RatFunc K) = 1 := by
  change
    (quadraticTransverse_rationalDualJet (K := K)
      (RatFunc.X : RatFunc K)).snd = 1
  rw [← RatFunc.algebraMap_X,
    quadraticTransverse_rationalDualJet_poly]
  simp [quadraticTransverse_polynomialDualJet]

/-- An immediate regular-branch consequence, with NO derivation
or Riccati assumptions in the statement: C(x) has a polynomial
two-sided inverse and nonzero constant determinant. -/
theorem quadraticTransverseCapSource_regularPolynomialInverse
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * P = 1 ∧
      P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
      ∃ d : K, d ≠ 0 ∧
        (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
          Polynomial.C d := by
  exact quadraticTransverseCapSource_regularPolynomialInverse_of_derivation
    F hcap hdet hregular
    (quadraticTransverse_canonicalRatFuncDerivation (K := K))
    (quadraticTransverse_canonicalRatFuncDerivation_X (K := K))

end

end HC4.Valuation
