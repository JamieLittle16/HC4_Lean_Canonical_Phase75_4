import Mathlib

/-!
# Explicit inverses for the classified symmetric-gradient families

The symmetric-gradings theorem ends with the two potentials

    x₁x₄ + x₂x₃ + P(x₁^b x₃^a),
    x₁x₄ + x₂x₃ + Q(x₂^a x₄^b).

Their gradients are triangular after reading the coordinates in the right
order.  This module formalises the displayed inverse formulae at the algebraic
level.  The function supplied as `dP` or `dQ` represents the derivative of the
univariate polynomial; no analytic or differentiability assumptions are
needed for the composition calculation.
-/

namespace HC4.ClassifiedFamilies

/-- A point in four-dimensional affine space. -/
@[ext]
structure Point4 (K : Type*) where
  x1 : K
  x2 : K
  x3 : K
  x4 : K
  deriving DecidableEq, Repr

section CommRing

variable {K : Type*} [CommRing K]

/-- The invariant `r = x₁^b x₃^a`. -/
def rValue (a b : ℕ) (x : Point4 K) : K :=
  x.x1 ^ b * x.x3 ^ a

/-- The invariant `s = x₂^a x₄^b`. -/
def sValue (a b : ℕ) (x : Point4 K) : K :=
  x.x2 ^ a * x.x4 ^ b

/--
The gradient map of the `r`-family, with `dP` standing for the derivative of
the univariate correction.
-/
def rGradientMap (a b : ℕ) (dP : K → K) (x : Point4 K) : Point4 K :=
  { x1 := x.x4 + (b : K) * x.x1 ^ (b - 1) * x.x3 ^ a * dP (rValue a b x)
    x2 := x.x3
    x3 := x.x2 + (a : K) * x.x1 ^ b * x.x3 ^ (a - 1) * dP (rValue a b x)
    x4 := x.x1 }

/-- The explicit triangular inverse of `rGradientMap`. -/
def rGradientInverse (a b : ℕ) (dP : K → K) (z : Point4 K) : Point4 K :=
  { x1 := z.x4
    x2 := z.x3 - (a : K) * z.x4 ^ b * z.x2 ^ (a - 1) *
      dP (z.x4 ^ b * z.x2 ^ a)
    x3 := z.x2
    x4 := z.x1 - (b : K) * z.x4 ^ (b - 1) * z.x2 ^ a *
      dP (z.x4 ^ b * z.x2 ^ a) }

/-- The `r` invariant is recoverable directly from the second and fourth outputs. -/
@[simp] theorem rValue_rGradientMap (a b : ℕ) (dP : K → K) (x : Point4 K) :
    (rGradientMap a b dP x).x4 ^ b * (rGradientMap a b dP x).x2 ^ a =
      rValue a b x := by
  simp [rGradientMap, rValue]

/-- Applying the displayed `r`-inverse after the gradient gives the input. -/
theorem rGradientInverse_comp_map (a b : ℕ) (dP : K → K) :
    Function.LeftInverse (rGradientInverse a b dP) (rGradientMap a b dP) := by
  intro x
  ext <;> simp [rGradientInverse, rGradientMap, rValue]

/-- Applying the `r`-gradient after the displayed inverse gives the input. -/
theorem rGradientMap_comp_inverse (a b : ℕ) (dP : K → K) :
    Function.RightInverse (rGradientInverse a b dP) (rGradientMap a b dP) := by
  intro z
  ext <;> simp [rGradientInverse, rGradientMap, rValue]

/-- The gradient map of every `r`-family is bijective. -/
theorem rGradientMap_bijective (a b : ℕ) (dP : K → K) :
    Function.Bijective (rGradientMap a b dP) := by
  refine ⟨(rGradientInverse_comp_map a b dP).injective, ?_⟩
  exact (rGradientMap_comp_inverse a b dP).surjective

/--
The gradient map of the coordinate-reversed `s`-family, with `dQ` standing
for the derivative of the univariate correction.
-/
def sGradientMap (a b : ℕ) (dQ : K → K) (x : Point4 K) : Point4 K :=
  { x1 := x.x4
    x2 := x.x3 + (a : K) * x.x2 ^ (a - 1) * x.x4 ^ b * dQ (sValue a b x)
    x3 := x.x2
    x4 := x.x1 + (b : K) * x.x2 ^ a * x.x4 ^ (b - 1) * dQ (sValue a b x) }

/-- The explicit triangular inverse of `sGradientMap`. -/
def sGradientInverse (a b : ℕ) (dQ : K → K) (z : Point4 K) : Point4 K :=
  { x1 := z.x4 - (b : K) * z.x3 ^ a * z.x1 ^ (b - 1) *
      dQ (z.x3 ^ a * z.x1 ^ b)
    x2 := z.x3
    x3 := z.x2 - (a : K) * z.x3 ^ (a - 1) * z.x1 ^ b *
      dQ (z.x3 ^ a * z.x1 ^ b)
    x4 := z.x1 }

/-- The `s` invariant is recoverable directly from the first and third outputs. -/
@[simp] theorem sValue_sGradientMap (a b : ℕ) (dQ : K → K) (x : Point4 K) :
    (sGradientMap a b dQ x).x3 ^ a * (sGradientMap a b dQ x).x1 ^ b =
      sValue a b x := by
  simp [sGradientMap, sValue]

/-- Applying the displayed `s`-inverse after the gradient gives the input. -/
theorem sGradientInverse_comp_map (a b : ℕ) (dQ : K → K) :
    Function.LeftInverse (sGradientInverse a b dQ) (sGradientMap a b dQ) := by
  intro x
  ext <;> simp [sGradientInverse, sGradientMap, sValue]

/-- Applying the `s`-gradient after the displayed inverse gives the input. -/
theorem sGradientMap_comp_inverse (a b : ℕ) (dQ : K → K) :
    Function.RightInverse (sGradientInverse a b dQ) (sGradientMap a b dQ) := by
  intro z
  ext <;> simp [sGradientInverse, sGradientMap, sValue]

/-- The gradient map of every `s`-family is bijective. -/
theorem sGradientMap_bijective (a b : ℕ) (dQ : K → K) :
    Function.Bijective (sGradientMap a b dQ) := by
  refine ⟨(sGradientInverse_comp_map a b dQ).injective, ?_⟩
  exact (sGradientMap_comp_inverse a b dQ).surjective

end CommRing

end HC4.ClassifiedFamilies
