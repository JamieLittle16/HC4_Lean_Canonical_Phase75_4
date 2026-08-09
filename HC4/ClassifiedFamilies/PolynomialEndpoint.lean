import HC4.ClassifiedFamilies.ClassifiedEquiv
import Mathlib

/-!
# Polynomial endpoint for the classified families

This module specialises the previously verified triangular maps to the actual
univariate polynomial corrections occurring in the theorem.  The derivative
is the formal polynomial derivative, evaluated at the invariant `r` or `s`.
-/

namespace HC4.ClassifiedFamilies

section CommRing

variable {K : Type*} [CommRing K]

/-- The value of the classified `r`-potential at a point. -/
def rPolynomialPotentialValue (a b : ℕ) (P : Polynomial K) (x : Point4 K) : K :=
  x.x1 * x.x4 + x.x2 * x.x3 + P.eval (rValue a b x)

/-- The value of the classified `s`-potential at a point. -/
def sPolynomialPotentialValue (a b : ℕ) (P : Polynomial K) (x : Point4 K) : K :=
  x.x1 * x.x4 + x.x2 * x.x3 + P.eval (sValue a b x)

/-- The displayed gradient formula for `p + q + P(r)`. -/
noncomputable def rPolynomialGradient (a b : ℕ) (P : Polynomial K) : Point4 K → Point4 K :=
  rGradientMap a b (fun t => P.derivative.eval t)

/-- The displayed gradient formula for `p + q + P(s)`. -/
noncomputable def sPolynomialGradient (a b : ℕ) (P : Polynomial K) : Point4 K → Point4 K :=
  sGradientMap a b (fun t => P.derivative.eval t)

/-- Explicit inverse for the polynomial `r`-family. -/
noncomputable def rPolynomialGradientInverse (a b : ℕ) (P : Polynomial K) : Point4 K → Point4 K :=
  rGradientInverse a b (fun t => P.derivative.eval t)

/-- Explicit inverse for the polynomial `s`-family. -/
noncomputable def sPolynomialGradientInverse (a b : ℕ) (P : Polynomial K) : Point4 K → Point4 K :=
  sGradientInverse a b (fun t => P.derivative.eval t)

/-- The explicit `r` inverse is a left inverse. -/
theorem rPolynomialGradientInverse_comp
    (a b : ℕ) (P : Polynomial K) :
    Function.LeftInverse (rPolynomialGradientInverse a b P)
      (rPolynomialGradient a b P) := by
  exact rGradientInverse_comp_map a b (fun t => P.derivative.eval t)

/-- The explicit `r` inverse is a right inverse. -/
theorem rPolynomialGradient_comp_inverse
    (a b : ℕ) (P : Polynomial K) :
    Function.RightInverse (rPolynomialGradientInverse a b P)
      (rPolynomialGradient a b P) := by
  exact rGradientMap_comp_inverse a b (fun t => P.derivative.eval t)

/-- Every polynomial `r`-family gradient is bijective. -/
theorem rPolynomialGradient_bijective
    (a b : ℕ) (P : Polynomial K) :
    Function.Bijective (rPolynomialGradient a b P) := by
  exact rGradientMap_bijective a b (fun t => P.derivative.eval t)

/-- The explicit `s` inverse is a left inverse. -/
theorem sPolynomialGradientInverse_comp
    (a b : ℕ) (P : Polynomial K) :
    Function.LeftInverse (sPolynomialGradientInverse a b P)
      (sPolynomialGradient a b P) := by
  exact sGradientInverse_comp_map a b (fun t => P.derivative.eval t)

/-- The explicit `s` inverse is a right inverse. -/
theorem sPolynomialGradient_comp_inverse
    (a b : ℕ) (P : Polynomial K) :
    Function.RightInverse (sPolynomialGradientInverse a b P)
      (sPolynomialGradient a b P) := by
  exact sGradientMap_comp_inverse a b (fun t => P.derivative.eval t)

/-- Every polynomial `s`-family gradient is bijective. -/
theorem sPolynomialGradient_bijective
    (a b : ℕ) (P : Polynomial K) :
    Function.Bijective (sPolynomialGradient a b P) := by
  exact sGradientMap_bijective a b (fun t => P.derivative.eval t)

/-- The two polynomial outcomes in one datatype. -/
inductive PolynomialBranch (K : Type*) [CommRing K] where
  | r (P : Polynomial K)
  | s (P : Polynomial K)

/-- Gradient formula attached to a polynomial branch. -/
noncomputable def polynomialBranchGradient (a b : ℕ) :
    PolynomialBranch K → Point4 K → Point4 K
  | .r P => rPolynomialGradient a b P
  | .s P => sPolynomialGradient a b P

/-- Explicit inverse attached to a polynomial branch. -/
noncomputable def polynomialBranchInverse (a b : ℕ) :
    PolynomialBranch K → Point4 K → Point4 K
  | .r P => rPolynomialGradientInverse a b P
  | .s P => sPolynomialGradientInverse a b P

/-- Every classified polynomial branch has a two-sided explicit inverse. -/
theorem polynomialBranchInverse_comp_gradient
    (a b : ℕ) (B : PolynomialBranch K) :
    Function.LeftInverse (polynomialBranchInverse a b B)
      (polynomialBranchGradient a b B) := by
  cases B with
  | r P => exact rPolynomialGradientInverse_comp (K := K) a b P
  | s P => exact sPolynomialGradientInverse_comp (K := K) a b P

/-- Every classified polynomial branch has the reverse composition identity. -/
theorem polynomialBranchGradient_comp_inverse
    (a b : ℕ) (B : PolynomialBranch K) :
    Function.RightInverse (polynomialBranchInverse a b B)
      (polynomialBranchGradient a b B) := by
  cases B with
  | r P => exact rPolynomialGradient_comp_inverse (K := K) a b P
  | s P => exact sPolynomialGradient_comp_inverse (K := K) a b P

/-- Every classified polynomial gradient is bijective. -/
theorem polynomialBranchGradient_bijective
    (a b : ℕ) (B : PolynomialBranch K) :
    Function.Bijective (polynomialBranchGradient a b B) := by
  refine ⟨(polynomialBranchInverse_comp_gradient a b B).injective, ?_⟩
  exact (polynomialBranchGradient_comp_inverse a b B).surjective

end CommRing

end HC4.ClassifiedFamilies
