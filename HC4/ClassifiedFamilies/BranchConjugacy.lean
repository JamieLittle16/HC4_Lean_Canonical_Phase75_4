import HC4.ClassifiedFamilies.TriangularInverse

/-!
# Conjugacy of the two classified gradient families

Reversing the four affine coordinates exchanges the `r` and `s` invariants.
The same reversal conjugates the two triangular gradient maps and their
explicit inverses.  This records formally that the two final families are one
family viewed through the coordinate-reversal symmetry.
-/

namespace HC4.ClassifiedFamilies

/-- Reverse the four affine coordinates. -/
def reversePoint {K : Type*} (x : Point4 K) : Point4 K :=
  ⟨x.x4, x.x3, x.x2, x.x1⟩

@[simp] theorem reversePoint_involutive
    {K : Type*} (x : Point4 K) :
    reversePoint (reversePoint x) = x := by
  ext <;> rfl

/-- Coordinate reversal as an equivalence of affine four-space. -/
def reversePointEquiv (K : Type*) : Point4 K ≃ Point4 K where
  toFun := reversePoint
  invFun := reversePoint
  left_inv := reversePoint_involutive
  right_inv := reversePoint_involutive

section CommRing

variable {K : Type*} [CommRing K]

@[simp] theorem rValue_reversePoint (a b : ℕ) (x : Point4 K) :
    rValue a b (reversePoint x) = sValue a b x := by
  simp [rValue, sValue, reversePoint, mul_comm]

@[simp] theorem sValue_reversePoint (a b : ℕ) (x : Point4 K) :
    sValue a b (reversePoint x) = rValue a b x := by
  simp [rValue, sValue, reversePoint, mul_comm]

/-- Coordinate reversal conjugates the `r` gradient map to the `s` gradient map. -/
theorem reverse_rGradientMap_reverse
    (a b : ℕ) (dP : K → K) (x : Point4 K) :
    reversePoint (rGradientMap a b dP (reversePoint x)) =
      sGradientMap a b dP x := by
  ext <;>
    simp [reversePoint, rGradientMap, sGradientMap, rValue, sValue, mul_comm] <;>
    ring

/-- Coordinate reversal conjugates the `s` gradient map to the `r` gradient map. -/
theorem reverse_sGradientMap_reverse
    (a b : ℕ) (dP : K → K) (x : Point4 K) :
    reversePoint (sGradientMap a b dP (reversePoint x)) =
      rGradientMap a b dP x := by
  ext <;>
    simp [reversePoint, rGradientMap, sGradientMap, rValue, sValue, mul_comm] <;>
    ring

/-- The explicit branch inverses are conjugate by the same reversal. -/
theorem reverse_rGradientInverse_reverse
    (a b : ℕ) (dP : K → K) (x : Point4 K) :
    reversePoint (rGradientInverse a b dP (reversePoint x)) =
      sGradientInverse a b dP x := by
  ext <;>
    simp [reversePoint, rGradientInverse, sGradientInverse, mul_comm] <;>
    ring

/-- The converse inverse conjugacy. -/
theorem reverse_sGradientInverse_reverse
    (a b : ℕ) (dP : K → K) (x : Point4 K) :
    reversePoint (sGradientInverse a b dP (reversePoint x)) =
      rGradientInverse a b dP x := by
  ext <;>
    simp [reversePoint, rGradientInverse, sGradientInverse, mul_comm] <;>
    ring

/-- The `r` gradient map packaged as an equivalence. -/
def rGradientEquiv (a b : ℕ) (dP : K → K) : Point4 K ≃ Point4 K where
  toFun := rGradientMap a b dP
  invFun := rGradientInverse a b dP
  left_inv := rGradientInverse_comp_map a b dP
  right_inv := rGradientMap_comp_inverse a b dP

/-- The `s` gradient map packaged as an equivalence. -/
def sGradientEquiv (a b : ℕ) (dP : K → K) : Point4 K ≃ Point4 K where
  toFun := sGradientMap a b dP
  invFun := sGradientInverse a b dP
  left_inv := sGradientInverse_comp_map a b dP
  right_inv := sGradientMap_comp_inverse a b dP

/-- Functional form of the branch conjugacy. -/
theorem sGradientMap_eq_reverse_conjugate
    (a b : ℕ) (dP : K → K) :
    sGradientMap a b dP =
      fun x => reversePoint (rGradientMap a b dP (reversePoint x)) := by
  funext x
  exact (reverse_rGradientMap_reverse a b dP x).symm

end CommRing

end HC4.ClassifiedFamilies
