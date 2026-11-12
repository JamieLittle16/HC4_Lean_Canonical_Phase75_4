import HC4.Valuation.QuadraticFirstLayerPrincipalSchurPivot
import Mathlib.Tactic

/-!
# Algebraic drift endpoints for transverse-quadratic Hessian sources

If the represented source has transverse cap two, the determinant-one
equation takes the form of a 1+3 scalar/transverse Schur identity.
The generic-rank-two and generic-rank-three cases have independent final
algebraic drift obstructions.

These statements do NOT claim that the hypotheses have already been
extracted from the E3 represented source. They isolate genuine
contradictions to be consumed only after the source-honest coefficient and
kernel arguments have been formalised.
-/

namespace HC4.Valuation

noncomputable section

universe u

/-- A polynomial square factor in a unit equation has to be a nonzero
constant.  The proof works over any field, without algebraic closure. -/
theorem polynomial_squareFactor_unit_constant
    {K : Type u} [Field K]
    (gamma v : Polynomial K)
    (hunit : -(gamma * v * v) = 1) :
    ∃ c : K, c ≠ 0 ∧ v = Polynomial.C c := by
  have hvunit : IsUnit v := by
    apply isUnit_iff_exists.mpr
    refine ⟨-gamma * v, ?_, ?_⟩
    · calc
        v * (-gamma * v) = -(gamma * v * v) := by ring
        _ = 1 := hunit
    · calc
        (-gamma * v) * v = -(gamma * v * v) := by ring
        _ = 1 := hunit
  obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp hvunit
  refine ⟨c, ?_, hc.symm⟩
  intro hczero
  have hvzero : v = 0 := by
    simpa [hczero] using hc.symm
  rw [hvzero] at hunit
  simp at hunit

/-- A polynomial function with constant nonzero derivative cannot take
the same value at 0 and 1. This is the elementary marked-axis drift step. -/
theorem polynomial_nonzeroConstantDerivative_no_unitIntervalCollision
    {K : Type u} [Field K] [CharZero K]
    (b : Polynomial K)
    (c : K)
    (hc : c ≠ 0)
    (hder : Polynomial.derivative b = Polynomial.C c)
    (hcoll : Polynomial.eval (1 : K) b =
      Polynomial.eval (0 : K) b) :
    False := by
  have hzero :
      Polynomial.derivative (b - Polynomial.C c * Polynomial.X) = 0 := by
    simp [hder]
  have hconstant :=
    Polynomial.eq_C_of_derivative_eq_zero hzero
  have heq :
      Polynomial.eval (1 : K) (b - Polynomial.C c * Polynomial.X) =
        Polynomial.eval (0 : K) (b - Polynomial.C c * Polynomial.X) := by
    rw [hconstant]
    simp
  have heval :
      Polynomial.eval (1 : K) b - c =
        Polynomial.eval (0 : K) b := by
    simpa using heq
  have hczero : c = 0 := by
    linear_combination hcoll - heval
  exact hc hczero

/-- The full generic-rank-two scalar drift contradiction, once the
source's one-dimensional constant kernel and adjugate factor have been
extracted. The hypotheses are polynomial identities, not generic rank
labels or a new final-resolution assumption. -/
theorem transverseQuadratic_rankTwo_constantKernelDrift_impossible
    {K : Type u} [Field K] [CharZero K]
    (gamma b : Polynomial K)
    (hdet : -(gamma * Polynomial.derivative b *
      Polynomial.derivative b) = 1)
    (hcoll : Polynomial.eval (1 : K) b =
      Polynomial.eval (0 : K) b) :
    False := by
  obtain ⟨c, hc, hder⟩ :=
    polynomial_squareFactor_unit_constant gamma
      (Polynomial.derivative b) hdet
  exact polynomial_nonzeroConstantDerivative_no_unitIntervalCollision
    b c hc hder hcoll

/-- The nilpotent-polynomial drift factor occurring in the generic-rank-three
case has the concrete two-sided inverse `1+N`. This identity works even in
a noncommutative ring (e.g. a ring of 3x3 matrices). -/
theorem cubicNilpotent_drift_twoSidedInverse
    {R : Type*} [Ring R]
    (N : R)
    (hN : N ^ 3 = 0) :
    (1 - N + N ^ 2) * (1 + N) = 1 ∧
      (1 + N) * (1 - N + N ^ 2) = 1 := by
  constructor
  · calc
      (1 - N + N ^ 2) * (1 + N) = 1 + N ^ 3 := by noncomm_ring
      _ = 1 := by rw [hN]; simp
  · calc
      (1 + N) * (1 - N + N ^ 2) = 1 + N ^ 3 := by noncomm_ring
      _ = 1 := by rw [hN]; simp

/-- No nonzero matrix/vector-valued drift can be annihilated by the
rank-three unipotent interval factor. The arbitrary ring form works with
any matrix coefficient module represented by a multiplication action. -/
theorem cubicNilpotent_drift_mul_eq_zero_iff
    {R : Type*} [Ring R]
    (N v : R)
    (hN : N ^ 3 = 0) :
    (1 - N + N ^ 2) * v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hinv := (cubicNilpotent_drift_twoSidedInverse N hN).2
    calc
      v = ((1 + N) * (1 - N + N ^ 2)) * v := by rw [hinv]; simp
      _ = (1 + N) * ((1 - N + N ^ 2) * v) := by rw [mul_assoc]
      _ = 0 := by rw [hv]; simp
  · intro hv
    simp [hv]

/-- In the generic rank-three case, the interval drift operator is
injective on *any* left module carrying the nilpotent transverse
operator, not only on a 3x3 matrix ring. This is the exact linear-algebra
consumer for the later coefficient transport from b'(x). -/
theorem cubicNilpotent_drift_smul_injective
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (N : R)
    (hN : N ^ 3 = 0) :
    Function.Injective (fun v : M => (1 - N + N ^ 2) • v) := by
  intro v w hvw
  have hleft :=
    (cubicNilpotent_drift_twoSidedInverse N hN).2
  have h := congrArg (fun z : M => (1 + N) • z) hvw
  simpa only [← mul_smul, hleft, one_smul] using h

/-- In particular, vanishing of the polynomial interval drift forces
vanishing of the source's initial transverse derivative vector. -/
theorem cubicNilpotent_drift_smul_eq_zero_iff
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (N : R)
    (hN : N ^ 3 = 0)
    (v : M) :
    (1 - N + N ^ 2) • v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    exact (cubicNilpotent_drift_smul_injective N hN)
      (by simpa using hv)
  · intro hv
    simp [hv]

end

end HC4.Valuation
