import HC4.Valuation.QuadraticTransverseCapSchurDriftEndpoints
import Mathlib.Tactic

/-!
# Rank-two transverse quadratic source: unimodular kernel drift

For a transverse-cap-two represented source, the determinant-one equation
on the longitudinal axis makes the polynomial kernel vector

  w(x) = adj(C(x)) b'(x)

unimodular: w·b' = -1 when det(C)=0. The coefficients linear in the
transverse variables force C' w = 0. Combining with C w = 0 and generic
transverse rank two implies w and w' are pointwise parallel; equivalently,
all their 2x2 wedges vanish.

The main theorem below shows that these exact *polynomial* consequences are
already incompatible with b(0)=b(1). There is no division by a variable,
no arbitrary rank promotion, and no new terminal endpoint assumption.
The subsequent source adapter must still prove the displayed consequences
from the actual four-variable Hessian and its transverse-weight cap.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A unimodular polynomial vector whose formal derivative is parallel
to itself has identically zero derivative. The factor of proportionality
is automatically polynomial: it is extracted from the unimodularity
certificate, not postulated from a fraction field.

For the next source adapter, `w` is `adj(C)b'` and the kernel-wedge
condition follows from generic transverse rank two. -/
omit [CharZero K] in
theorem polynomial_unimodularKernel_derivative_eq_zero
    (w v : Fin 3 → Polynomial K)
    (hpair : (∑ i : Fin 3, w i * v i) = -1)
    (hwedge : ∀ i j : Fin 3,
      w i * Polynomial.derivative (w j) =
        w j * Polynomial.derivative (w i)) :
    ∀ j : Fin 3, Polynomial.derivative (w j) = 0 := by
  let s : Polynomial K :=
    ∑ i : Fin 3, v i * Polynomial.derivative (w i)
  have hsum (j : Fin 3) :
      (∑ i : Fin 3, w i * v i) *
          Polynomial.derivative (w j) = s * w j := by
    dsimp [s]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      w i * v i * Polynomial.derivative (w j) =
          v i * (w i * Polynomial.derivative (w j)) := by ring
      _ = v i * (w j * Polynomial.derivative (w i)) := by
          rw [hwedge i j]
      _ = v i * Polynomial.derivative (w i) * w j := by ring
  intro j
  have hparallel :
      Polynomial.derivative (w j) = (-s) * w j := by
    calc
      Polynomial.derivative (w j) =
          -((∑ i : Fin 3, w i * v i) *
            Polynomial.derivative (w j)) := by
              rw [hpair]
              ring
      _ = -(s * w j) := by rw [hsum j]
      _ = (-s) * w j := by ring
  have hdiv : w j ∣ Polynomial.derivative (w j) := by
    refine ⟨-s, ?_⟩
    simpa only [mul_comm] using hparallel
  exact Polynomial.dvd_derivative_iff.mp hdiv

/-- The whole generic-rank-two quadratic-axis endpoint, expressed as
explicit polynomial coefficient consequences of the source determinant:
w·b'=-1, w∧w'=0, and the *actual* marked collision b(1)=b(0).

Unlike an arbitrary abstract rank-two witness, these conditions are
contradictory. The adapter from the source Hessian to w is still open. -/
theorem polynomial_unimodularKernel_markedDrift_impossible
    (w b : Fin 3 → Polynomial K)
    (hpair :
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) = -1)
    (hwedge : ∀ i j : Fin 3,
      w i * Polynomial.derivative (w j) =
        w j * Polynomial.derivative (w i))
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    False := by
  have hwd : ∀ i : Fin 3, Polynomial.derivative (w i) = 0 :=
    polynomial_unimodularKernel_derivative_eq_zero
      w (fun i => Polynomial.derivative (b i)) hpair hwedge
  have hwconst (i : Fin 3) :
      w i = Polynomial.C ((w i).coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero (hwd i)
  let B : Polynomial K := ∑ i : Fin 3, w i * b i
  have hBder :
      Polynomial.derivative B = -1 := by
    calc
      Polynomial.derivative B =
          ∑ i : Fin 3, Polynomial.derivative (w i * b i) := by
            dsimp [B]
            rw [map_sum]
      _ = ∑ i : Fin 3, w i * Polynomial.derivative (b i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Polynomial.derivative_mul, hwd i]
            simp
      _ = -1 := hpair
  have hBcoll :
      Polynomial.eval (1 : K) B =
        Polynomial.eval (0 : K) B := by
    calc
      Polynomial.eval (1 : K) B =
          ∑ i : Fin 3,
            Polynomial.eval (1 : K) (w i * b i) := by
              simp only [B, Polynomial.eval_finset_sum]
      _ = ∑ i : Fin 3,
            Polynomial.eval (0 : K) (w i * b i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Polynomial.eval_mul, Polynomial.eval_mul, hwconst i]
              simp [hcoll i]
      _ = Polynomial.eval (0 : K) B := by
            simp only [B, Polynomial.eval_finset_sum]
  have hBder' :
      Polynomial.derivative B = Polynomial.C (-1 : K) := by
    simpa using hBder
  exact polynomial_nonzeroConstantDerivative_no_unitIntervalCollision
    B (-1 : K) (by norm_num) hBder' hBcoll

end

end HC4.Valuation
