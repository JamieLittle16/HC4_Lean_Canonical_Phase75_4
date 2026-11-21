import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# A marked collision forces drift of a singular transverse axis block

Let the Hessian on the marked axis have determinant one and block form
`[[a, b'ᵀ], [b', C]]` over `K[X]`. If `det C = 0`, its adjugate supplies
a polynomial kernel vector `n` with `C n = 0` and `b' · n = 1`.
The marked equality `b(0) = b(1)` forces `C' n ≠ 0`.
No rational function field, constant-rank specialization, or bound on
transverse degree is assumed.
-/

namespace HC4.Valuation.TransverseAxis

open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K]

private abbrev R (K : Type*) [Field K] := Polynomial K

/-- Symmetric block presentation with coordinate zero longitudinal. Symmetry
of the transverse block is not needed for the kernel drift argument. -/
def axisBlock (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) :
    Matrix (Fin 4) (Fin 4) (R K) :=
  Matrix.of (Fin.cons (Fin.cons a d) fun i => Fin.cons (d i) (C i))

@[simp] lemma axisBlock_zero_zero
    (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) :
    axisBlock a d C 0 0 = a := rfl

@[simp] lemma axisBlock_zero_succ
    (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) (j : Fin 3) :
    axisBlock a d C 0 j.succ = d j := rfl

@[simp] lemma axisBlock_succ_zero
    (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) (i : Fin 3) :
    axisBlock a d C i.succ 0 = d i := rfl

@[simp] lemma axisBlock_succ_succ
    (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) (i j : Fin 3) :
    axisBlock a d C i.succ j.succ = C i j := rfl

@[simp] lemma axisBlock_zero (K : Type*) [Field K] :
    axisBlock (K := K) 0 0 0 = 0 := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp

private lemma adjugate_axisBlock_zero
    (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) :
    (axisBlock a d C).adjugate 0 0 = C.det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub :
      (axisBlock a d C).submatrix Fin.succ Fin.succ = C := by
    ext i j
    simp [Matrix.submatrix_apply]
  simp [hsub]

/-- The canonical polynomial transverse kernel vector furnished by the
longitudinal column of the adjugate. -/
def kernelColumn (a : R K) (d : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K)) :
    Fin 3 → R K :=
  fun i => (axisBlock a d C).adjugate i.succ 0

private lemma axisBlock_mulVec_cons_zero (a : R K) (d : Fin 3 → R K)
    (C : Matrix (Fin 3) (Fin 3) (R K)) (v : Fin 3 → R K) :
    axisBlock a d C *ᵥ (Fin.cons 0 v) = Fin.cons (d ⬝ᵥ v) (C *ᵥ v) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | succ i =>
    simp only [Matrix.mulVec, dotProduct, Fin.cons_succ]
    rw [Fin.sum_univ_succ]
    simp

/-- The adjugate column simultaneously gives a transverse kernel vector
and pairs to one with the longitudinal mixed row. -/
theorem kernelColumn_spec (a : R K) (d : Fin 3 → R K)
    (C : Matrix (Fin 3) (Fin 3) (R K))
    (hA : (axisBlock a d C).det = 1) (hC : C.det = 0) :
    C *ᵥ kernelColumn a d C = 0 ∧ d ⬝ᵥ kernelColumn a d C = 1 := by
  let A := axisBlock a d C
  let n := kernelColumn a d C
  let e : Fin 4 → R K := Fin.cons 1 0
  have hcol : A *ᵥ (Fin.cons 0 n) = e := by
    have hmul : A * A.adjugate = 1 := by
      rw [Matrix.mul_adjugate, hA, one_smul]
    have hc : (fun i => A.adjugate i 0) = Fin.cons 0 n := by
      apply funext
      intro i
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        change (axisBlock a d C).adjugate 0 0 = 0
        rw [adjugate_axisBlock_zero, hC]
      | succ i => rfl
    apply funext
    intro i
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) (R K) => M i 0) hmul
    change (∑ j, A i j * A.adjugate j 0) = (1 : Matrix (Fin 4) (Fin 4) (R K)) i 0 at hi
    have h1 : (1 : Matrix (Fin 4) (Fin 4) (R K)) i 0 = e i := by
      cases i using Fin.cases with
      | zero => simp [e]
      | succ i => simp [e]
    rw [h1] at hi
    change (A *ᵥ (fun j => A.adjugate j 0)) i = _ at hi
    simpa only [hc] using hi
  rw [axisBlock_mulVec_cons_zero] at hcol
  constructor
  · apply funext
    intro j
    exact congrFun hcol j.succ
  · exact congrFun hcol 0

private lemma kernel_eq_zero (a : R K) (d : Fin 3 → R K)
    (C : Matrix (Fin 3) (Fin 3) (R K)) (hA : (axisBlock a d C).det = 1)
    (v : Fin 3 → R K) (hCv : C *ᵥ v = 0) (hdv : d ⬝ᵥ v = 0) : v = 0 := by
  let A := axisBlock a d C
  have h1 : A.adjugate * A = 1 := by
    rw [Matrix.adjugate_mul, hA, one_smul]
  have hv : A *ᵥ Fin.cons 0 v = 0 := by
    change axisBlock a d C *ᵥ Fin.cons 0 v = 0
    rw [axisBlock_mulVec_cons_zero, hCv, hdv]
    funext i
    cases i using Fin.cases <;> rfl
  have hz := congrArg (fun z => A.adjugate *ᵥ z) hv
  change A.adjugate *ᵥ (A *ᵥ Fin.cons 0 v) = A.adjugate *ᵥ 0 at hz
  rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] at hz
  apply funext
  intro j
  exact congrFun hz j.succ

private lemma derivative_dotProduct (u v : Fin 3 → R K) :
    Polynomial.derivative (u ⬝ᵥ v) =
      (fun i => Polynomial.derivative (u i)) ⬝ᵥ v +
        u ⬝ᵥ (fun i => Polynomial.derivative (v i)) := by
  simp [dotProduct, Polynomial.derivative_mul, Finset.sum_add_distrib]

/-- The drift of a symmetric block has zero self-pairing on its kernel.
This is the differentiated identity `nᵀ C n = 0`. -/
theorem kernel_drift_selfPairing_eq_zero
    (C : Matrix (Fin 3) (Fin 3) (R K)) (n : Fin 3 → R K)
    (hS : Cᵀ = C) (hn : C *ᵥ n = 0) :
    n ⬝ᵥ ((C.map Polynomial.derivative) *ᵥ n) = 0 := by
  let nd := fun i => Polynomial.derivative (n i)
  have hD : (C.map Polynomial.derivative) *ᵥ n + C *ᵥ nd = 0 := by
    apply funext
    intro i
    have h := congrArg Polynomial.derivative (congrFun hn i)
    change Polynomial.derivative (C i ⬝ᵥ n) = Polynomial.derivative 0 at h
    rw [derivative_dotProduct, Polynomial.derivative_zero] at h
    exact h
  have htail : n ⬝ᵥ (C *ᵥ nd) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, hn, zero_dotProduct]
  have h := congrArg (fun v => n ⬝ᵥ v) hD
  change n ⬝ᵥ ((C.map Polynomial.derivative) *ᵥ n + C *ᵥ nd) = n ⬝ᵥ 0 at h
  simpa only [dotProduct_add, htail, add_zero, dotProduct_zero] using h

private lemma derivative_eq_mul_self_forces_zero
    {p c : R K} (hp : p ≠ 0) (h : Polynomial.derivative p = c * p) : c = 0 := by
  by_contra hc
  have hn : p.natDegree ≠ 0 := by
    intro hz
    exact mul_ne_zero hc hp (h.symm.trans (Polynomial.derivative_of_natDegree_zero hz))
  have hdeg := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_mul hc hp] at hdeg
  have hl := Polynomial.natDegree_derivative_lt hn
  omega

/-- If the transverse axis block is singular, the normalized kernel column
cannot be annihilated by the longitudinal derivative of that block when
the transverse gradients agree at the two marked points. -/
theorem derivative_mulVec_kernelColumn_ne_zero_of_marked
    [CharZero K]
    (a : R K) (b : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K))
    (hA : (axisBlock a (fun i => Polynomial.derivative (b i)) C).det = 1)
    (hC : C.det = 0)
    (hmarked : ∀ i, (b i).eval 0 = (b i).eval 1) :
    let d := fun i => Polynomial.derivative (b i)
    (C.map Polynomial.derivative) *ᵥ kernelColumn a d C ≠ 0 := by
  dsimp only
  intro hstatic
  let d := fun i => Polynomial.derivative (b i)
  let n := kernelColumn a d C
  let nd := fun i => Polynomial.derivative (n i)
  let c := d ⬝ᵥ nd
  obtain ⟨hCn, hdn⟩ := kernelColumn_spec a d C hA hC
  change d ⬝ᵥ n = 1 at hdn
  change C.map Polynomial.derivative *ᵥ n = 0 at hstatic
  have hCnd : C *ᵥ nd = 0 := by
    apply funext
    intro i
    have h := congrArg Polynomial.derivative (congrFun hCn i)
    change Polynomial.derivative (C i ⬝ᵥ n) = Polynomial.derivative 0 at h
    rw [derivative_dotProduct, Polynomial.derivative_zero] at h
    have hs := congrFun hstatic i
    change (fun j => Polynomial.derivative (C i j)) ⬝ᵥ n = 0 at hs
    rw [hs, zero_add] at h
    exact h
  have hnd : nd = c • n := by
    apply sub_eq_zero.mp
    apply kernel_eq_zero a d C hA
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hCn, hCnd, smul_zero, sub_zero]
    · rw [dotProduct_sub, dotProduct_smul, hdn, smul_eq_mul, mul_one]
      exact sub_self c
  have hn : ∃ i, n i ≠ 0 := by
    by_contra! hn
    have he : n = 0 := funext hn
    rw [he, dotProduct_zero] at hdn
    exact zero_ne_one hdn
  obtain ⟨i, hi⟩ := hn
  have hc : c = 0 :=
    derivative_eq_mul_self_forces_zero hi (congrFun hnd i)
  rw [hc, zero_smul] at hnd
  let p := b ⬝ᵥ n
  have hdp : Polynomial.derivative p = 1 := by
    dsimp [p]
    rw [derivative_dotProduct]
    change d ⬝ᵥ n + b ⬝ᵥ nd = 1
    rw [hnd, dotProduct_zero, add_zero, hdn]
  have hconst := Polynomial.eq_C_of_derivative_eq_zero
    (f := p - Polynomial.X) (by simp [hdp])
  have heq : p.eval 0 = p.eval 1 := by
    have hnconst (j : Fin 3) : n j = Polynomial.C ((n j).coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero (congrFun hnd j)
    simp only [p, dotProduct, Polynomial.eval_finset_sum, Polynomial.eval_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [show Polynomial.eval 0 (b j) = Polynomial.eval 1 (b j) from hmarked j,
      hnconst j]
    simp
  have h0 := congrArg (Polynomial.eval 0) hconst
  have h1 := congrArg (Polynomial.eval 1) hconst
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_zero] at h0 h1
  rw [← h0, heq] at h1
  exact one_ne_zero (by linear_combination -h1)

/-- On a singular transverse block the longitudinal-longitudinal entry of
the perturbation drops out of the determinant variation. The mixed entries
pair twice with the normalized kernel column. -/
theorem trace_axisBlock_singular
    (a a₁ : R K) (d u : Fin 3 → R K) (C B : Matrix (Fin 3) (Fin 3) (R K))
    (hC : C.det = 0) (hS : Cᵀ = C) :
    ((axisBlock a d C).adjugate * axisBlock a₁ u B).trace =
      2 * (u ⬝ᵥ kernelColumn a d C) +
        ((axisBlock a d C).adjugate * axisBlock 0 0 B).trace := by
  let A := axisBlock a d C
  have hA : Aᵀ = A := by
    apply Matrix.ext
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [A]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (R K) => M _ _) hS
  have hAdj : A.adjugateᵀ = A.adjugate := by rw [Matrix.adjugate_transpose, hA]
  have hzero : A.adjugate 0 0 = 0 := by
    change (axisBlock a d C).adjugate 0 0 = 0
    rw [adjugate_axisBlock_zero, hC]
  have hdecomp : axisBlock a₁ u B = axisBlock a₁ u 0 + axisBlock 0 0 B := by
    apply Matrix.ext
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp
  rw [hdecomp, Matrix.mul_add, Matrix.trace_add]
  congr 1
  change (A.adjugate * axisBlock a₁ u 0).trace = 2 * (u ⬝ᵥ kernelColumn a d C)
  have hr (j : Fin 3) : A.adjugate 0 j.succ = kernelColumn a d C j :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) (R K) => M j.succ 0) hAdj
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    axisBlock_zero_zero, axisBlock_zero_succ, axisBlock_succ_zero, axisBlock_succ_succ,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hzero, zero_mul, zero_add,
    hr, dotProduct]
  change (∑ j : Fin 3, kernelColumn a d C j * u j) +
      (∑ j : Fin 3, kernelColumn a d C j * u j) = 2 * ∑ j : Fin 3, u j * kernelColumn a d C j
  simp_rw [mul_comm (kernelColumn a d C _)]
  ring

/-- In the singular-axis branch, determinant-one first jets and a marked
collision force a nonzero transverse cubic correction. The matrices
`B j` are the transverse-transverse blocks of the first jets. -/
theorem exists_nonzero_cubic_trace_of_singular_axis
    [CharZero K]
    (a : R K) (b : Fin 3 → R K) (C : Matrix (Fin 3) (Fin 3) (R K))
    (a₁ : Fin 3 → R K) (B : Fin 3 → Matrix (Fin 3) (Fin 3) (R K))
    (hA : (axisBlock a (fun i => Polynomial.derivative (b i)) C).det = 1)
    (hC : C.det = 0) (hS : Cᵀ = C)
    (hmarked : ∀ i, (b i).eval 0 = (b i).eval 1)
    (hjets : ∀ j, ((axisBlock a (fun i => Polynomial.derivative (b i)) C).adjugate *
      axisBlock (a₁ j) (fun i => Polynomial.derivative (C j i)) (B j)).trace = 0) :
    ∃ j, ((axisBlock a (fun i => Polynomial.derivative (b i)) C).adjugate *
      axisBlock 0 0 (B j)).trace ≠ 0 := by
  by_contra! h
  apply derivative_mulVec_kernelColumn_ne_zero_of_marked a b C hA hC hmarked
  apply funext
  intro j
  have hj := hjets j
  rw [trace_axisBlock_singular _ _ _ _ _ _ hC hS, h j, add_zero] at hj
  exact (mul_eq_zero.mp hj).resolve_left (by norm_num)

end

end HC4.Valuation.TransverseAxis
