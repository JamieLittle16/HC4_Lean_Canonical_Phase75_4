import HC4.Polynomial.DerivativeWeight
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The rank-one power of a nonzero nilpotent transverse velocity

In dimension three, the last nonzero power of a nilpotent operator is
square-zero and has rank one. Its outer-product factors give the fixed
direction and invariant linear form without choosing a Jordan basis.
-/

namespace HC4.Polynomial.RankThreeCubic
open MvPolynomial
open scoped BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K]

private theorem outerProduct_of_square_zero
    (T : Matrix (Fin 3) (Fin 3) K) (hT : T ≠ 0) (h2 : T * T = 0) :
    ∃ d l : Fin 3 → K, d ≠ 0 ∧ l ≠ 0 ∧ T = Matrix.vecMulVec d l := by
  classical
  let f := T.toLin'
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rw [LinearMap.range_le_ker_iff]
    change T.toLin'.comp T.toLin' = 0
    rw [← Matrix.toLin'_mul, h2, map_zero]
  have hh := LinearMap.finrank_range_add_finrank_ker f
  have hf : Module.finrank K (Fin 3 → K) = 3 := by simp
  rw [hf] at hh
  have hle' := Submodule.finrank_mono hle
  have hne : Module.finrank K (LinearMap.range f) ≠ 0 := by
    intro he
    have hbot := Submodule.finrank_eq_zero.mp he
    apply hT
    apply Matrix.toLin'.injective
    change f = (0 : Matrix (Fin 3) (Fin 3) K).toLin'
    rw [LinearMap.range_eq_bot.mp hbot, map_zero]
  have hfr : Module.finrank K (LinearMap.range f) = 1 := by omega
  obtain ⟨D, hD, hs⟩ := finrank_eq_one_iff'.mp hfr
  let d : Fin 3 → K := D
  have hd : d ≠ 0 := fun h => hD (Subtype.ext h)
  have hc (j : Fin 3) : T.col j ∈ LinearMap.range f := by
    refine ⟨Pi.single j 1, ?_⟩
    change T *ᵥ Pi.single j 1 = T.col j
    rw [Matrix.mulVec_single_one]
  choose l hl using fun j : Fin 3 => hs ⟨T.col j, hc j⟩
  have hfac : T = Matrix.vecMulVec d l := by
    ext i j
    have h := congrArg (fun x : LinearMap.range f => (x : Fin 3 → K) i) (hl j)
    change l j * d i = T i j at h
    simpa [Matrix.vecMulVec, mul_comm] using h.symm
  refine ⟨d, l, hd, ?_, hfac⟩
  intro he
  apply hT
  simp [hfac, he]

/-- In dimension three, a nontrivial nilpotent direction admits a
rank-one power with a fixed vector and an invariant covector. -/
theorem exists_nilpotent_rankOnePower
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ≠ 0) (h3 : N ^ 3 = 0) :
    ∃ (r : ℕ) (d l : Fin 3 → K),
      (r = 1 ∨ r = 2) ∧ d ≠ 0 ∧ l ≠ 0 ∧ N ^ r = Matrix.vecMulVec d l ∧
      N *ᵥ d = 0 ∧ l ᵥ* N = 0 := by
  classical
  let r := if N ^ 2 = 0 then 1 else 2
  let T := N ^ r
  have hr : r = 1 ∨ r = 2 := by dsimp [r]; split <;> simp
  have hT : T ≠ 0 := by
    dsimp [T, r]
    split
    · simpa using hN
    · assumption
  have hNT : N * T = 0 := by
    dsimp [T, r]
    split
    · simpa [pow_two] using ‹N ^ 2 = 0›
    · simpa [pow_succ', pow_two] using h3
  have hTN : T * N = 0 := by
    dsimp [T]
    rwa [← pow_succ, pow_succ']
  have h2 : T * T = 0 := by
    rcases hr with he | he
    · simpa [T, he] using hNT
    · change N ^ r * T = 0
      rw [he, pow_two, mul_assoc, hNT, mul_zero]
  obtain ⟨d, l, hd, hl, hfac⟩ := outerProduct_of_square_zero T hT h2
  refine ⟨r, d, l, hr, hd, hl, hfac, ?_, ?_⟩
  · rw [hfac, Matrix.mul_vecMulVec] at hNT
    obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by contrapose! hl; exact funext hl
    funext i
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hNT
    exact (mul_eq_zero.mp h).resolve_right hj
  · rw [hfac, Matrix.vecMulVec_mul] at hTN
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by contrapose! hd; exact funext hd
    funext j
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hTN
    exact (mul_eq_zero.mp h).resolve_left hi

section SquareExtraction

/-- A directional derivative with constant vector of coefficients. -/
def constantDirectional {ι : Type*} [Fintype ι] (d : ι → K)
    (q : MvPolynomial ι K) : MvPolynomial ι K :=
  ∑ i, MvPolynomial.C (d i) * pderiv i q

/-- The linear form associated to a covector. -/
def constantLinearForm {ι : Type*} [Fintype ι] (l : ι → K) : MvPolynomial ι K :=
  ∑ i, MvPolynomial.C (l i) * X i

theorem pderiv_constantLinearForm {ι : Type*} [Fintype ι] (l : ι → K) (j : ι) :
    pderiv j (constantLinearForm l) = MvPolynomial.C (l j) := by
  classical
  simp only [constantLinearForm, map_sum, pderiv_C_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [pderiv_X_of_ne hi]
  · simp

private theorem pderiv_directional_eq_hessian_mulVec
    (d : Fin 3 → K) (q : MvPolynomial (Fin 3) K) (j : Fin 3) :
    pderiv j (constantDirectional d q) = (hessian q *ᵥ (fun i => MvPolynomial.C (d i))) j := by
  simp only [constantDirectional, map_sum, pderiv_C_mul, Matrix.mulVec, dotProduct, hessian_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [HC4.Newton.pderiv_comm_backport j i, mul_comm]

/-- If a nonzero rank-one velocity is self-adjoint against the
reference Hessian, its direction differentiates the cubic to a
nonzero constant multiple of the covector squared. -/
theorem reference_directional_eq_square_of_rankOne [CharZero K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    (hdet : (hessian q).det ≠ 0)
    (d l : Fin 3 → K) (hd : d ≠ 0) (hl : l ≠ 0)
    (hs : let T := hessian q *
        Matrix.vecMulVec (fun i => MvPolynomial.C (d i)) (fun i => MvPolynomial.C (l i))
      ∀ i j, T i j = T j i) :
    ∃ c : K, c ≠ 0 ∧ constantDirectional d q = MvPolynomial.C c * constantLinearForm l ^ 2 := by
  classical
  let P := constantDirectional d q
  let E := constantLinearForm l
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by contrapose! hl; exact funext hl
  let a : MvPolynomial (Fin 3) K := MvPolynomial.C (l j)
  have ha : a ≠ 0 := MvPolynomial.C_ne_zero.mpr hj
  have hdeg : P.IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    exact (hq.pderiv (i := i)).C_mul (d i)
  have hh (i) : a * pderiv i P = MvPolynomial.C (l i) * pderiv j P := by
    have h := hs i j
    rw [Matrix.mul_vecMulVec] at h
    simpa [Matrix.vecMulVec, P, a, pderiv_directional_eq_hessian_mulVec, mul_comm] using h
  have hE : a * (2 * P) = E * pderiv j P := by
    have heuler := hdeg.sum_X_mul_pderiv
    rw [nsmul_eq_mul] at heuler
    have heuler' : (∑ i : Fin 3, X i * pderiv i P) = 2 * P := by simpa using heuler
    dsimp only [E]
    rw [← heuler', Finset.mul_sum, constantLinearForm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      a * (X i * pderiv i P) = X i * (a * pderiv i P) := by ring
      _ = _ := by rw [hh]; ring
  have h1 : a * pderiv j P = E * pderiv j (pderiv j P) := by
    have h := congrArg (pderiv j) hE
    change pderiv j (a * (2 * P)) = pderiv j (E * pderiv j P) at h
    have h2 : pderiv j (2 : MvPolynomial (Fin 3) K) = 0 := by
      rw [show (2 : MvPolynomial (Fin 3) K) = 1 + 1 by norm_num, map_add, pderiv_one, add_zero]
    have ha0 : pderiv j a = 0 := pderiv_C
    have hdE : pderiv j E = a := pderiv_constantLinearForm l j
    simp only [Derivation.leibniz, smul_eq_mul, ha0, h2, mul_zero, add_zero, hdE] at h
    linear_combination h
  have hfinal : (2 * a ^ 2) * P = E ^ 2 * pderiv j (pderiv j P) := by
    linear_combination a * hE + E * h1
  have hbdeg : (pderiv j (pderiv j P)).IsHomogeneous 0 := (hdeg.pderiv (i := j)).pderiv (i := j)
  let b := MvPolynomial.coeff 0 (pderiv j (pderiv j P))
  have hb : pderiv j (pderiv j P) = MvPolynomial.C b :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hbdeg)
  rw [hb] at hfinal
  have hden : 2 * l j ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ hj)
  let c := b / (2 * l j ^ 2)
  have hsq : P = MvPolynomial.C c * E ^ 2 := by
    apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hden)
    have he : (MvPolynomial.C (2 * l j ^ 2) : MvPolynomial (Fin 3) K) = 2 * a ^ 2 := by
      rw [map_mul, map_pow]
      rfl
    rw [he, hfinal, ← he, ← mul_assoc, ← map_mul]
    rw [show (2 * l j ^ 2) * c = b by dsimp [c]; rw [mul_comm, div_mul_cancel₀ _ hden]]
    ring
  have hc : c ≠ 0 := by
    intro hc0
    have hzero : P = 0 := by simp [hsq, hc0]
    let M := hessian q
    let D : Fin 3 → MvPolynomial (Fin 3) K := fun i => MvPolynomial.C (d i)
    have hker : M *ᵥ D = 0 := by
      funext i
      change (hessian q *ᵥ D) i = 0
      rw [← pderiv_directional_eq_hessian_mulVec, show constantDirectional d q = P from rfl,
        hzero, map_zero]
    have hh : M.det • D = 0 := by
      rw [← Matrix.one_mulVec D, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul,
        ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
    apply hd
    funext i
    have he := congrFun hh i
    change M.det * MvPolynomial.C (d i) = 0 at he
    exact MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hdet)
  exact ⟨c, hc, hsq⟩

end SquareExtraction

end
end HC4.Polynomial.RankThreeCubic
