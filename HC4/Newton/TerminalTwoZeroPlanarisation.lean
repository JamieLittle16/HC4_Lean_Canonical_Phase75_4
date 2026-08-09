import HC4.Newton.TerminalTwoZeroEndpointInterface
import HC4.PlanarJC2Interface
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-!
# Planarisation of the two-zero terminal coefficients

Phase 93.28 proves that on the standard two-zero terminal face

    F = X₂ A + X₃ C

and that `A,C` depend only on variables `0,1`.

This file turns that support statement into an actual pair of polynomials
in `MvPolynomial (Fin 2) K`.

The inclusion

    Fin 2 ↪ Fin 4,   0 ↦ 0, 1 ↦ 1

is used with Mathlib's
`MvPolynomial.exists_rename_eq_of_vars_subset_range`.

Thus the terminal coefficient pair is not merely "morally planar":
there are honest planar polynomials whose renames are exactly `A` and `C`.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Standard inclusion of the two zero-weight variables into `Fin 4`. -/
def standardZeroPairEmbedding : Fin 2 ↪ Fin 4 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact
      congrArg
        (fun x : Fin 4 => x.val)
        hij

@[simp] theorem standardZeroPairEmbedding_zero :
    standardZeroPairEmbedding (0 : Fin 2) = (0 : Fin 4) := rfl

@[simp] theorem standardZeroPairEmbedding_one :
    standardZeroPairEmbedding (1 : Fin 2) = (1 : Fin 4) := rfl

/-- Support-level dependence only on `X₀,X₁` implies that every variable in
`vars P` lies in the range of the standard planar inclusion. -/
theorem dependsOnlyOnStandardZeroPair_vars_subset_range
    {P : MvPolynomial (Fin 4) K}
    (hdep : DependsOnlyOnStandardZeroPair P) :
    (↑P.vars : Set (Fin 4)) ⊆
      Set.range standardZeroPairEmbedding := by
  intro i hi
  change i ∈ P.vars at hi
  rw [MvPolynomial.mem_vars i] at hi
  rcases hi with ⟨m, hm, him⟩
  have hmcoeff :
      MvPolynomial.coeff m P ≠ 0 := by
    simpa [MvPolynomial.coeff] using
      (Finsupp.mem_support_iff.mp hm)
  have hz := hdep m hmcoeff
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · have hmi : m 2 ≠ 0 :=
      Finsupp.mem_support_iff.mp him
    exact (hmi hz.1).elim
  · have hmi : m 3 ≠ 0 :=
      Finsupp.mem_support_iff.mp him
    exact (hmi hz.2).elim

/-- An ambient polynomial supported only in the standard zero pair is the
rename of an honest planar polynomial. -/
theorem dependsOnlyOnStandardZeroPair_exists_planarisation
    {P : MvPolynomial (Fin 4) K}
    (hdep : DependsOnlyOnStandardZeroPair P) :
    ∃ Q : MvPolynomial (Fin 2) K,
      MvPolynomial.rename standardZeroPairEmbedding Q = P := by
  exact
    MvPolynomial.exists_rename_eq_of_vars_subset_range
      P
      standardZeroPairEmbedding
      standardZeroPairEmbedding.injective
      (dependsOnlyOnStandardZeroPair_vars_subset_range hdep)

/-- The planar map with coordinate polynomials `A,C`. -/
def standardPlanarPairMap
    (A C : MvPolynomial (Fin 2) K) :
    HC4.PlanarPolynomialMap K
  | 0 => A
  | 1 => C

@[simp] theorem standardPlanarPairMap_zero
    (A C : MvPolynomial (Fin 2) K) :
    standardPlanarPairMap A C 0 = A := rfl

@[simp] theorem standardPlanarPairMap_one
    (A C : MvPolynomial (Fin 2) K) :
    standardPlanarPairMap A C 1 = C := rfl

/-- Exact planarisation data for the two ambient coefficient polynomials. -/
def HasStandardTwoZeroPlanarPair
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∃ A C : MvPolynomial (Fin 2) K,
    MvPolynomial.rename standardZeroPairEmbedding A =
        standardTwoZeroA F ∧
    MvPolynomial.rename standardZeroPairEmbedding C =
        standardTwoZeroC F

/-- Every ambient doubling form supplies honest planar coefficient
polynomials. -/
theorem standardTwoZeroDoublingForm_hasPlanarPair
    {F : MvPolynomial (Fin 4) K}
    (hform : HasStandardTwoZeroDoublingForm F) :
    HasStandardTwoZeroPlanarPair F := by
  rcases
      dependsOnlyOnStandardZeroPair_exists_planarisation
        hform.2.1 with
    ⟨A, hA⟩
  rcases
      dependsOnlyOnStandardZeroPair_exists_planarisation
        hform.2.2 with
    ⟨C, hC⟩
  exact ⟨A, C, hA, hC⟩

/-- Join a planar base point and a planar fibre point into the standard
four-coordinate point. -/
def standardJoinPoint
    (uv : HC4.Point2 K × HC4.Point2 K) :
    Fin 4 -> K
  | 0 => uv.1 0
  | 1 => uv.1 1
  | 2 => uv.2 0
  | 3 => uv.2 1

/-- Renaming a planar polynomial along the standard inclusion and evaluating
at a joined point is exactly planar evaluation at the base point. -/
theorem eval_rename_standardZeroPair
    (P : MvPolynomial (Fin 2) K)
    (u v : HC4.Point2 K) :
    MvPolynomial.eval
        (standardJoinPoint (u, v))
        (MvPolynomial.rename
          standardZeroPairEmbedding P) =
      MvPolynomial.eval u P := by
  have hassign :
      standardJoinPoint (u, v) ∘
          standardZeroPairEmbedding = u := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.eval_rename]
  rw [hassign]

end

end HC4.Newton
