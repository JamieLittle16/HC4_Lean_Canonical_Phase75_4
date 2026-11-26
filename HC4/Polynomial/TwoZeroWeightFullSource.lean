module

public import HC4.Polynomial.PositiveWeightZeroClock
public import HC4.Newton.TerminalTwoZeroPlanarCollision

/-!
# Full-source two-zero terminal under planar JC2

At the cap d for weights (0,0,d,d), d>0, the maximal layer
is an exact doubling potential and the strictly lower remainder
depends only on the zero-weight coordinates. Its contribution
to the gradient cancels as soon as the planar base points agree.

Unlike the homogeneous terminal endpoint, this consumes the
full determinant-one source and its original gradient collision.
-/

public section

namespace HC4.Polynomial

open MvPolynomial
open HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private theorem twoZero_weight_formula (d : ℤ) (u : Fin 4 →₀ ℕ) :
    Finsupp.weight (standardTwoZeroTerminalWeight d) u =
      ((u 2 : ℤ) + (u 3 : ℤ)) * d := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [Fin.sum_univ_four, standardTwoZeroTerminalWeight, nsmul_eq_mul]
    <;> ring
  · intro i
    simp

/-- The lower part is planar support, not merely a formal error term. -/
theorem twoZero_strictWeight_dependsOnly
    (d : ℤ) (hd : 0 < d) (Q : MvPolynomial (Fin 4) K)
    (hQ : IsWeightLT (standardTwoZeroTerminalWeight d) d Q) :
    DependsOnlyOnStandardZeroPair Q := by
  intro u hu
  have h := hQ (MvPolynomial.mem_support_iff.mpr hu)
  rw [twoZero_weight_formula] at h
  have hn : (u 2 : ℤ) + (u 3 : ℤ) < 1 := by
    by_contra! hn
    have hnonneg := mul_nonneg (sub_nonneg.mpr hn) hd.le
    nlinarith only [h, hnonneg]
  constructor <;> omega

/-- All evaluations of a base-supported polynomial coincide at
points with the same standard base. -/
theorem twoZero_eval_eq_of_base_eq
    (Q : MvPolynomial (Fin 4) K)
    (hQ : DependsOnlyOnStandardZeroPair Q)
    (p q : Fin 4 → K) (hpq : standardBasePoint p = standardBasePoint q) :
    MvPolynomial.eval p Q = MvPolynomial.eval q Q := by
  obtain ⟨D, hD⟩ := dependsOnlyOnStandardZeroPair_exists_planarisation hQ
  rw [← hD, eval_rename_standardZeroPair_at, eval_rename_standardZeroPair_at, hpq]

set_option maxHeartbeats 4000000 in
/-- The full cap-two-zero source is injective under planar JC2.
No homogeneity hypothesis on the full source is required. -/
theorem gradient_injective_of_twoZeroWeight_cap
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (d : ℤ) (hd : 0 < d) (P : MvPolynomial (Fin 4) K)
    (hcap : IsWeightLE (standardTwoZeroTerminalWeight d) d P)
    (hdet : hessianDeterminant P = 1) :
    Function.Injective (mvGradientMap P) := by
  classical
  let w := standardTwoZeroTerminalWeight d
  let L := initialForm w d P
  let R := P - L
  have hR : IsWeightLT w d R := sub_initialForm_isWeightLT hcap
  have hRdep : DependsOnlyOnStandardZeroPair R := twoZero_strictWeight_dependsOnly d hd R hR
  have hR2 : pderiv 2 R = 0 :=
    pderiv_eq_zero_of_all_supported_exponents_zero 2 R (fun u hu => (hRdep u hu).1)
  have hR3 : pderiv 3 R = 0 :=
    pderiv_eq_zero_of_all_supported_exponents_zero 3 R (fun u hu => (hRdep u hu).2)
  have hdec : P = L + R := by dsimp [R]; ring
  have hder (i : Fin 4) : pderiv i P = pderiv i L + pderiv i R := by
    calc
      pderiv i P = pderiv i (L + R) := congrArg (pderiv i) hdec
      _ = pderiv i L + pderiv i R := map_add _ _ _
  have hclock : (Fintype.card (Fin 4) : ℤ) * d - 2 * (∑ i : Fin 4, w i) = 0 := by
    simp [w, Fin.sum_univ_four] <;> ring
  have hLdet : HC4.MongeAmpere.IsPolynomialMongeAmpere L := by
    change hessianDeterminant (initialForm w d P) = 1
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w d P hcap,
      hclock, hdet]
    exact initialForm_eq_self_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_one K w)
  have hLhom : IsIntegralWeightedHomogeneous w d L := by
    intro u hu
    have h := initialForm_isWeightedHomogeneous w d P hu
    change Finsupp.weight (standardTwoZeroTerminalWeight d) u = d at h
    rw [twoZero_weight_formula] at h
    change integralWeightedDegree (standardTwoZeroTerminalWeight d) u = d
    rw [integralWeightedDegree_standardTwoZero]
    exact h
  obtain ⟨A, C, hA, hC, hKeller⟩ :=
    standardTwoZero_mongeAmpere_hasPlanarKellerModel hd hLhom hLdet
  intro p q hpq
  have hpos (x : Fin 4 → K) :
      standardFibrePoint (mvGradientMap P x) = standardFibrePoint (mvGradientMap L x) := by
    funext i
    fin_cases i
    · change MvPolynomial.eval x (pderiv 2 P) = MvPolynomial.eval x (pderiv 2 L)
      rw [hder, hR2, add_zero]
    · change MvPolynomial.eval x (pderiv 3 P) = MvPolynomial.eval x (pderiv 3 L)
      rw [hder, hR3, add_zero]
  have hbase : standardBasePoint p = standardBasePoint q := by
    apply hJC2 (standardPlanarPairMap A C) hKeller
    have he := congrArg standardFibrePoint hpq
    rw [hpos p, hpos q, standardTwoZero_gradient_positive_eq_planar hA hC p,
      standardTwoZero_gradient_positive_eq_planar hA hC q] at he
    exact he
  have hRgrad (i : Fin 4) : DependsOnlyOnStandardZeroPair (pderiv i R) := by
    intro u hu
    constructor
    · apply HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero 2 (pderiv i R) _ u hu
      rw [HC4.Newton.pderiv_comm_backport 2 i R, hR2, map_zero]
    · apply HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero 3 (pderiv i R) _ u hu
      rw [HC4.Newton.pderiv_comm_backport 3 i R, hR3, map_zero]
  have hcoll : HasExactGradientCollision L p q := by
    intro i
    have he := congrFun hpq i
    change MvPolynomial.eval p (pderiv i P) = MvPolynomial.eval q (pderiv i P) at he
    simp only [hder, map_add] at he
    rw [twoZero_eval_eq_of_base_eq _ (hRgrad i) p q hbase] at he
    exact add_right_cancel he
  by_contra hn
  exact (standardTwoZero_terminal_not_planarJC2 hd hLhom hLdet p q hn hcoll) hJC2

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_injective_of_twoZeroWeight_cap
