import HC4.Newton.TerminalOneZeroAmbientDecoupling
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-!
# Standard one-zero terminal endpoint

Phases 93.35--93.37 already prove:

* equality of gradients recovers the unique zero-weight coordinate `X₀`;
* every fixed `X₀` fibre in coordinates `2,3` is a planar Keller map and
  is injective under `JC₂`;
* gradient coordinates `2,3` ignore `X₁`;
* once `X₀,X₂,X₃` agree, gradient coordinate `0` recovers `X₁`.

The only missing standard-coordinate bridge is evaluation of the specialised
planar fibre.

This file closes that bridge and then assembles the full standard `k=1`
terminal endpoint.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/- Keep the standard one-zero endpoint isolated from the two-zero shorthand
simp aliases. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- The ambient point represented by a fixed zero-coordinate `c` and a
planar fibre point `u=(X₂,X₃)`, with the irrelevant coordinate `X₁` set
to zero. -/
def oneZeroFibrePoint
    (c : K)
    (u : HC4.Point2 K) :
    Fin 4 -> K
  | 0 => c
  | 1 => 0
  | 2 => u 0
  | 3 => u 1

/-- The planar point extracted from ambient coordinates `2,3`. -/
def standardOneZeroPlanarPoint
    (p : Fin 4 -> K) :
    HC4.Point2 K
  | 0 => p 2
  | 1 => p 3

@[simp] theorem standardOneZeroPlanarPoint_zero
    (p : Fin 4 -> K) :
    standardOneZeroPlanarPoint p 0 = p 2 := rfl

@[simp] theorem standardOneZeroPlanarPoint_one
    (p : Fin 4 -> K) :
    standardOneZeroPlanarPoint p 1 = p 3 := rfl

/-- Evaluating a fibre-specialised polynomial at `u` is exactly ambient
evaluation at `(c,0,u₀,u₁)`.

The proof is the universal property of multivariate polynomial evaluation:
compose the fibre substitution with evaluation at `u`, push through the
renaming, and inspect the four ambient variables. -/
theorem eval_oneZeroFibreSpecialise
    (c : K)
    (u : HC4.Point2 K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval u
        (oneZeroFibreSpecialise c P) =
      MvPolynomial.eval
        (oneZeroFibrePoint c u) P := by
  change
    (MvPolynomial.aeval u)
        (oneZeroFibreSpecialise c P) =
      (MvPolynomial.aeval
        (oneZeroFibrePoint c u)) P
  unfold oneZeroFibreSpecialise
  rw [MvPolynomial.comp_aeval_apply]
  rw [MvPolynomial.aeval_rename]
  have hhom :
      (MvPolynomial.aeval
          (((fun i =>
              (MvPolynomial.aeval u)
                (Sum.elim
                  MvPolynomial.X
                  (fun j =>
                    MvPolynomial.C
                      (oneZeroFrozenParameter c j))
                  i)) ∘
            oneZeroSplitIndex)) :
        MvPolynomial (Fin 4) K →ₐ[K] K) =
      (MvPolynomial.aeval
          (oneZeroFibrePoint c u) :
        MvPolynomial (Fin 4) K →ₐ[K] K) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [oneZeroSplitIndex,
        oneZeroFrozenParameter,
        oneZeroFibrePoint]
  exact
    congrArg
      (fun φ : MvPolynomial (Fin 4) K →ₐ[K] K =>
        φ P)
      hhom

/-- The first component of the planar fibre gradient is ambient gradient
coordinate `2` at the corresponding point with `X₁=0`. -/
theorem standardOneZeroFibreGradient_eval_zero
    (c : K)
    (u : HC4.Point2 K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.planarPolynomialMapEval
        (standardOneZeroFibreGradientMap c F) u 0 =
      mvGradientMap F
        (oneZeroFibrePoint c u) 2 := by
  unfold HC4.planarPolynomialMapEval
  unfold standardOneZeroFibreGradientMap
  rw [pderiv_zero_oneZeroFibreSpecialise]
  exact
    eval_oneZeroFibreSpecialise
      c u (MvPolynomial.pderiv 2 F)

/-- The second component of the planar fibre gradient is ambient gradient
coordinate `3` at the corresponding point with `X₁=0`. -/
theorem standardOneZeroFibreGradient_eval_one
    (c : K)
    (u : HC4.Point2 K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.planarPolynomialMapEval
        (standardOneZeroFibreGradientMap c F) u 1 =
      mvGradientMap F
        (oneZeroFibrePoint c u) 3 := by
  unfold HC4.planarPolynomialMapEval
  unfold standardOneZeroFibreGradientMap
  rw [pderiv_one_oneZeroFibreSpecialise]
  exact
    eval_oneZeroFibreSpecialise
      c u (MvPolynomial.pderiv 3 F)

/-- The fibre point built from an ambient point agrees with that point
away from coordinate `1`. -/
theorem oneZeroFibrePoint_planarPoint_eq_off_one
    (p : Fin 4 -> K) :
    ∀ j : Fin 4,
      j ≠ 1 ->
        oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint p) j =
          p j := by
  intro j hj
  fin_cases j
  · rfl
  · exact (hj rfl).elim
  · rfl
  · rfl

/-- If two ambient points have the same zero-coordinate, the fibre point
formed from the second point using the first point's zero-coordinate still
agrees with the second point away from coordinate `1`. -/
theorem oneZeroFibrePoint_planarPoint_eq_off_one_of_zero_eq
    {p q : Fin 4 -> K}
    (h0 : p 0 = q 0) :
    ∀ j : Fin 4,
      j ≠ 1 ->
        oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint q) j =
          q j := by
  intro j hj
  fin_cases j
  · exact h0
  · exact (hj rfl).elim
  · rfl
  · rfl

/-- Equal ambient gradients induce equal values of the common planar
one-zero fibre map once Phase 93.35 has recovered `X₀`. -/
theorem standardOneZero_equal_gradient_gives_equal_fibre_gradient
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (hgrad :
      mvGradientMap F p =
        mvGradientMap F q) :
    HC4.planarPolynomialMapEval
        (standardOneZeroFibreGradientMap (p 0) F)
        (standardOneZeroPlanarPoint p) =
      HC4.planarPolynomialMapEval
        (standardOneZeroFibreGradientMap (p 0) F)
        (standardOneZeroPlanarPoint q) := by
  have h0 :
      p 0 = q 0 :=
    standardOneZero_gradient_eq_recovers_zero
      ha had hhom hMA hgrad
  have hp2 :
      mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint p)) 2 =
        mvGradientMap F p 2 := by
    symm
    exact
      standardOneZero_gradient_two_eq_of_eq_off_one
        ha had hhom
        p
        (oneZeroFibrePoint
          (p 0)
          (standardOneZeroPlanarPoint p))
        (fun j hj =>
          (oneZeroFibrePoint_planarPoint_eq_off_one p j hj).symm)
  have hp3 :
      mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint p)) 3 =
        mvGradientMap F p 3 := by
    symm
    exact
      standardOneZero_gradient_three_eq_of_eq_off_one
        ha had hhom
        p
        (oneZeroFibrePoint
          (p 0)
          (standardOneZeroPlanarPoint p))
        (fun j hj =>
          (oneZeroFibrePoint_planarPoint_eq_off_one p j hj).symm)
  have hq2 :
      mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint q)) 2 =
        mvGradientMap F q 2 := by
    symm
    exact
      standardOneZero_gradient_two_eq_of_eq_off_one
        ha had hhom
        q
        (oneZeroFibrePoint
          (p 0)
          (standardOneZeroPlanarPoint q))
        (fun j hj =>
          (oneZeroFibrePoint_planarPoint_eq_off_one_of_zero_eq
            h0 j hj).symm)
  have hq3 :
      mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint q)) 3 =
        mvGradientMap F q 3 := by
    symm
    exact
      standardOneZero_gradient_three_eq_of_eq_off_one
        ha had hhom
        q
        (oneZeroFibrePoint
          (p 0)
          (standardOneZeroPlanarPoint q))
        (fun j hj =>
          (oneZeroFibrePoint_planarPoint_eq_off_one_of_zero_eq
            h0 j hj).symm)
  funext i
  fin_cases i
  · calc
      HC4.planarPolynomialMapEval
          (standardOneZeroFibreGradientMap (p 0) F)
          (standardOneZeroPlanarPoint p) 0 =
        mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint p)) 2 :=
              standardOneZeroFibreGradient_eval_zero
                (p 0) (standardOneZeroPlanarPoint p) F
      _ = mvGradientMap F p 2 := hp2
      _ = mvGradientMap F q 2 := congrFun hgrad 2
      _ =
        mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint q)) 2 := hq2.symm
      _ =
        HC4.planarPolynomialMapEval
          (standardOneZeroFibreGradientMap (p 0) F)
          (standardOneZeroPlanarPoint q) 0 :=
              (standardOneZeroFibreGradient_eval_zero
                (p 0) (standardOneZeroPlanarPoint q) F).symm
  · calc
      HC4.planarPolynomialMapEval
          (standardOneZeroFibreGradientMap (p 0) F)
          (standardOneZeroPlanarPoint p) 1 =
        mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint p)) 3 :=
              standardOneZeroFibreGradient_eval_one
                (p 0) (standardOneZeroPlanarPoint p) F
      _ = mvGradientMap F p 3 := hp3
      _ = mvGradientMap F q 3 := congrFun hgrad 3
      _ =
        mvGradientMap F
          (oneZeroFibrePoint
            (p 0)
            (standardOneZeroPlanarPoint q)) 3 := hq3.symm
      _ =
        HC4.planarPolynomialMapEval
          (standardOneZeroFibreGradientMap (p 0) F)
          (standardOneZeroPlanarPoint q) 1 :=
              (standardOneZeroFibreGradient_eval_one
                (p 0) (standardOneZeroPlanarPoint q) F).symm

/-- Under `JC₂`, equal gradients in the standard one-zero terminal branch
recover the two interior coordinates `2,3`. -/
theorem standardOneZero_equal_gradient_recovers_transverse_of_JC2
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (hgrad :
      mvGradientMap F p =
        mvGradientMap F q) :
    p 2 = q 2 ∧ p 3 = q 3 := by
  have hfibreEq :=
    standardOneZero_equal_gradient_gives_equal_fibre_gradient
      ha had hhom hMA hgrad
  have hinj :=
    standardOneZeroFibreGradientMap_injective_of_JC2
      hJC2 ha had hhom hMA (p 0)
  have huv :
      standardOneZeroPlanarPoint p =
        standardOneZeroPlanarPoint q :=
    hinj hfibreEq
  constructor
  · exact congrFun huv 0
  · exact congrFun huv 1

/-- **Standard one-zero terminal endpoint.**

Assuming the planar Jacobian-conjecture injectivity interface, the gradient
map of every standard one-zero Monge--Ampère terminal face is injective. -/
theorem standardOneZero_terminal_gradient_injective_of_JC2
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    Function.Injective (mvGradientMap F) := by
  intro p q hgrad
  have h0 :
      p 0 = q 0 :=
    standardOneZero_gradient_eq_recovers_zero
      ha had hhom hMA hgrad
  rcases
      standardOneZero_equal_gradient_recovers_transverse_of_JC2
        hJC2 ha had hhom hMA hgrad with
    ⟨h2, h3⟩
  have h1 :
      p 1 = q 1 :=
    standardOneZero_gradient_zero_recovers_one
      ha had hhom hMA
      h0 h2 h3
      (congrFun hgrad 0)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Hence an exact gradient collision is impossible in the standard
one-zero terminal branch under `JC₂`. -/
theorem standardOneZero_terminal_collision_impossible_of_JC2
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (hpq : p ≠ q)
    (hcollision :
      mvGradientMap F p =
        mvGradientMap F q) :
    False := by
  exact
    hpq
      (standardOneZero_terminal_gradient_injective_of_JC2
        hJC2 ha had hhom hMA hcollision)

end

end HC4.Newton
