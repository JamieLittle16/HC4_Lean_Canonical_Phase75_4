import HC4.Newton.TerminalOneZeroTransverseConstant
import HC4.PlanarJC2Interface
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-!
# Planar Keller fibres of the standard one-zero terminal face

Reindex the four ambient variables as

    fibre parameters :  X₂, X₃   -> Sum.inl 0, Sum.inl 1
    frozen parameters:  X₀, X₁   -> Sum.inr 0, Sum.inr 1.

For a scalar `c`, specialise

    X₀ = c,
    X₁ = 0,

while retaining `X₂,X₃` as honest planar variables.

Mathlib's `MvPolynomial.aeval_sumElim_pderiv_inl` says that partial
differentiation in a retained `Sum.inl` variable commutes with this
specialisation.  Consequently the planar Jacobian determinant of the
specialised fibre gradient is exactly the specialisation of the ambient
transverse determinant `Δ₂₃`.

Phase 93.36's constant-transverse theorem therefore gives a nonzero
constant planar Jacobian on every fibre.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/- Keep the one-zero calculation isolated from the two-zero shorthand
simp aliases. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- Reindex ambient variables so that the retained planar variables
`X₂,X₃` form the left summand. -/
def oneZeroSplitIndex :
    Fin 4 -> (Fin 2 ⊕ Fin 2)
  | 0 => Sum.inr 0
  | 1 => Sum.inr 1
  | 2 => Sum.inl 0
  | 3 => Sum.inl 1

@[simp] theorem oneZeroSplitIndex_zero :
    oneZeroSplitIndex (0 : Fin 4) =
      Sum.inr (0 : Fin 2) := rfl

@[simp] theorem oneZeroSplitIndex_one :
    oneZeroSplitIndex (1 : Fin 4) =
      Sum.inr (1 : Fin 2) := rfl

@[simp] theorem oneZeroSplitIndex_two :
    oneZeroSplitIndex (2 : Fin 4) =
      Sum.inl (0 : Fin 2) := rfl

@[simp] theorem oneZeroSplitIndex_three :
    oneZeroSplitIndex (3 : Fin 4) =
      Sum.inl (1 : Fin 2) := rfl

theorem oneZeroSplitIndex_injective :
    Function.Injective oneZeroSplitIndex := by
  intro i j hij
  fin_cases i <;>
    fin_cases j <;>
    simp [oneZeroSplitIndex] at hij ⊢

/-- Values assigned to the frozen right-summand variables:
`X₀=c`, `X₁=0`. -/
def oneZeroFrozenParameter
    (c : K) : Fin 2 -> K
  | 0 => c
  | 1 => 0

/-- Specialise a four-variable polynomial to the planar fibre
`X₀=c, X₁=0`, retaining `X₂,X₃` as the two planar variables. -/
def oneZeroFibreSpecialise
    (c : K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval
    (Sum.elim
      MvPolynomial.X
      (fun j =>
        MvPolynomial.C
          (oneZeroFrozenParameter c j)))
    (MvPolynomial.rename
      oneZeroSplitIndex P)

/-- Differentiation in the first planar variable is ambient
differentiation in coordinate `2`, followed by fibre specialisation. -/
theorem pderiv_zero_oneZeroFibreSpecialise
    (c : K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 0
        (oneZeroFibreSpecialise c P) =
      oneZeroFibreSpecialise c
        (MvPolynomial.pderiv 2 P) := by
  have hsum :=
    MvPolynomial.aeval_sumElim_pderiv_inl
      (p := MvPolynomial.rename
        oneZeroSplitIndex P)
      (f := oneZeroFrozenParameter c)
      (j := (0 : Fin 2))
  have hren :
      MvPolynomial.pderiv
          (Sum.inl (0 : Fin 2))
          (MvPolynomial.rename
            oneZeroSplitIndex P) =
        MvPolynomial.rename
          oneZeroSplitIndex
          (MvPolynomial.pderiv 2 P) := by
    simpa [oneZeroSplitIndex] using
      (MvPolynomial.pderiv_rename
        oneZeroSplitIndex_injective
        (2 : Fin 4) P)
  calc
    MvPolynomial.pderiv 0
        (oneZeroFibreSpecialise c P) =
      MvPolynomial.aeval
        (Sum.elim
          MvPolynomial.X
          (fun j =>
            MvPolynomial.C
              (oneZeroFrozenParameter c j)))
        (MvPolynomial.pderiv
          (Sum.inl (0 : Fin 2))
          (MvPolynomial.rename
            oneZeroSplitIndex P)) := by
              simpa [oneZeroFibreSpecialise] using
                hsum.symm
    _ =
      MvPolynomial.aeval
        (Sum.elim
          MvPolynomial.X
          (fun j =>
            MvPolynomial.C
              (oneZeroFrozenParameter c j)))
        (MvPolynomial.rename
          oneZeroSplitIndex
          (MvPolynomial.pderiv 2 P)) := by
            rw [hren]
    _ =
      oneZeroFibreSpecialise c
        (MvPolynomial.pderiv 2 P) := rfl

/-- Differentiation in the second planar variable is ambient
differentiation in coordinate `3`, followed by fibre specialisation. -/
theorem pderiv_one_oneZeroFibreSpecialise
    (c : K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 1
        (oneZeroFibreSpecialise c P) =
      oneZeroFibreSpecialise c
        (MvPolynomial.pderiv 3 P) := by
  have hsum :=
    MvPolynomial.aeval_sumElim_pderiv_inl
      (p := MvPolynomial.rename
        oneZeroSplitIndex P)
      (f := oneZeroFrozenParameter c)
      (j := (1 : Fin 2))
  have hren :
      MvPolynomial.pderiv
          (Sum.inl (1 : Fin 2))
          (MvPolynomial.rename
            oneZeroSplitIndex P) =
        MvPolynomial.rename
          oneZeroSplitIndex
          (MvPolynomial.pderiv 3 P) := by
    simpa [oneZeroSplitIndex] using
      (MvPolynomial.pderiv_rename
        oneZeroSplitIndex_injective
        (3 : Fin 4) P)
  calc
    MvPolynomial.pderiv 1
        (oneZeroFibreSpecialise c P) =
      MvPolynomial.aeval
        (Sum.elim
          MvPolynomial.X
          (fun j =>
            MvPolynomial.C
              (oneZeroFrozenParameter c j)))
        (MvPolynomial.pderiv
          (Sum.inl (1 : Fin 2))
          (MvPolynomial.rename
            oneZeroSplitIndex P)) := by
              simpa [oneZeroFibreSpecialise] using
                hsum.symm
    _ =
      MvPolynomial.aeval
        (Sum.elim
          MvPolynomial.X
          (fun j =>
            MvPolynomial.C
              (oneZeroFrozenParameter c j)))
        (MvPolynomial.rename
          oneZeroSplitIndex
          (MvPolynomial.pderiv 3 P)) := by
            rw [hren]
    _ =
      oneZeroFibreSpecialise c
        (MvPolynomial.pderiv 3 P) := rfl

/-- Planar gradient of the fibre-specialised potential. -/
def standardOneZeroFibreGradientMap
    (c : K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.PlanarPolynomialMap K :=
  fun i =>
    MvPolynomial.pderiv i
      (oneZeroFibreSpecialise c F)

/-- Its planar Jacobian determinant is precisely the fibre specialisation
of the ambient transverse `2,3` Hessian determinant. -/
theorem standardOneZeroFibreGradientMap_jacobian
    (c : K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.planarJacobianDetPolynomial
        (standardOneZeroFibreGradientMap c F) =
      oneZeroFibreSpecialise c
        (standardOneZeroTransverseDet F) := by
  have h22 :
      MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 0
            (oneZeroFibreSpecialise c F)) =
        oneZeroFibreSpecialise c
          (MvPolynomial.pderiv 2
            (MvPolynomial.pderiv 2 F)) := by
    rw [pderiv_zero_oneZeroFibreSpecialise]
    rw [pderiv_zero_oneZeroFibreSpecialise]
  have h33 :
      MvPolynomial.pderiv 1
          (MvPolynomial.pderiv 1
            (oneZeroFibreSpecialise c F)) =
        oneZeroFibreSpecialise c
          (MvPolynomial.pderiv 3
            (MvPolynomial.pderiv 3 F)) := by
    rw [pderiv_one_oneZeroFibreSpecialise]
    rw [pderiv_one_oneZeroFibreSpecialise]
  have h32 :
      MvPolynomial.pderiv 1
          (MvPolynomial.pderiv 0
            (oneZeroFibreSpecialise c F)) =
        oneZeroFibreSpecialise c
          (MvPolynomial.pderiv 3
            (MvPolynomial.pderiv 2 F)) := by
    rw [pderiv_zero_oneZeroFibreSpecialise]
    rw [pderiv_one_oneZeroFibreSpecialise]
  have h23 :
      MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 1
            (oneZeroFibreSpecialise c F)) =
        oneZeroFibreSpecialise c
          (MvPolynomial.pderiv 2
            (MvPolynomial.pderiv 3 F)) := by
    rw [pderiv_one_oneZeroFibreSpecialise]
    rw [pderiv_zero_oneZeroFibreSpecialise]
  unfold HC4.planarJacobianDetPolynomial
  unfold standardOneZeroFibreGradientMap
  rw [h22, h33, h32, h23]
  simp [oneZeroFibreSpecialise,
    standardOneZeroTransverseDet]

/-- Every fixed standard one-zero fibre is a planar Keller map. -/
theorem standardOneZeroFibreGradientMap_hasKeller
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (c : K) :
    HC4.HasNonzeroConstantPlanarJacobian
      (standardOneZeroFibreGradientMap c F) := by
  rcases
      standardOneZero_transverseDet_eq_C_nonzero
        ha had hhom hMA with
    ⟨t, ht, hdet⟩
  refine ⟨t, ht, ?_⟩
  rw [standardOneZeroFibreGradientMap_jacobian]
  rw [hdet]
  simp [oneZeroFibreSpecialise]

/-- Under the planar Jacobian conjecture interface, every fixed
one-zero fibre gradient is injective. -/
theorem standardOneZeroFibreGradientMap_injective_of_JC2
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
    (c : K) :
    Function.Injective
      (HC4.planarPolynomialMapEval
        (standardOneZeroFibreGradientMap c F)) := by
  exact
    HC4.planar_injective_of_JC2
      hJC2
      (standardOneZeroFibreGradientMap c F)
      (standardOneZeroFibreGradientMap_hasKeller
        ha had hhom hMA c)

end

end HC4.Newton
