import HC4.Valuation.QuadraticTransverseCapSourceSections
import HC4.Newton.TerminalTwoZeroSupport
import HC4.Newton.TerminalOneZeroAmbientDecoupling
import Mathlib.Tactic

/-!
# Whole-source transverse-degree-two Hessian is constant across sections

This is a direct application of the honest (0,1,1,1)-weight cap on
the REPRESENTED determinant-one source, not just on a quadratic
associated-graded layer.

Each transverse derivative decreases the weight cap by one.
Thus two transverse derivatives of a cap-two source have weight
zero, and any third transverse derivative is zero. Characteristic
zero then makes every transverse Hessian entry independent of ALL
transverse variables, with x₀ left genuinely free.

Consequently the actual transverse 3x3 Hessian at every constant
section y is the same polynomial matrix C(x₀) as on the axis.
The mixed-block affine-in-y identity is a separate next step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Differentiation in one transverse source variable lowers the
original represented-source transverse-weight cap by exactly one. -/
theorem quadraticTransverseCap_pderiv_succ
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight (n + 1) F)
    (j : Fin 3) :
    HasReverseWeightBound topKernelMarkedAxisNatWeight n
      (MvPolynomial.pderiv j.succ F) := by
  intro m hm
  have hne :
      MvPolynomial.coeff m (MvPolynomial.pderiv j.succ F) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [coeff_pderiv_mixedDegree] at hne
  have hsource :
      MvPolynomial.coeff
        (m + Finsupp.single j.succ 1) F ≠ 0 := by
    intro hz
    simp [hz] at hne
  have hle := hbound
    (m + Finsupp.single j.succ 1)
    (MvPolynomial.mem_support_iff.mpr hsource)
  rw [weight_topKernelMarkedAxisNatWeight] at hle ⊢
  fin_cases j <;>
    simp [Finsupp.add_apply, Finsupp.single_apply] at hle <;>
    omega

/-- Cap zero means that all three transverse coordinates are absent
from the support. Each transverse partial derivative therefore vanishes. -/
theorem quadraticTransverseCap_zero_pderiv_succ
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 0 F)
    (j : Fin 3) :
    MvPolynomial.pderiv j.succ F = 0 := by
  apply HC4.Newton.pderiv_eq_zero_of_all_supported_exponents_zero
    j.succ F
  intro m hm
  have hle := hbound m (MvPolynomial.mem_support_iff.mpr hm)
  rw [weight_topKernelMarkedAxisNatWeight] at hle
  fin_cases j <;> omega

/-- The entire third transverse derivative of the honest
quadratic-cap represented source vanishes, for all three transverse
indices, in any order. -/
theorem quadraticTransverseCap_two_tripleTransversePderiv_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j k : Fin 3) :
    MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ F)) = 0 := by
  have hfirst : HasReverseWeightBound topKernelMarkedAxisNatWeight 1
      (MvPolynomial.pderiv i.succ F) :=
    quadraticTransverseCap_pderiv_succ F 1 hbound i
  have hsecond : HasReverseWeightBound topKernelMarkedAxisNatWeight 0
      (MvPolynomial.pderiv j.succ (MvPolynomial.pderiv i.succ F)) :=
    quadraticTransverseCap_pderiv_succ
      (MvPolynomial.pderiv i.succ F) 0 hfirst j
  exact quadraticTransverseCap_zero_pderiv_succ
    (MvPolynomial.pderiv j.succ (MvPolynomial.pderiv i.succ F))
    hsecond k

/-- An auxiliary multivariate polynomial with zero transverse
partials has the same values along all transverse sections at each
fixed longitudinal point. This uses genuine coordinatewise evaluation
equality, rather than an unproved formal series argument. -/
theorem quadraticTransverse_source_eval_section_eq_axis
    [CharZero K]
    (P : MvPolynomial (Fin 4) K)
    (hzero : ∀ i : Fin 3, MvPolynomial.pderiv i.succ P = 0)
    (x : K)
    (y : Fin 3 → K) :
    MvPolynomial.eval (Fin.cons x y) P =
      MvPolynomial.eval (Fin.cons x (fun _ : Fin 3 => (0 : K))) P := by
  let p0 : Fin 4 → K := Fin.cons x y
  let p1 : Fin 4 → K := Fin.cons x ![0, y 1, y 2]
  let p2 : Fin 4 → K := Fin.cons x ![0, 0, y 2]
  let p3 : Fin 4 → K := Fin.cons x ![0, 0, 0]
  have h01 : MvPolynomial.eval p0 P = MvPolynomial.eval p1 P := by
    apply HC4.Newton.eval_eq_of_pderiv_eq_zero
      (1 : Fin 4) P (hzero 0) p0 p1
    intro i hi
    fin_cases i <;> simp [p0, p1] at *
  have h12 : MvPolynomial.eval p1 P = MvPolynomial.eval p2 P := by
    apply HC4.Newton.eval_eq_of_pderiv_eq_zero
      (2 : Fin 4) P (hzero 1) p1 p2
    intro i hi
    fin_cases i <;> simp [p1, p2] at *
  have h23 : MvPolynomial.eval p2 P = MvPolynomial.eval p3 P := by
    apply HC4.Newton.eval_eq_of_pderiv_eq_zero
      (3 : Fin 4) P (hzero 2) p2 p3
    intro i hi
    fin_cases i <;> simp [p2, p3] at *
  have hp3 :
      p3 = Fin.cons x (fun _ : Fin 3 => (0 : K)) := by
    funext i
    fin_cases i <;> rfl
  calc
    MvPolynomial.eval (Fin.cons x y) P =
        MvPolynomial.eval p0 P := rfl
    _ = MvPolynomial.eval p1 P := h01
    _ = MvPolynomial.eval p2 P := h12
    _ = MvPolynomial.eval p3 P := h23
    _ = MvPolynomial.eval (Fin.cons x
        (fun _ : Fin 3 => (0 : K))) P := by rw [hp3]

/-- Section ring-hom evaluation is exactly ordinary evaluation
at (x,y), leaving the longitudinal variable as the outer polynomial. -/
theorem quadraticTransverseSourceSectionRingHom_eval
    (F : MvPolynomial (Fin 4) K)
    (x : K)
    (y : Fin 3 → K) :
    Polynomial.eval x (quadraticTransverseSourceSectionRingHom y F) =
      MvPolynomial.eval (Fin.cons x y) F := by
  rw [MvPolynomial.eval_eq_eval_mv_eval']
  rfl

/-- The ACTUAL transverse Hessian of a cap-two source is identical on
every constant transverse section and on the distinguished source axis.
The equality is in K[x₀], not merely after evaluating x₀ at zero. -/
theorem quadraticTransverseCap_two_sectionHessian_succ_succ
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3)
    (y : Fin 3 → K) :
    quadraticTransverseSourceSectionRingHom y
        (HC4.Polynomial.hessian F i.succ j.succ) =
      longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F i.succ j.succ) := by
  let P := HC4.Polynomial.hessian F i.succ j.succ
  have hzero : ∀ k : Fin 3, MvPolynomial.pderiv k.succ P = 0 := by
    intro k
    exact quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hbound i j k
  rw [← quadraticTransverseSourceSectionRingHom_zero]
  apply Polynomial.funext
  intro x
  rw [quadraticTransverseSourceSectionRingHom_eval,
      quadraticTransverseSourceSectionRingHom_eval]
  exact quadraticTransverse_source_eval_section_eq_axis P hzero x y

end

end HC4.Valuation
