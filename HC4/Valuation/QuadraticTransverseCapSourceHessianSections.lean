import HC4.Valuation.QuadraticTransverseCapSourceHessianSupport
import Mathlib.Tactic

/-!
# Genuine quadratic source: transverse Hessian sections agree

The verified source cap forces all third transverse derivatives to vanish.
The intervening support certificate proves that every nonzero monomial of
each actual transverse Hessian entry involves only longitudinal variable 0.

Consequently restricting the genuine Hessian to any constant transverse
section agrees with its restriction to the marked longitudinal axis.
The proof transports the SAME source polynomial through the two existing
section ring homomorphisms and uses Mathlib's support-sensitive hom
congruence; it does not posit another Hessian family or a chart.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The genuine transverse Hessian entries are independent of the chosen
constant transverse section, as polynomials in the longitudinal variable. -/
theorem transverseCapTwo_sourceHessian_transverseSection_independent
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3)
    (y : Fin 3 → K) :
    quadraticSourceSectionHessian F y i.succ j.succ =
      quadraticSourceSectionHessian F (fun _ => 0) i.succ j.succ := by
  let Q : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.hessian F i.succ j.succ
  let f₁ := quadraticSourceSectionRingHom y
  let f₂ := quadraticSourceSectionRingHom (fun _ : Fin 3 => (0 : K))
  have hvars : ∀ k : Fin 4, k ∈ Q.vars → k = 0 := by
    intro k hk
    cases k using Fin.cases with
    | zero => rfl
    | succ k =>
      exfalso
      obtain ⟨d, hd, hpos⟩ :=
        (MvPolynomial.mem_vars (p := Q) k.succ).mp hk
      have hd0 : d k.succ = 0 :=
        transverseCapTwo_sourceHessian_support_longitudinal
          F hbound i j d hd k
      exact (Finsupp.mem_support_iff.mp hpos) hd0
  have hC : f₁.comp (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K) =
      f₂.comp (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K) := by
    apply RingHom.ext
    intro a
    change
      Polynomial.map (MvPolynomial.eval y)
          (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C a)) =
        Polynomial.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))
          (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C a))
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX : f₁ (MvPolynomial.X (0 : Fin 4)) =
      f₂ (MvPolynomial.X (0 : Fin 4)) := by
    change
      Polynomial.map (MvPolynomial.eval y)
          (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X 0)) =
        Polynomial.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))
          (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X 0))
    simp only [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  have hsections : f₁ Q = f₂ Q := by
    exact MvPolynomial.hom_congr_vars hC
      (by
        intro k hk _
        rw [hvars k hk]
        exact hX)
      rfl
  exact hsections

end
end HC4.Valuation
