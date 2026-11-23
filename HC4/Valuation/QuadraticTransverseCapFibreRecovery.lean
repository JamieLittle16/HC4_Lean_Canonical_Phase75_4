import Mathlib.Tactic

/-!
# Exact longitudinal-fibre recovery, with a two-sided inverse

This theorem is the COMPLETE inverse-construction step in the regular
quadratic-transverse-cap argument. It works over an arbitrary field
and in an arbitrary transverse index type.

If the transverse gradient is an invertible affine function of y
for each x, and the longitudinal gradient on each transverse-output
fibre is affine in x with a fixed nonzero slope, then the full
gradient-like map is explicitly bijective.

The *source-to-fibre-slope identity* is a separate, substantive
mathematical obligation. This module does not assume that the
actual Hessian determinant already implies that identity.
-/

namespace HC4.Valuation

noncomputable section

variable {K ι : Type*} [Field K]

/-- An abstract fibrewise-affine gradient shape. In the eventual
application, C(x) is the transverse Hessian of the original source,
b(x) is its transverse gradient at y=0, and h(x,y)=F_x(x,y). -/
def quadraticFibreGradient
    (h : K → (ι → K) → K)
    (b : K → (ι → K))
    (C : K → (ι → K) → (ι → K))
    (z : K × (ι → K)) : K × (ι → K) :=
  (h z.1 z.2, b z.1 + C z.1 z.2)

/-- Inverse using the fixed-fibre longitudinal slope. -/
def quadraticFibreGradientInverse
    (b : K → (ι → K))
    (U : K → (ι → K) → (ι → K))
    (lambda : K)
    (kappa : (ι → K) → K)
    (out : K × (ι → K)) : K × (ι → K) :=
  let x := (out.1 - kappa out.2) * lambda⁻¹
  (x, U x (out.2 - b x))

/-- Fixed-fibre affine longitudinal drift produces an exact
TWO-SIDED inverse, not merely injectivity or a local inverse.

No finiteness requirement is placed on the transverse index type,
since the result is purely fibrewise algebraic. -/
theorem quadraticFibreGradient_bijective_of_affineDrift
    (h : K → (ι → K) → K)
    (b : K → (ι → K))
    (C U : K → (ι → K) → (ι → K))
    (lambda : K) (hlambda : lambda ≠ 0)
    (kappa : (ι → K) → K)
    (hCU : ∀ x z, C x (U x z) = z)
    (hUC : ∀ x z, U x (C x z) = z)
    (hdrift : ∀ x p,
      h x (U x (p - b x)) = lambda * x + kappa p) :
    Function.Bijective (quadraticFibreGradient h b C) := by
  let G := quadraticFibreGradient h b C
  let J := quadraticFibreGradientInverse b U lambda kappa
  have hlambdaMul : lambda * lambda⁻¹ = 1 := mul_inv_cancel₀ hlambda
  have hright : Function.RightInverse J G := by
    intro out
    rcases out with ⟨s, p⟩
    let xx := (s - kappa p) * lambda⁻¹
    have htrans : b xx + C xx (U xx (p - b xx)) = p := by
      rw [hCU]
      abel
    have hlong : h xx (U xx (p - b xx)) = s := by
      rw [hdrift]
      change lambda * ((s - kappa p) * lambda⁻¹) + kappa p = s
      calc
        lambda * ((s - kappa p) * lambda⁻¹) + kappa p =
            (s - kappa p) * (lambda * lambda⁻¹) + kappa p := by ring
        _ = s := by rw [hlambdaMul]; ring
    exact Prod.ext hlong htrans
  have hleft : Function.LeftInverse J G := by
    intro inp
    rcases inp with ⟨x, y⟩
    let p := b x + C x y
    have hpreimage : U x (p - b x) = y := by
      have hdiff : p - b x = C x y := by
        dsimp [p]
        abel
      rw [hdiff, hUC]
    have hresponse : h x y = lambda * x + kappa p := by
      have hd := hdrift x p
      rw [hpreimage] at hd
      exact hd
    have hx : (h x y - kappa p) * lambda⁻¹ = x := by
      rw [hresponse]
      calc
        (lambda * x + kappa p - kappa p) * lambda⁻¹ =
            x * (lambda * lambda⁻¹) := by ring
        _ = x := by rw [hlambdaMul, mul_one]
    have hy : U x (p - b x) = y := hpreimage
    change
      (((h x y - kappa p) * lambda⁻¹),
        U ((h x y - kappa p) * lambda⁻¹)
          (p - b ((h x y - kappa p) * lambda⁻¹))) = (x, y)
    rw [hx, hpreimage]
  exact ⟨hleft.injective, hright.surjective⟩

end

end HC4.Valuation
