import HC4.Polynomial.FiniteStaircaseCrossRoofArithmetic
import Mathlib.Tactic

/-!
# Lower-hull arithmetic for the finite staircase

The source-honest left `(1,V)` carrier is most conveniently viewed in the two
coordinate deficits

    a = e₁,   b = e₂,

with longitudinal coordinate `t = e₀`.  Writing

    k = t + a,   j + 1 = t + b,

the staircase wall equation gives the exact chord identity

    ell*a + (n-1)*b
      = ell*(n-1) + (ell+n-1)*(1-t).

Hence `t=1` is exactly the chord joining the honest `a=0` locked endpoint to
the honest `b=0` highest endpoint, while `t=0` lies strictly northeast of that
chord.  In particular a point with `t=0` and both deficits positive cannot lie
below both axis endpoints for any positive exposing functional.

These facts are state-free.  They are the arithmetic input for the source
multi-fibre exposed-roof adapter.
-/

namespace HC4.Polynomial

noncomputable section

/-- **Exact source-deficit chord identity.** -/
theorem staircase_source_deficit_chord_identity
    {n ell t a b : ℕ}
    (hwall :
      ((n : ℤ) - 1) * ((t : ℤ) + (b : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (t : ℤ) - (a : ℤ))) :
    (ell : ℤ) * (a : ℤ) + ((n : ℤ) - 1) * (b : ℤ) =
      (ell : ℤ) * ((n : ℤ) - 1) +
        ((ell : ℤ) + (n : ℤ) - 1) * (1 - (t : ℤ)) := by
  nlinarith [hwall]

/-- A positive `t=0` staircase point cannot minimize a positive linear
functional against both honest axis endpoints `(0,ell)` and `(n-1,0)`.

This is the precise arithmetic statement excluding the only boundary
monomial left by the lower-hull positive-vertex alternative. -/
theorem zeroLongitudinal_not_positive_lowerHull
    {n ell a b A B : ℕ}
    (hn : 2 ≤ n) (hell : 0 < ell)
    (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B)
    (hwall :
      ((n : ℤ) - 1) * ((b : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (a : ℤ)))
    (hlocked :
      (A : ℤ) * (a : ℤ) + (B : ℤ) * (b : ℤ) ≤
        (B : ℤ) * (ell : ℤ))
    (hhighest :
      (A : ℤ) * (a : ℤ) + (B : ℤ) * (b : ℤ) ≤
        (A : ℤ) * ((n : ℤ) - 1)) : False := by
  have hAZ : (0 : ℤ) < (A : ℤ) := by exact_mod_cast hA
  have hBZ : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hB
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hn1Z : (0 : ℤ) < (n : ℤ) - 1 := by
    exact_mod_cast (show 1 < n by omega)
  have hellZ : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell

  have hAa :
      (A : ℤ) * (a : ℤ) ≤
        (B : ℤ) * ((ell : ℤ) - (b : ℤ)) := by
    nlinarith [hlocked]
  have hBb :
      (B : ℤ) * (b : ℤ) ≤
        (A : ℤ) * (((n : ℤ) - 1) - (a : ℤ)) := by
    nlinarith [hhighest]

  have hAa0 : (0 : ℤ) ≤ (A : ℤ) * (a : ℤ) := by positivity
  have hBb0 : (0 : ℤ) ≤ (B : ℤ) * (b : ℤ) := by positivity
  have hRightA0 :
      (0 : ℤ) ≤ (B : ℤ) * ((ell : ℤ) - (b : ℤ)) :=
    le_trans hAa0 hAa

  have hprod :
      ((A : ℤ) * (a : ℤ)) * ((B : ℤ) * (b : ℤ)) ≤
        ((B : ℤ) * ((ell : ℤ) - (b : ℤ))) *
          ((A : ℤ) * (((n : ℤ) - 1) - (a : ℤ))) :=
    mul_le_mul hAa hBb hBb0 hRightA0

  have hAB : (0 : ℤ) < (A : ℤ) * (B : ℤ) := mul_pos hAZ hBZ
  have hscaled :
      ((A : ℤ) * (B : ℤ)) * ((a : ℤ) * (b : ℤ)) ≤
        ((A : ℤ) * (B : ℤ)) *
          (((ell : ℤ) - (b : ℤ)) *
            (((n : ℤ) - 1) - (a : ℤ))) := by
    calc
      ((A : ℤ) * (B : ℤ)) * ((a : ℤ) * (b : ℤ)) =
          ((A : ℤ) * (a : ℤ)) * ((B : ℤ) * (b : ℤ)) := by ring
      _ ≤ ((B : ℤ) * ((ell : ℤ) - (b : ℤ))) *
          ((A : ℤ) * (((n : ℤ) - 1) - (a : ℤ))) := hprod
      _ = ((A : ℤ) * (B : ℤ)) *
          (((ell : ℤ) - (b : ℤ)) *
            (((n : ℤ) - 1) - (a : ℤ))) := by ring

  have hcancel :
      (a : ℤ) * (b : ℤ) ≤
        ((ell : ℤ) - (b : ℤ)) *
          (((n : ℤ) - 1) - (a : ℤ)) :=
    (mul_le_mul_left hAB).mp hscaled

  have hchordLe :
      (ell : ℤ) * (a : ℤ) + ((n : ℤ) - 1) * (b : ℤ) ≤
        (ell : ℤ) * ((n : ℤ) - 1) := by
    nlinarith [hcancel]

  nlinarith [hwall, hchordLe]

end

end HC4.Polynomial