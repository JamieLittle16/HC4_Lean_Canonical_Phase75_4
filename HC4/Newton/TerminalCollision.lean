import HC4.Newton.ExactCollisionFirstWall

/-!
# Terminal collision

This module isolates the elementary final contradiction used by terminal
restart endpoints.

If a polynomial gradient is injective, two points with exactly equal
gradient values must coincide.  Hence a distinct exact gradient collision
is incompatible with an injective terminal gradient.

The theorem is intentionally independent of valuation or DVR structures:
all such machinery only has to deliver a distinct collision on the special
fibre and an injective reduced gradient.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The evaluated polynomial gradient as an ordinary function on source
points. -/
def mvGradientMap
    (F : MvPolynomial σ K) :
    (σ -> K) -> (σ -> K) :=
  fun p => mvGradientAt p F

/-- Exact equality of gradients is equality under `mvGradientMap`. -/
theorem mvGradientMap_eq_of_exactCollision
    (F : MvPolynomial σ K)
    (p q : σ -> K)
    (hcoll : HasExactGradientCollision F p q) :
    mvGradientMap F p = mvGradientMap F q := by
  funext i
  exact hcoll i

/-- Injectivity of the terminal gradient identifies the two points of an
exact collision. -/
theorem exactGradientCollision_eq_of_injective
    (F : MvPolynomial σ K)
    (p q : σ -> K)
    (hinj : Function.Injective (mvGradientMap F))
    (hcoll : HasExactGradientCollision F p q) :
    p = q := by
  apply hinj
  exact mvGradientMap_eq_of_exactCollision F p q hcoll

/-- A distinct exact collision contradicts an injective terminal gradient. -/
theorem exactGradientCollision_impossible_of_injective
    (F : MvPolynomial σ K)
    (p q : σ -> K)
    (hpq : p ≠ q)
    (hinj : Function.Injective (mvGradientMap F))
    (hcoll : HasExactGradientCollision F p q) :
    False := by
  exact hpq
    (exactGradientCollision_eq_of_injective
      F p q hinj hcoll)

end

end HC4.Newton
