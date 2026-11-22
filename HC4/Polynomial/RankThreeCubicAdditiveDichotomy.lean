import Mathlib.Tactic

/-!
# A pointwise dichotomy for two linear maps is a global dichotomy

If two additive maps f and g defined on the same additive
group satisfy f(x)=0 or g(x)=0 at *every* point, then one
of the maps vanishes everywhere. Indeed, choose x with
f(x) nonzero and y with g(y) nonzero; additivity makes
both images nonzero at x+y, contradicting the hypothesis.

The result needs no topology, irreducibility, generic-point
choice, or infinitude of the ground field. It is the algebraic
upgrade from a pointwise tangent-Hessian dichotomy to a
uniform pencil normal form.
-/

namespace HC4.Polynomial.RankThreeCubic

noncomputable section

/-- Two additive maps cannot have pointwise complementary
zero sets without one map being identically zero. -/
theorem additiveMaps_pointwiseEitherZero_implies_globalEitherZero
    {G A B : Type*}
    [AddGroup G] [AddGroup A] [AddGroup B]
    (f : G → A) (g : G → B)
    (hf : ∀ x y : G, f (x + y) = f x + f y)
    (hg : ∀ x y : G, g (x + y) = g x + g y)
    (h : ∀ x : G, f x = 0 ∨ g x = 0) :
    (∀ x : G, f x = 0) ∨ (∀ x : G, g x = 0) := by
  classical
  by_cases hzero : ∀ x : G, f x = 0
  · exact Or.inl hzero
  · right
    push_neg at hzero
    obtain ⟨x, hx⟩ := hzero
    intro y
    by_contra hy
    have hgX : g x = 0 := (h x).resolve_left hx
    have hfY : f y = 0 := (h y).resolve_right hy
    have hfx : f (x + y) ≠ 0 := by
      rw [hf x y, hfY, add_zero]
      exact hx
    have hgy : g (x + y) ≠ 0 := by
      rw [hg x y, hgX, zero_add]
      exact hy
    rcases h (x + y) with hz | hz
    · exact hfx hz
    · exact hgy hz

end
end HC4.Polynomial.RankThreeCubic
