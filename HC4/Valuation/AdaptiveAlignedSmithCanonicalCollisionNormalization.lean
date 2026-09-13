import HC4.Valuation.AdaptiveAlignedSmithCanonicalPointedCollisionAxisNormalization

/-!
# A18.5.86: arbitrary determinant-one collision enters canonical A18

A18.5.84 recentres an arbitrary distinct exact gradient collision at `p,q` to
`0 ~ (q-p)`.  A18.5.85 then uses determinant-one source transvections to send
the nonzero displacement to `e_0` while preserving determinant one and every
nonlinear degree ceiling.

This file is the proposition-level composition.  It is the global front door
needed by the final HC4 contradiction: there is no longer any assumption that
a counterexample arrives pre-normalised at `0,e_0`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **A18.5.86 — arbitrary exact determinant-one collision -> canonical A18
zero-defect entry.** -/
noncomputable def zeroDefectCollisionEntry_ofExactCollision
    (degreeCap : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (p q : Fin 4 → K)
    (hdegree : NonlinearDegreeBound degreeCap F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) :=
  (AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry.ofExactCollision
      degreeCap F p q hdegree hdet hpq hcoll).toZeroDefectCollisionEntry

end

end HC4.Valuation
