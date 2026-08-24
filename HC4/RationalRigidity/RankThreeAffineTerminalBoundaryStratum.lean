import HC4.RationalRigidity.RankThreeAffineTerminalNormalForm
import HC4.Newton.MvBoundaryStrata
import Mathlib.Tactic

/-!
# A18.5.40: classify the far boundary endpoint of an affine rank-three terminal

A18.5.39 packages the complete scalar normal form and proves that the far
supported exponent lies on the toric boundary.  For the symmetric-gradings
application the actual edge support is torus balanced.  The existing boundary
stratum theorem then leaves exactly the two manuscript endpoint geometries:

* a genuine rank-three point in the relative interior of one facet; or
* a point on one of the four extreme transition rays.

This file is only the representation adapter from the actual `Fin 4 ->₀ Nat`
endpoint to the already-verified toric boundary classification.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Newton
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Toric stratum of the far endpoint of a balanced affine rank-three
terminal. -/
inductive RankThreeAffineTerminalTopStratum
    (a b : ℕ) (d : Fin 4 →₀ ℕ) : Prop
  | rankThree
      (facet : ToricFacet)
      (h : MvRankThreeOnFacet facet d)
  | extremeRay
      (facet next : ToricFacet)
      (adjacent : AdjacentFacets facet next)
      (ray : OnRay a b facet next (toToricExponent d))

/-- **Balanced affine terminal top endpoint = rank-three facet point or
extreme ray.** -/
theorem rankThreeAffineTerminal_topStratum
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C P Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hbal : IsBalancedExponent a b (L.exponent phi.natDegree)) :
    RankThreeAffineTerminalTopStratum
      a b (L.exponent phi.natDegree) := by
  have hboundary : MvExponentOnBoundary (L.exponent phi.natDegree) :=
    rankThreeAffineLine_topExponent_on_boundary_of_certificate
      L hA hB hC hP hphiDeg hphi0 hcert
  rcases mv_boundary_rankThree_or_extremeRay
      ha hb hcop hbal hboundary with hthree | hray
  · rcases hthree with ⟨facet, hfacet⟩
    exact .rankThree facet hfacet
  · rcases hray with ⟨facet, next, hadj, hray⟩
    exact .extremeRay facet next hadj hray

end

end HC4.RationalRigidity
