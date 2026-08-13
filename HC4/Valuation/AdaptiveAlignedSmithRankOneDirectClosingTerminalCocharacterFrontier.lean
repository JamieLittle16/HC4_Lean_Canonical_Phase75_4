import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingCanonicalSquareLattice
import Mathlib.Tactic

/-!
# Direct-closing terminal cocharacter frontier

The canonical fresh-square lattice has now reduced the equality branch
`j = Delta` to either an explicit earlier coefficient/section wall or an
honest terminal first-contact Monge--Ampere fibre carrying the fresh square.

It is important not to identify the first-contact exposure weight with a
terminal homogeneous cocharacter.  The two objects are genuinely different.
This file records the exact terminal consequence instead:

* any honest nontrivial terminal source cocharacter on the square fibre is
  already impossible, by the green square-contact elimination;
* hence every surviving canonical terminal square fibre is cocharacter-free;
* equivalently, for every honest nontrivial candidate terminal source weight,
  the finite support of the fibre contains a monomial whose weighted degree
  differs from the distinguished square degree.

Thus the terminal side of the equality branch has become a concrete second
Newton-support problem rather than an implicit cocharacter assumption.
No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A terminal aligned-square fibre is cocharacter-free when there is no
honest nontrivial integral source cocharacter transporting its marked right
point. -/
def DirectClosingSquareTerminalCocharacterFree
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L) : Prop :=
  ¬ Nonempty (DirectClosingSquareFirstContactTerminalCocharacterData T)

/-- **Every surviving terminal square fibre is cocharacter-free.**

Indeed, the generic aligned-square terminal theorem already proves that any
honest terminal cocharacter would contradict the surviving fresh square and
exact collision. -/
theorem directClosingSquare_terminal_cocharacterFree
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L) :
    DirectClosingSquareTerminalCocharacterFree T := by
  intro hE
  rcases hE with ⟨E⟩
  exact E.impossible

/-- The distinguished square has weighted degree `w_i + w_i` for every
integral source weight, independently of any homogeneity assumption. -/
theorem directClosingSquare_squareExponent_integralWeightedDegree
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (weight : Fin 4 → ℕ) :
    integralWeightedDegree (fun i => (weight i : ℤ)) D.squareExponent =
      (weight D.index : ℤ) + (weight D.index : ℤ) := by
  simpa [DirectClosingAlignedSquareSourceData.squareExponent,
    directClosingQuadraticExponent, HC4.Newton.quadraticExponent, add_comm] using
    (integralWeightedDegree_quadraticExponent
      (fun i : Fin 4 => (weight i : ℤ)) D.index D.index)

/-- Cocharacter-freeness is a finite support obstruction.

For every nontrivial natural source weight which honestly transports the
terminal marked right point, some actual supported monomial has weighted
degree different from the fresh square degree.  Otherwise that weight would
make the whole terminal fibre weighted homogeneous and hence would define the
forbidden terminal cocharacter. -/
theorem directClosingSquare_terminal_exists_weightMismatch
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L)
    (weight : Fin 4 → ℕ)
    (hnontrivial :
      IsNontrivialIntegralWeight (fun i => (weight i : ℤ)))
    (hright :
      HasIntegralAdaptiveSmithSection weight
        (directClosingSquareTerminalRightConstantSection T)) :
    ∃ m : Fin 4 →₀ ℕ,
      MvPolynomial.coeff m T.fibre ≠ 0 ∧
      integralWeightedDegree (fun i => (weight i : ℤ)) m ≠
        (weight D.index : ℤ) + (weight D.index : ℤ) := by
  by_contra hno
  push_neg at hno
  have hhom :
      IsIntegralWeightedHomogeneous
        (fun i => (weight i : ℤ))
        ((weight D.index + weight D.index : ℕ) : ℤ)
        T.fibre := by
    intro m hm
    have hmdeg := hno m hm
    simpa using hmdeg
  let E : DirectClosingSquareFirstContactTerminalCocharacterData T := {
    weight := weight
    degree := weight D.index + weight D.index
    nontrivial := hnontrivial
    homogeneous := hhom
    rightPointIntegrality := hright
  }
  exact (directClosingSquare_terminal_cocharacterFree T) ⟨E⟩

/-- The support witness furnished above is genuinely different from the
fresh square exponent itself. -/
theorem directClosingSquare_terminal_exists_competingSupportExponent
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L)
    (weight : Fin 4 → ℕ)
    (hnontrivial :
      IsNontrivialIntegralWeight (fun i => (weight i : ℤ)))
    (hright :
      HasIntegralAdaptiveSmithSection weight
        (directClosingSquareTerminalRightConstantSection T)) :
    ∃ m : Fin 4 →₀ ℕ,
      MvPolynomial.coeff m T.fibre ≠ 0 ∧
      m ≠ D.squareExponent ∧
      integralWeightedDegree (fun i => (weight i : ℤ)) m ≠
        integralWeightedDegree
          (fun i => (weight i : ℤ)) D.squareExponent := by
  rcases directClosingSquare_terminal_exists_weightMismatch
      T weight hnontrivial hright with ⟨m, hm, hdeg⟩
  have hsquare :=
    directClosingSquare_squareExponent_integralWeightedDegree
      (D := D) weight
  refine ⟨m, hm, ?_, ?_⟩
  · intro hmsquare
    subst m
    exact hdeg hsquare
  · simpa [hsquare] using hdeg

/-- Exact extraction obligation for the terminal half of the canonical
square frontier.  It asks for a genuine second source cocharacter on the
already constructed terminal first-contact fibre; it does *not* reuse the
first-contact exposure weight. -/
def HasDirectClosingCanonicalTerminalCocharacterExtraction
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop :=
  ∀ (D : DirectClosingAlignedSquareSourceData C)
    (G : DirectClosingCanonicalSquareIntegralityData D)
    (T : DirectClosingSquareFirstContactTerminalData
      (G.toFirstContactLattice heq)),
    Nonempty (DirectClosingSquareFirstContactTerminalCocharacterData T)

/-- If the honest terminal-cocharacter extraction is supplied, the terminal
half of the canonical square dichotomy disappears unconditionally.  Thus at
`j = Delta` only the explicit earlier-wall branch can remain. -/
theorem directClosing_equality_forces_earlierWall_of_terminalCocharacterExtraction
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (hextract : HasDirectClosingCanonicalTerminalCocharacterExtraction C heq) :
    ∃ D : DirectClosingAlignedSquareSourceData C,
      DirectClosingCanonicalSquareEarlierWall D := by
  rcases C.directClosing_canonicalTerminalSquare_or_earlierWall heq with
    hterm | hwall
  · rcases hterm with ⟨D, G, hT⟩
    rcases hT with ⟨T⟩
    rcases hextract D G T with ⟨E⟩
    exact False.elim E.impossible
  · exact hwall

/-- **Sharp unconditional equality frontier after square elimination.**

Without assuming the second cocharacter extraction, `j = Delta` now has only
two honest outputs: an explicit earlier wall, or an actual terminal square
fibre together with a proof that no honest terminal cocharacter exists on it.
The latter proof immediately yields the competing-support theorem above for
any candidate honest weight. -/
theorem directClosing_equality_earlierWall_or_cocharacterFreeTerminal
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (∃ D : DirectClosingAlignedSquareSourceData C,
      DirectClosingCanonicalSquareEarlierWall D) ∨
    (∃ (D : DirectClosingAlignedSquareSourceData C)
        (G : DirectClosingCanonicalSquareIntegralityData D)
        (T : DirectClosingSquareFirstContactTerminalData
          (G.toFirstContactLattice heq)),
      DirectClosingSquareTerminalCocharacterFree T) := by
  rcases C.directClosing_canonicalTerminalSquare_or_earlierWall heq with
    hterm | hwall
  · right
    rcases hterm with ⟨D, G, hT⟩
    rcases hT with ⟨T⟩
    exact ⟨D, G, T, directClosingSquare_terminal_cocharacterFree T⟩
  · left
    exact hwall

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
