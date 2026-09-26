import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSupportFrontier
import HC4.Newton.MixedDegreeWallRefinement

/-!
# A19.9: current-terminal quadratic refinement to an honest homogeneous packet

A18.5.21 exposes, on the actual represented terminal special fibre, a nonempty
quadratic Smith refinement whose projected exponents are exactly the three
binary patterns `(0,2,0)`, `(1,1,0)`, `(2,0,0)`.

The generic mixed-degree wall theorem already knows how to consume precisely
such a finite subface.  It selects its minimal ordinary degree and returns the
literal longitudinal initial form of that same polynomial subface.  The packet
is nonzero and ordinary-homogeneous, and—crucially—the existing theorem has
already proved that this extraction retains the canonical exact collision,
zero Hessian determinant, and persistent rank-one packet support.

This file only adapts that green theorem to the current A18.5 terminal.  Thus
the remaining JC2-facing quadratic producer receives an actual homogeneous
polynomial collision packet with source provenance; it need not reconstruct
one from support-pattern equations.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Homogeneous packet extracted from the canonical quadratic Smith subface of
one current presented terminal. -/
structure AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket
    {RR : RepairRanking}
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) : Type (u + 1) where
  degree : ℕ
  packet : MvPolynomial (Fin 4) K
  provenance :
    IsMinimalLongitudinalSmithPacket
      (smithSymmetricBalancedSubface
        (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
        0 (fun _ : SmithSupportExponent => (0 : ℤ)))
      T.specialFiber degree packet
  degree_ge_two : 2 ≤ degree
  exactCollision :
    HasExactGradientCollision packet
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  hessian_zero : HC4.Polynomial.hessianDeterminant packet = 0
  persistent :
    HasRankOnePersistentPacketSupport
      (0 : Fin 4) 1 2 degree packet

/-- **Quadratic terminal support produces an honest homogeneous collision
packet.**  This is the current-terminal form of the green generic packet
extractor. -/
theorem AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.quadraticPacket_nonempty
    {RR : RepairRanking}
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hne :
      (smithSymmetricBalancedSubface
        (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
        0 (fun _ : SmithSupportExponent => (0 : ℤ))).Nonempty)
    (hshape :
      ∀ e ∈ smithSymmetricBalancedSubface
        (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
        0 (fun _ : SmithSupportExponent => (0 : ℤ)),
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    Nonempty (AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket T) := by
  let S : Finset SmithSupportExponent :=
    smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ))
  have hSne : S.Nonempty := by
    simpa [S] using hne
  have hSsubset :
      S ⊆ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber := by
    intro e he
    have he' :
        e ∈ smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ)) := by
      simpa [S] using he
    exact (mem_smithSymmetricBalancedSubface.mp he').1
  have hSshape :
      ∀ e ∈ S,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
    intro e he
    exact hshape e (by simpa [S] using he)
  rcases
      nonemptyQuadraticProjectedSubface_exists_minimalLongitudinalPacket
        S T.specialFiber hSne hSsubset hSshape with
    ⟨D, Q, hprov, hD, hcoll, hhess, hpersistent⟩
  exact ⟨{
    degree := D
    packet := Q
    provenance := by simpa [S] using hprov
    degree_ge_two := hD
    exactCollision := hcoll
    hessian_zero := hhess
    persistent := hpersistent
  }⟩

end

end HC4.Valuation
