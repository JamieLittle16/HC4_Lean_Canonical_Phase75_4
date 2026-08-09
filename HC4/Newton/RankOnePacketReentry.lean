import HC4.Newton.RankOnePacketQuadratic
import Mathlib.Tactic

/-!
# Rank-one persistent-packet re-entry certificate

Phase 92.2 gives the first persistent packet a canonical denominator-cleared
binary block and proves the discriminant/determinant dichotomy.

This file turns that dichotomy into the form needed by the finite corank
argument.

There are two additions.

1. A nonzero polynomial satisfying the Phase 92.1 packet-support condition
   automatically has a nonzero canonical binary quadratic.  Thus later
   arguments need only assume that the persistent packet itself is nonzero.

2. A binary block with nonzero determinant core has trivial kernel.  Hence
   the nonzero-discriminant branch is not another unresolved rank-one
   phenomenon: it is genuinely two-dimensional in the transverse variables.

The resulting re-entry theorem says that every nonzero persistent packet is
either

* a determinant-zero square/axis packet already controlled by the Phase 91
  rank-one geometry; or
* a determinant-nonzero transverse packet with trivial kernel, certifying
  genuine rank-two escalation.

This is deliberately an algebraic re-entry certificate.  The next layer
must connect the rank-two certificate to the next Rees/Schur event and then
prove that repeated repairs decrease a finite complexity measure.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

namespace BinarySchurBlock

/-- A binary symmetric block has no nonzero vector in its kernel. -/
def HasTrivialKernel
    (q : BinarySchurBlock K) : Prop :=
  ∀ u v : K,
    q.a * u + q.b * v = 0 ->
    q.b * u + q.c * v = 0 ->
    u = 0 ∧ v = 0

/-- Nonzero determinant core gives a trivial kernel by explicit
two-by-two elimination. -/
theorem hasTrivialKernel_of_detCore_ne_zero
    (q : BinarySchurBlock K)
    (hdet : q.detCore ≠ 0) :
    q.HasTrivialKernel := by
  intro u v hfirst hsecond
  have huProd : q.detCore * u = 0 := by
    calc
      q.detCore * u =
          q.c * (q.a * u + q.b * v) -
            q.b * (q.b * u + q.c * v) := by
              unfold BinarySchurBlock.detCore
              ring
      _ = 0 := by
        rw [hfirst, hsecond]
        ring
  have hvProd : q.detCore * v = 0 := by
    calc
      q.detCore * v =
          q.a * (q.b * u + q.c * v) -
            q.b * (q.a * u + q.b * v) := by
              unfold BinarySchurBlock.detCore
              ring
      _ = 0 := by
        rw [hfirst, hsecond]
        ring
  exact
    ⟨(mul_eq_zero.mp huProd).resolve_left hdet,
      (mul_eq_zero.mp hvProd).resolve_left hdet⟩

end BinarySchurBlock

/-- A nonzero polynomial with persistent-packet support must have at least
one nonzero canonical packet coefficient. -/
theorem rankOnePacketQuadraticNonzero_of_polynomial_ne_zero
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (hF : F ≠ 0) :
    RankOnePacketQuadraticNonzero x y z D F := by
  by_contra hquad
  have hcoeffs :
      rankOnePacketCoeffYY x y D F = 0 ∧
      rankOnePacketCoeffYZ x y z D F = 0 ∧
      rankOnePacketCoeffZZ x z D F = 0 := by
    simpa [RankOnePacketQuadraticNonzero] using hquad
  apply hF
  ext d
  by_cases hd : MvPolynomial.coeff d F = 0
  · simp [hd]
  · rcases rankOnePersistentPacket_support_cases
      hxy hxz hyz hpacket hd with hYY | hYZ | hZZ
    · subst d
      simpa [rankOnePacketCoeffYY] using hcoeffs.1
    · subst d
      simpa [rankOnePacketCoeffYZ] using hcoeffs.2.1
    · subst d
      simpa [rankOnePacketCoeffZZ] using hcoeffs.2.2

/-- The determinant-nonzero branch of a persistent packet has a genuinely
trivial transverse kernel. -/
theorem rankOnePacket_trivialKernel_of_discriminant_ne_zero
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (hdisc : rankOnePacketDiscriminant x y z D F ≠ 0) :
    (rankOnePacketQuadraticBlock x y z D F).HasTrivialKernel := by
  apply BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero
  intro hdet
  exact hdisc
    ((rankOnePacketQuadraticBlock_detCore_eq_zero_iff
      x y z D F).1 hdet)

/-- Full algebraic re-entry certificate for a nonzero persistent packet. -/
def HasRankOnePacketReentry
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  (rankOnePacketDiscriminant x y z D F = 0 ∧
    (((rankOnePacketQuadraticBlock x y z D F).LeftPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D F).a *
            (rankOnePacketQuadraticBlock x y z D F).quadratic Y Z =
          ((rankOnePacketQuadraticBlock x y z D F).a * Y +
            (rankOnePacketQuadraticBlock x y z D F).b * Z) ^ 2)) ∨
    ((rankOnePacketQuadraticBlock x y z D F).RightAxisPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D F).quadratic Y Z =
          (rankOnePacketQuadraticBlock x y z D F).c * Z * Z)))) ∨
  (rankOnePacketDiscriminant x y z D F ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D F).detCore ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D F).HasTrivialKernel)

/-- **Rank-one persistent-packet re-entry theorem.**
A nonzero persistent packet cannot remain an unclassified rank-one object.

Either its binary quadratic is determinant zero and has the explicit
square/axis geometry from Phase 91, or its discriminant is nonzero and its
binary block has trivial kernel, certifying genuine rank-two transverse
behaviour. -/
theorem rankOnePersistentPacket_reentry
    [CharZero K]
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (hF : F ≠ 0) :
    HasRankOnePacketReentry x y z D F := by
  have hnz :
      RankOnePacketQuadraticNonzero x y z D F :=
    rankOnePacketQuadraticNonzero_of_polynomial_ne_zero
      hxy hxz hyz hpacket hF
  by_cases hdisc :
      rankOnePacketDiscriminant x y z D F = 0
  · left
    refine ⟨hdisc, ?_⟩
    exact
      rankOnePacket_squareGeometry_of_discriminant_eq_zero
        x y z D F hnz hdisc
  · right
    refine ⟨hdisc, ?_, ?_⟩
    · intro hdet
      exact hdisc
        ((rankOnePacketQuadraticBlock_detCore_eq_zero_iff
          x y z D F).1 hdet)
    · exact
        rankOnePacket_trivialKernel_of_discriminant_ne_zero
          x y z D F hdisc

end

end HC4.Newton
