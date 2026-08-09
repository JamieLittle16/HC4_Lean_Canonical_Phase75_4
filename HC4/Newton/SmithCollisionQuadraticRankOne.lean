import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Collision forces the persistent Smith quadratic to have rank one

The restart proof has a sharper conclusion than the abstract
rank-one-packet re-entry dichotomy.

At the first nonzero transverse collision wall, the persistent packet is

    x^e q(y,z),

with `x` a unit and `(y,z) ≠ (0,0)`.  Equality of the leading transverse
gradient values gives

    ∇q(y,z) = 0.

If the binary quadratic were nondegenerate, its linear gradient map would
have trivial kernel, forcing `(y,z) = (0,0)`, contradiction.  Therefore
the quadratic Hessian has determinant zero.

This file proves exactly that finite algebraic step using the Phase 92
denominator-cleared binary block and the Phase 92.3 theorem

    detCore ≠ 0  ->  HasTrivialKernel.

Thus the nondegenerate branch of the Phase 92 re-entry dichotomy is
eliminated at an actual nonzero collision wall.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- A nonzero vector in the kernel of a binary Schur block forces its
determinant core to vanish. -/
theorem BinarySchurBlock.detCore_eq_zero_of_nonzero_kernel
    (q : BinarySchurBlock K)
    (u v : K)
    (hvec : u ≠ 0 ∨ v ≠ 0)
    (hfirst : q.a * u + q.b * v = 0)
    (hsecond : q.b * u + q.c * v = 0) :
    q.detCore = 0 := by
  by_contra hdet
  have hkernel :
      u = 0 ∧ v = 0 :=
    (BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero
      q hdet) u v hfirst hsecond
  rcases hvec with hu | hv
  · exact hu hkernel.1
  · exact hv hkernel.2

/-- Leading transverse gradient equations for the actual persistent
quadratic

    A Y^2 + B Y Z + C Z^2.

The equations are its two first derivatives with the harmless common
longitudinal factor removed. -/
def HasPersistentQuadraticGradientZero
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K) : Prop :=
  2 * rankOnePacketCoeffYY x y D F * Y +
      rankOnePacketCoeffYZ x y z D F * Z = 0 ∧
    rankOnePacketCoeffYZ x y z D F * Y +
      2 * rankOnePacketCoeffZZ x z D F * Z = 0

/-- The leading-gradient equations give the two kernel equations for the
denominator-cleared binary block from Phase 92.2. -/
theorem rankOnePacketQuadraticBlock_kernel_of_gradientZero
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K)
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D F Y Z) :
    (rankOnePacketQuadraticBlock x y z D F).a * Y +
        (rankOnePacketQuadraticBlock x y z D F).b * Z = 0 ∧
      (rankOnePacketQuadraticBlock x y z D F).b * Y +
        (rankOnePacketQuadraticBlock x y z D F).c * Z = 0 := by
  rcases hgrad with ⟨hY, hZ⟩
  constructor
  · change
      (4 * rankOnePacketCoeffYY x y D F) * Y +
        (2 * rankOnePacketCoeffYZ x y z D F) * Z = 0
    linear_combination 2 * hY
  · change
      (2 * rankOnePacketCoeffYZ x y z D F) * Y +
        (4 * rankOnePacketCoeffZZ x z D F) * Z = 0
    linear_combination 2 * hZ

/-- **Collision forces the persistent quadratic blocker to be degenerate.**
If the leading transverse gradient vanishes at a nonzero transverse wall
point, the Phase 92 binary block has determinant core zero. -/
theorem rankOnePacket_detCore_eq_zero_of_nonzero_collision
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D F Y Z) :
    (rankOnePacketQuadraticBlock x y z D F).detCore = 0 := by
  have hk :=
    rankOnePacketQuadraticBlock_kernel_of_gradientZero
      x y z D F Y Z hgrad
  exact
    BinarySchurBlock.detCore_eq_zero_of_nonzero_kernel
      (rankOnePacketQuadraticBlock x y z D F)
      Y Z hpoint hk.1 hk.2

/-- In characteristic zero, the same collision hypothesis forces the
ordinary discriminant of the persistent quadratic to vanish. -/
theorem rankOnePacket_discriminant_eq_zero_of_nonzero_collision
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D F Y Z) :
    rankOnePacketDiscriminant x y z D F = 0 := by
  apply
    (rankOnePacketQuadraticBlock_detCore_eq_zero_iff
      x y z D F).1
  exact
    rankOnePacket_detCore_eq_zero_of_nonzero_collision
      x y z D F Y Z hpoint hgrad

/-- **Smith collision rank-one certificate.**
For a nonzero persistent packet, a nonzero transverse collision point with
vanishing leading transverse gradient lands directly in the rigid
discriminant-zero square/axis geometry.  The nondegenerate rank-two
alternative of Phase 92 cannot occur at this wall. -/
theorem rankOnePersistentPacket_rigid_of_nonzero_collision
    [CharZero K]
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (hF : F ≠ 0)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D F Y Z) :
    HasRigidRankOnePacket x y z D F := by
  have hnz :
      RankOnePacketQuadraticNonzero x y z D F :=
    rankOnePacketQuadraticNonzero_of_polynomial_ne_zero
      hxy hxz hyz hpacket hF
  have hdisc :
      rankOnePacketDiscriminant x y z D F = 0 :=
    rankOnePacket_discriminant_eq_zero_of_nonzero_collision
      x y z D F Y Z hpoint hgrad
  refine ⟨hdisc, ?_⟩
  exact
    rankOnePacket_squareGeometry_of_discriminant_eq_zero
      x y z D F hnz hdisc

end

end HC4.Newton
