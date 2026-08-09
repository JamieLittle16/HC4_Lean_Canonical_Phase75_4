import HC4.Newton.SmithRefinedFacePolynomial
import HC4.Newton.ExactCollisionFirstWall
import Mathlib.Tactic

/-!
# Exact transverse collisions for rank-one persistent packets

The green Phase 93.17 construction reaches a canonical rank-one packet
`x^(D-2) q(y,z)`, but Phase 93.4 was still phrased using the coefficient
equations

    2 A Y + B Z = 0,
    B Y + 2 C Z = 0.

This file identifies those equations with the actual evaluated polynomial
gradient at the normalised transverse point

    x = 1,  y = Y,  z = Z,

with all other coordinates zero.

For any polynomial satisfying `HasRankOnePersistentPacketSupport`, we first
prove an exact three-monomial normal form.  Rewriting those monomials into
products of `X x`, `X y`, and `X z` then gives the two transverse derivative
formulas directly.

Consequently, an exact gradient collision between the origin and the
normalised transverse point automatically produces
`HasPersistentQuadraticGradientZero`.  At a nonzero transverse point this
feeds the already-green Phase 93.4 collision theorem and forces the rigid
discriminant-zero packet.

The final theorem applies this directly to the canonical symmetric Smith
restriction from Phase 93.17.  After this module, the remaining global
geometric input is reduced to proving that the actual first nonzero restart
wall induces such an exact gradient collision on the canonical restriction.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The normalised transverse point used by the persistent rank-one packet:
`x=1`, `y=Y`, `z=Z`, and every other coordinate zero. -/
noncomputable def rankOnePacketTransversePoint
    (x y z : σ)
    (Y Z : K) : σ → K := by
  classical
  exact fun t =>
    if t = x then 1
    else if t = y then Y
    else if t = z then Z
    else 0

@[simp] theorem rankOnePacketTransversePoint_apply_x
    (x y z : σ)
    (Y Z : K) :
    rankOnePacketTransversePoint x y z Y Z x = 1 := by
  simp [rankOnePacketTransversePoint]

@[simp] theorem rankOnePacketTransversePoint_apply_y
    (x y z : σ)
    (hxy : x ≠ y)
    (Y Z : K) :
    rankOnePacketTransversePoint x y z Y Z y = Y := by
  simp [rankOnePacketTransversePoint, hxy, Ne.symm hxy]

@[simp] theorem rankOnePacketTransversePoint_apply_z
    (x y z : σ)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (Y Z : K) :
    rankOnePacketTransversePoint x y z Y Z z = Z := by
  simp [rankOnePacketTransversePoint,
    hxz, hyz, Ne.symm hxz, Ne.symm hyz]

/-- The `YY` and `YZ` packet exponents are distinct. -/
theorem rankOnePacketYY_ne_YZ
    {x y z : σ}
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (D : ℕ) :
    rankOnePacketYY x y D ≠
      rankOnePacketYZ x y z D := by
  intro h
  have hz :=
    congrArg (fun d : σ →₀ ℕ => d z) h
  simp [rankOnePacketYY, rankOnePacketYZ,
    hxz, hyz, Ne.symm hxz, Ne.symm hyz] at hz

/-- The `YY` and `ZZ` packet exponents are distinct. -/
theorem rankOnePacketYY_ne_ZZ
    {x y z : σ}
    (hxy : x ≠ y)
    (hyz : y ≠ z)
    (D : ℕ) :
    rankOnePacketYY x y D ≠
      rankOnePacketZZ x z D := by
  intro h
  have hy :=
    congrArg (fun d : σ →₀ ℕ => d y) h
  simp [rankOnePacketYY, rankOnePacketZZ,
    hxy, hyz, Ne.symm hxy, Ne.symm hyz] at hy

/-- The `YZ` and `ZZ` packet exponents are distinct. -/
theorem rankOnePacketYZ_ne_ZZ
    {x y z : σ}
    (hxy : x ≠ y)
    (hyz : y ≠ z)
    (D : ℕ) :
    rankOnePacketYZ x y z D ≠
      rankOnePacketZZ x z D := by
  intro h
  have hy :=
    congrArg (fun d : σ →₀ ℕ => d y) h
  simp [rankOnePacketYZ, rankOnePacketZZ,
    hxy, hyz, Ne.symm hxy, Ne.symm hyz] at hy

/-- The exact three-monomial polynomial attached to the three persistent
packet coefficients. -/
noncomputable def rankOnePacketMonomialModel
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.monomial
      (rankOnePacketYY x y D)
      (rankOnePacketCoeffYY x y D F) +
    MvPolynomial.monomial
      (rankOnePacketYZ x y z D)
      (rankOnePacketCoeffYZ x y z D F) +
    MvPolynomial.monomial
      (rankOnePacketZZ x z D)
      (rankOnePacketCoeffZZ x z D F)

/-- Support classification reconstructs the whole persistent packet from
its three canonical coefficients. -/
theorem rankOnePersistentPacket_eq_monomialModel
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F) :
    F = rankOnePacketMonomialModel x y z D F := by
  classical
  apply MvPolynomial.ext
  intro d
  have hYY_YZ :
      rankOnePacketYY x y D ≠
        rankOnePacketYZ x y z D :=
    rankOnePacketYY_ne_YZ hxz hyz D
  have hYY_ZZ :
      rankOnePacketYY x y D ≠
        rankOnePacketZZ x z D :=
    rankOnePacketYY_ne_ZZ hxy hyz D
  have hYZ_ZZ :
      rankOnePacketYZ x y z D ≠
        rankOnePacketZZ x z D :=
    rankOnePacketYZ_ne_ZZ hxy hyz D
  by_cases hYY :
      d = rankOnePacketYY x y D
  · subst d
    simp [rankOnePacketMonomialModel,
      rankOnePacketCoeffYY,
      rankOnePacketCoeffYZ,
      rankOnePacketCoeffZZ,
      hYY_YZ, hYY_ZZ,
      Ne.symm hYY_YZ, Ne.symm hYY_ZZ]
  · by_cases hYZ :
        d = rankOnePacketYZ x y z D
    · subst d
      simp [rankOnePacketMonomialModel,
        rankOnePacketCoeffYY,
        rankOnePacketCoeffYZ,
        rankOnePacketCoeffZZ,
        hYY_YZ, hYZ_ZZ,
        Ne.symm hYY_YZ, Ne.symm hYZ_ZZ]
    · by_cases hZZ :
          d = rankOnePacketZZ x z D
      · subst d
        simp [rankOnePacketMonomialModel,
          rankOnePacketCoeffYY,
          rankOnePacketCoeffYZ,
          rankOnePacketCoeffZZ,
          hYY_ZZ, hYZ_ZZ,
          Ne.symm hYY_ZZ, Ne.symm hYZ_ZZ]
      · have hzero :
            MvPolynomial.coeff d F = 0 :=
          coeff_eq_zero_outside_rankOnePacket
            hxy hxz hyz hpacket d
            hYY hYZ hZZ
        simp [rankOnePacketMonomialModel,
          hzero, hYY, hYZ, hZZ,
          Ne.symm hYY, Ne.symm hYZ, Ne.symm hZZ]

/-- Algebraic `X`-variable presentation of the same rank-one packet. -/
noncomputable def rankOnePacketAlgebraicModel
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.C (rankOnePacketCoeffYY x y D F) *
      MvPolynomial.X x ^ (D - 2) *
      MvPolynomial.X y ^ 2 +
    MvPolynomial.C (rankOnePacketCoeffYZ x y z D F) *
      MvPolynomial.X x ^ (D - 2) *
      MvPolynomial.X y *
      MvPolynomial.X z +
    MvPolynomial.C (rankOnePacketCoeffZZ x z D F) *
      MvPolynomial.X x ^ (D - 2) *
      MvPolynomial.X z ^ 2

/-- The monomial and algebraic presentations of the packet agree. -/
theorem rankOnePacketMonomialModel_eq_algebraicModel
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    rankOnePacketMonomialModel x y z D F =
      rankOnePacketAlgebraicModel x y z D F := by
  unfold rankOnePacketMonomialModel
  unfold rankOnePacketAlgebraicModel
  simp only [rankOnePacketYY,
    rankOnePacketYZ, rankOnePacketZZ,
    MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial,
    pow_one]

/-- Exact algebraic normal form of every persistent rank-one packet. -/
theorem rankOnePersistentPacket_eq_algebraicModel
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F) :
    F = rankOnePacketAlgebraicModel x y z D F := by
  calc
    F = rankOnePacketMonomialModel x y z D F :=
      rankOnePersistentPacket_eq_monomialModel
        hxy hxz hyz hpacket
    _ = rankOnePacketAlgebraicModel x y z D F :=
      rankOnePacketMonomialModel_eq_algebraicModel
        x y z D F

/-- The actual evaluated `y`-gradient of a persistent packet at the
normalised transverse point is the first quadratic-gradient expression. -/
theorem rankOnePacket_gradient_y_at_transversePoint
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F)
    (Y Z : K) :
    mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        F y =
      2 * rankOnePacketCoeffYY x y D F * Y +
        rankOnePacketCoeffYZ x y z D F * Z := by
  calc
    mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        F y =
      mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        (rankOnePacketAlgebraicModel x y z D F) y := by
          exact congrArg
            (fun G : MvPolynomial σ K =>
              mvGradientComponentAt
                (rankOnePacketTransversePoint x y z Y Z)
                G y)
            (rankOnePersistentPacket_eq_algebraicModel
              hxy hxz hyz hpacket)
    _ =
      2 * rankOnePacketCoeffYY x y D F * Y +
        rankOnePacketCoeffYZ x y z D F * Z := by
          unfold mvGradientComponentAt
          unfold rankOnePacketAlgebraicModel
          simp [rankOnePacketTransversePoint,
            hxy, hxz, hyz,
            Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
          ring_nf

/-- The actual evaluated `z`-gradient of a persistent packet at the
normalised transverse point is the second quadratic-gradient expression. -/
theorem rankOnePacket_gradient_z_at_transversePoint
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F)
    (Y Z : K) :
    mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        F z =
      rankOnePacketCoeffYZ x y z D F * Y +
        2 * rankOnePacketCoeffZZ x z D F * Z := by
  calc
    mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        F z =
      mvGradientComponentAt
        (rankOnePacketTransversePoint x y z Y Z)
        (rankOnePacketAlgebraicModel x y z D F) z := by
          exact congrArg
            (fun G : MvPolynomial σ K =>
              mvGradientComponentAt
                (rankOnePacketTransversePoint x y z Y Z)
                G z)
            (rankOnePersistentPacket_eq_algebraicModel
              hxy hxz hyz hpacket)
    _ =
      rankOnePacketCoeffYZ x y z D F * Y +
        2 * rankOnePacketCoeffZZ x z D F * Z := by
          unfold mvGradientComponentAt
          unfold rankOnePacketAlgebraicModel
          simp [rankOnePacketTransversePoint,
            hxy, hxz, hyz,
            Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
          ring_nf

/-- **Exact collision produces the Phase 93.4 transverse gradient
equations.** -/
theorem rankOnePacket_gradientZero_of_exactTransverseCollision
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (Y Z : K)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (rankOnePacketTransversePoint x y z Y Z)) :
    HasPersistentQuadraticGradientZero
      x y z D F Y Z := by
  have hzero :=
    homogeneous_exactCollision_gradient_zero
      hhom hD
      (rankOnePacketTransversePoint x y z Y Z)
      hcoll
  constructor
  · rw [← rankOnePacket_gradient_y_at_transversePoint
      hxy hxz hyz hpacket Y Z]
    exact hzero y
  · rw [← rankOnePacket_gradient_z_at_transversePoint
      hxy hxz hyz hpacket Y Z]
    exact hzero z

/-- A nonzero exact transverse collision forces a persistent rank-one
packet directly into the rigid Phase 93.4 branch. -/
theorem rankOnePersistentPacket_rigid_of_exactTransverseCollision
    [CharZero K]
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket :
      HasRankOnePersistentPacketSupport x y z D F)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (hF : F ≠ 0)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (rankOnePacketTransversePoint x y z Y Z)) :
    HasRigidRankOnePacket x y z D F := by
  have hgrad :
      HasPersistentQuadraticGradientZero
        x y z D F Y Z :=
    rankOnePacket_gradientZero_of_exactTransverseCollision
      hxy hxz hyz hpacket hhom hD Y Z hcoll
  exact
    rankOnePersistentPacket_rigid_of_nonzero_collision
      hxy hxz hyz hpacket hF
      Y Z hpoint hgrad

/-- **Canonical Smith restriction: exact collision formulation.**
The coefficient-level collision hypothesis in Phase 93.17 is replaced by
an actual exact gradient collision of the canonical restricted polynomial. -/
theorem poleMinimal_symmetricSmithRestriction_rigid_of_exactCollision
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base)
    (hnoW :
      ∀ e ∈ S,
        base e = m ->
          ¬ IsWLinearSmithPattern e)
    (hreal :
      IsSmithSubfaceRealisedInPolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hcoll :
      HasExactGradientCollision
        (smithSubfacePolynomial
          y z w
          (smithSymmetricBalancedSubface S m base)
          F)
        (fun _ => (0 : K))
        (rankOnePacketTransversePoint x y z Y Z)) :
    HasRigidRankOnePacket
      x y z D
      (smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F) := by
  let T :=
    smithSymmetricBalancedSubface S m base
  let G :=
    smithSubfacePolynomial y z w T F
  have hpacketData :=
    poleMinimal_symmetricSmithRestriction_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom
      S m base hpole hmin hattain hshape hnoW
  have hGhom :
      G.IsHomogeneous D := by
    dsimp [G, T]
    exact
      smithSubfacePolynomial_isHomogeneous
        y z w
        (smithSymmetricBalancedSubface S m base)
        hhom
  have hGne :
      G ≠ 0 := by
    dsimp [G, T]
    exact
      smithSubfacePolynomial_ne_zero_of_nonempty_realised
        y z w
        (smithSymmetricBalancedSubface S m base)
        F
        hpacketData.1
        hreal
  have hGpacket :
      HasRankOnePersistentPacketSupport
        x y z D G := by
    dsimp [G, T]
    exact hpacketData.2
  apply
    rankOnePersistentPacket_rigid_of_exactTransverseCollision
      hxy hxz hyz
      hGpacket hGhom hD hGne
      Y Z hpoint
  simpa [G, T] using hcoll

end

end HC4.Newton
