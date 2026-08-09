import HC4.Newton.RankTwoHomogeneousPacketClassification
import Mathlib.Tactic

/-!
# Rank-one persistent packet support

The rank-one corank-entry branch is expected to produce a first persistent
homogeneous packet of the form

    x^(D-2) * q(y,z),

where `q` is a binary quadratic form.

This file formalises the support-theoretic content of that statement.
Rather than assuming a factorisation syntax, we record the exact exponent
conditions on every nonzero monomial:

* longitudinal exponent `x` is `D-2`;
* transverse degree in `y,z` is exactly `2`;
* every other variable has exponent zero.

For pairwise distinct `x,y,z`, those conditions force every support
monomial to be exactly one of

    x^(D-2) y^2,
    x^(D-2) y z,
    x^(D-2) z^2.

Thus the first persistent packet is reduced canonically to three scalar
coefficients.  The next phase can package those coefficients as the binary
quadratic `q` and classify its determinant/rank alternatives.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Support predicate for a rank-one persistent packet
`x^(D-2) * q(y,z)`. -/
def HasRankOnePersistentPacketSupport
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 ->
    d x = D - 2 ∧
    d y + d z = 2 ∧
    ∀ t, t ≠ x -> t ≠ y -> t ≠ z -> d t = 0

/-- Canonical exponent vector for `x^(D-2) y^2`. -/
def rankOnePacketYY
    (x y : σ)
    (D : ℕ) : σ →₀ ℕ :=
  Finsupp.single x (D - 2) +
    Finsupp.single y 2

/-- Canonical exponent vector for `x^(D-2) y z`. -/
def rankOnePacketYZ
    (x y z : σ)
    (D : ℕ) : σ →₀ ℕ :=
  Finsupp.single x (D - 2) +
    Finsupp.single y 1 +
    Finsupp.single z 1

/-- Canonical exponent vector for `x^(D-2) z^2`. -/
def rankOnePacketZZ
    (x z : σ)
    (D : ℕ) : σ →₀ ℕ :=
  Finsupp.single x (D - 2) +
    Finsupp.single z 2

/-- Arithmetic classification of a binary quadratic exponent pair. -/
theorem nat_pair_sum_two_cases
    (a b : ℕ)
    (h : a + b = 2) :
    (a = 2 ∧ b = 0) ∨
    (a = 1 ∧ b = 1) ∨
    (a = 0 ∧ b = 2) := by
  omega

/-- If a multi-index has the persistent-packet exponent conditions and
transverse exponents `(2,0)`, it is the `YY` packet index. -/
theorem eq_rankOnePacketYY
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {d : σ →₀ ℕ}
    (hx : d x = D - 2)
    (hy : d y = 2)
    (hz : d z = 0)
    (hother :
      ∀ t, t ≠ x -> t ≠ y -> t ≠ z -> d t = 0) :
    d = rankOnePacketYY x y D := by
  classical
  ext t
  by_cases htx : t = x
  · subst t
    simp [rankOnePacketYY, hx, hxy]
  · by_cases hty : t = y
    · subst t
      simp [rankOnePacketYY, hy, hxy]
    · by_cases htz : t = z
      · subst t
        simp [rankOnePacketYY, hz, hxz, hyz]
      · have ht0 : d t = 0 := hother t htx hty htz
        simp [rankOnePacketYY, htx, hty, ht0]

/-- The `(1,1)` transverse exponent case is the `YZ` packet index. -/
theorem eq_rankOnePacketYZ
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {d : σ →₀ ℕ}
    (hx : d x = D - 2)
    (hy : d y = 1)
    (hz : d z = 1)
    (hother :
      ∀ t, t ≠ x -> t ≠ y -> t ≠ z -> d t = 0) :
    d = rankOnePacketYZ x y z D := by
  classical
  ext t
  by_cases htx : t = x
  · subst t
    simp [rankOnePacketYZ, hx, hxy, hxz]
  · by_cases hty : t = y
    · subst t
      simp [rankOnePacketYZ, hy, hxy, hyz]
    · by_cases htz : t = z
      · subst t
        simp [rankOnePacketYZ, hz, hxz, hyz]
      · have ht0 : d t = 0 := hother t htx hty htz
        simp [rankOnePacketYZ, htx, hty, htz, ht0]

/-- The `(0,2)` transverse exponent case is the `ZZ` packet index. -/
theorem eq_rankOnePacketZZ
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {d : σ →₀ ℕ}
    (hx : d x = D - 2)
    (hy : d y = 0)
    (hz : d z = 2)
    (hother :
      ∀ t, t ≠ x -> t ≠ y -> t ≠ z -> d t = 0) :
    d = rankOnePacketZZ x z D := by
  classical
  ext t
  by_cases htx : t = x
  · subst t
    simp [rankOnePacketZZ, hx, hxz]
  · by_cases hty : t = y
    · subst t
      simp [rankOnePacketZZ, hy, hxy, hyz]
    · by_cases htz : t = z
      · subst t
        simp [rankOnePacketZZ, hz, hxz]
      · have ht0 : d t = 0 := hother t htx hty htz
        simp [rankOnePacketZZ, htx, htz, ht0]

/-- **Persistent packet support trichotomy.**
Every nonzero monomial of a rank-one persistent packet is one of the three
binary-quadratic monomials. -/
theorem rankOnePersistentPacket_support_cases
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    {d : σ →₀ ℕ}
    (hd : MvPolynomial.coeff d F ≠ 0) :
    d = rankOnePacketYY x y D ∨
    d = rankOnePacketYZ x y z D ∨
    d = rankOnePacketZZ x z D := by
  rcases hpacket d hd with ⟨hx, hsum, hother⟩
  rcases nat_pair_sum_two_cases (d y) (d z) hsum with
    hYY | hYZ | hZZ
  · left
    exact eq_rankOnePacketYY
      hxy hxz hyz hx hYY.1 hYY.2 hother
  · right
    left
    exact eq_rankOnePacketYZ
      hxy hxz hyz hx hYZ.1 hYZ.2 hother
  · right
    right
    exact eq_rankOnePacketZZ
      hxy hxz hyz hx hZZ.1 hZZ.2 hother

/-- Coefficients outside the three canonical packet indices vanish. -/
theorem coeff_eq_zero_outside_rankOnePacket
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (d : σ →₀ ℕ)
    (hYY : d ≠ rankOnePacketYY x y D)
    (hYZ : d ≠ rankOnePacketYZ x y z D)
    (hZZ : d ≠ rankOnePacketZZ x z D) :
    MvPolynomial.coeff d F = 0 := by
  by_contra hd
  rcases rankOnePersistentPacket_support_cases
      hxy hxz hyz hpacket hd with h | h | h
  · exact hYY h
  · exact hYZ h
  · exact hZZ h

/-- The three scalar coefficients of the persistent binary quadratic
packet. -/
def rankOnePacketCoeffYY
    (x y : σ) (D : ℕ)
    (F : MvPolynomial σ K) : K :=
  MvPolynomial.coeff (rankOnePacketYY x y D) F

def rankOnePacketCoeffYZ
    (x y z : σ) (D : ℕ)
    (F : MvPolynomial σ K) : K :=
  MvPolynomial.coeff (rankOnePacketYZ x y z D) F

def rankOnePacketCoeffZZ
    (x z : σ) (D : ℕ)
    (F : MvPolynomial σ K) : K :=
  MvPolynomial.coeff (rankOnePacketZZ x z D) F

end

end HC4.Newton
