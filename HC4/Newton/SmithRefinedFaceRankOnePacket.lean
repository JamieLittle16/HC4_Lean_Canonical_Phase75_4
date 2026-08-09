import HC4.Newton.SmithSymmetricBalanceRefinement
import HC4.Newton.RankOnePersistentPacket
import Mathlib.Tactic

/-!
# Symmetric Smith refined face to rank-one persistent packet

Phase 93.15 proves that the symmetric pole-minimal refinement is nonempty
and, after excluding the `w`-linear zero-grade blocker, its Smith exponent
triples are exactly

    (b,c,d) = (0,2,0), (1,1,0), (2,0,0).

This file restores the longitudinal exponent.

For a homogeneous degree-`D` polynomial in a genuine four-coordinate chart
`x,y,z,w`, those three transverse patterns imply

    exponent(y) + exponent(z) = 2,
    exponent(w) = 0.

Homogeneity gives total degree `D`, hence the remaining longitudinal
exponent is exactly

    exponent(x) = D - 2.

Since every coordinate other than `x,y,z` is necessarily `w`, its exponent
vanishes.  These are precisely the conditions in the already-green
`HasRankOnePersistentPacketSupport` predicate from Phase 92.

Thus the Smith first-wall/refinement machinery now lands directly in the
rank-one quadratic packet model, modulo the global extraction step that
constructs the polynomial supported on the refined subface.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Project a polynomial multi-index to the Smith-relevant transverse
exponent triple `(y,z,w)`. -/
def smithSupportExponentOf
    (y z w : σ)
    (d : σ →₀ ℕ) : SmithSupportExponent where
  b := d y
  c := d z
  d := d w

@[simp] theorem smithSupportExponentOf_b
    (y z w : σ)
    (d : σ →₀ ℕ) :
    (smithSupportExponentOf y z w d).b = d y := rfl

@[simp] theorem smithSupportExponentOf_c
    (y z w : σ)
    (d : σ →₀ ℕ) :
    (smithSupportExponentOf y z w d).c = d z := rfl

@[simp] theorem smithSupportExponentOf_d
    (y z w : σ)
    (d : σ →₀ ℕ) :
    (smithSupportExponentOf y z w d).d = d w := rfl

/-- A polynomial is supported on a specified Smith exponent subface. -/
def IsSupportedOnSmithSubface
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 ->
    smithSupportExponentOf y z w d ∈ T

/-- Four named coordinates exhaust the ambient coordinate type. -/
def IsFourCoordinateChart
    (x y z w : σ) : Prop :=
  ∀ t : σ, t = x ∨ t = y ∨ t = z ∨ t = w

/-- The three symmetric Smith target exponent patterns imply transverse
degree two and zero `w`-exponent. -/
theorem smithQuadraticPattern_transverseDegree
    {y z w : σ}
    {d : σ →₀ ℕ}
    (hquad :
      ((smithSupportExponentOf y z w d).b = 0 ∧
       (smithSupportExponentOf y z w d).c = 2 ∧
       (smithSupportExponentOf y z w d).d = 0) ∨
      ((smithSupportExponentOf y z w d).b = 1 ∧
       (smithSupportExponentOf y z w d).c = 1 ∧
       (smithSupportExponentOf y z w d).d = 0) ∨
      ((smithSupportExponentOf y z w d).b = 2 ∧
       (smithSupportExponentOf y z w d).c = 0 ∧
       (smithSupportExponentOf y z w d).d = 0)) :
    d y + d z = 2 ∧ d w = 0 := by
  rcases hquad with hzz | hyz | hyy
  · change d y = 0 ∧ d z = 2 ∧ d w = 0 at hzz
    exact ⟨by omega, hzz.2.2⟩
  · change d y = 1 ∧ d z = 1 ∧ d w = 0 at hyz
    exact ⟨by omega, hyz.2.2⟩
  · change d y = 2 ∧ d z = 0 ∧ d w = 0 at hyy
    exact ⟨by omega, hyy.2.2⟩

/-- In a four-coordinate chart, every multi-index decomposes into the four
coordinate singles. -/
theorem finsupp_eq_fourCoordinateSum
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (d : σ →₀ ℕ) :
    d =
      Finsupp.single x (d x) +
      Finsupp.single y (d y) +
      Finsupp.single z (d z) +
      Finsupp.single w (d w) := by
  classical
  apply Finsupp.ext
  intro t
  rcases hchart t with htx | hty | htz | htw
  · subst t
    simp [hxy, hxz, hxw, Ne.symm hxy, Ne.symm hxz, Ne.symm hxw]
  · subst t
    simp [hxy, hyz, hyw, Ne.symm hxy, Ne.symm hyz, Ne.symm hyw]
  · subst t
    simp [hxz, hyz, hzw, Ne.symm hxz, Ne.symm hyz, Ne.symm hzw]
  · subst t
    simp [hxw, hyw, hzw, Ne.symm hxw, Ne.symm hyw, Ne.symm hzw]

/-- Homogeneity plus the transverse quadratic Smith pattern restores the
longitudinal exponent `D-2`. -/
theorem homogeneous_smithQuadraticPattern_longitudinalExponent
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (d : σ →₀ ℕ)
    (hd : MvPolynomial.coeff d F ≠ 0)
    (hyzdeg : d y + d z = 2)
    (hw : d w = 0) :
    d x = D - 2 := by
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hd
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      x y z w hxy hxz hxw hyz hyw hzw hchart d
  rw [hdecomp] at hdeg
  have htotal :
      d x + d y + d z + d w = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  omega

/-- Every coordinate outside `x,y,z` is `w` in a four-coordinate chart,
so zero `w` exponent gives the packet's off-axis support condition. -/
theorem smithQuadraticPattern_otherExponent_zero
    (x y z w : σ)
    (hchart : IsFourCoordinateChart x y z w)
    (d : σ →₀ ℕ)
    (hw : d w = 0) :
    ∀ t, t ≠ x -> t ≠ y -> t ≠ z -> d t = 0 := by
  intro t htx hty htz
  rcases hchart t with h | h | h | h
  · exact False.elim (htx h)
  · exact False.elim (hty h)
  · exact False.elim (htz h)
  · subst t
    exact hw

/-- **Refined Smith face to persistent packet adapter.**
A homogeneous polynomial whose support projects into a Smith subface
consisting only of the three transverse quadratic exponent patterns has
rank-one persistent packet support. -/
theorem rankOnePersistentPacketSupport_of_smithQuadraticSubface
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
    (T : Finset SmithSupportExponent)
    (hF :
      IsSupportedOnSmithSubface y z w T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    HasRankOnePersistentPacketSupport x y z D F := by
  intro d hd
  have heT :
      smithSupportExponentOf y z w d ∈ T :=
    hF d hd
  have hpattern :=
    hquad (smithSupportExponentOf y z w d) heT
  have htrans :
      d y + d z = 2 ∧ d w = 0 :=
    smithQuadraticPattern_transverseDegree hpattern
  refine
    ⟨homogeneous_smithQuadraticPattern_longitudinalExponent
        hhom x y z w hxy hxz hxw hyz hyw hzw
        hchart d hd htrans.1 htrans.2,
      htrans.1,
      ?_⟩
  exact
    smithQuadraticPattern_otherExponent_zero
      x y z w hchart d htrans.2

/-- **Pole-minimal symmetric Smith face lands in the Phase 92 packet
model.**
If `F` is the homogeneous polynomial supported on the symmetric refined
subface, pole minimality and the corrected first-wall classification imply
both that the subface is nonempty and that `F` satisfies the green
rank-one persistent packet support predicate. -/
theorem poleMinimal_symmetricSmithRefinement_rankOnePacket
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
    (hF :
      IsSupportedOnSmithSubface
        y z w
        (smithSymmetricBalancedSubface S m base)
        F) :
    (smithSymmetricBalancedSubface S m base).Nonempty ∧
      HasRankOnePersistentPacketSupport x y z D F := by
  rcases
      poleMinimal_symmetricSmithRefinement_quadratic
        S m base hpole hmin hattain hshape hnoW with
    ⟨hnonempty, hquad⟩
  refine ⟨hnonempty, ?_⟩
  exact
    rankOnePersistentPacketSupport_of_smithQuadraticSubface
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom
      (smithSymmetricBalancedSubface S m base)
      hF hquad

end

end HC4.Newton
