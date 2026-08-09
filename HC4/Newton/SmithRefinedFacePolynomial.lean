import HC4.Newton.SmithRefinedFaceRankOnePacket
import HC4.Newton.SmithCollisionQuadraticRankOne
import HC4.Newton.RankOnePacketReentry
import HC4.Newton.MixedDepartureAdapter
import Mathlib.Tactic

/-!
# Constructing the symmetric refined-face polynomial

Phase 93.16 proves that any homogeneous polynomial whose support projects
into the symmetric Smith refined subface is a rank-one persistent packet.
This file removes that support hypothesis by constructing the polynomial
canonically.

For a finite Smith subface `T`, define `smithSubfacePolynomial y z w T F`
by filtering the coefficients of `F` and retaining exactly those monomials
whose transverse Smith exponent triple lies in `T`.

The construction has three formal properties.

1. Its coefficients are exactly the corresponding coefficients of `F` on
   `T`, and zero off `T`.
2. If `F` is ordinary homogeneous of degree `D`, the filtered polynomial is
   homogeneous of the same degree.
3. It is automatically `IsSupportedOnSmithSubface y z w T`.

Consequently the green Phase 93.15/93.16 chain applies to this canonical
restriction without an externally supplied refined-face polynomial.

If the refined Smith subface is realised by actual support monomials of
`F`, nonemptiness of the Smith subface also implies the restricted
polynomial is nonzero.

Finally, adding exactly the geometric first-nonzero-wall hypothesis from
Phase 93.4 -- a nonzero transverse point `(Y,Z)` with vanishing leading
quadratic gradient -- immediately gives `HasRigidRankOnePacket`.

Thus after this module the remaining local/global interface is the actual
restart geometry producing that nonzero transverse wall and its leading
gradient equations; the refined polynomial itself no longer has to be
postulated.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The Smith projection of the actual support of `F`. -/
noncomputable def smithProjectedSupport
    (y z w : σ)
    (F : MvPolynomial σ K) :
    Finset SmithSupportExponent := by
  classical
  exact F.support.image (smithSupportExponentOf y z w)

/-- Restrict `F` to the monomials whose Smith projection lies in `T`. -/
noncomputable def smithSubfacePolynomial
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K) :
    MvPolynomial σ K := by
  classical
  exact
    Finsupp.filter
      (fun d : σ →₀ ℕ =>
        smithSupportExponentOf y z w d ∈ T)
      F

/-- Coefficients of the Smith-subface restriction are unchanged on `T`
and vanish off `T`. -/
@[simp] theorem coeff_smithSubfacePolynomial
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K)
    (d : σ →₀ ℕ) :
    MvPolynomial.coeff d
        (smithSubfacePolynomial y z w T F) =
      if smithSupportExponentOf y z w d ∈ T
      then MvPolynomial.coeff d F
      else 0 := by
  classical
  unfold smithSubfacePolynomial
  exact
    Finsupp.filter_apply
      (fun d : σ →₀ ℕ =>
        smithSupportExponentOf y z w d ∈ T)
      F d

/-- The canonical restriction is automatically supported on its Smith
subface. -/
theorem smithSubfacePolynomial_supported
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K) :
    IsSupportedOnSmithSubface
      y z w T
      (smithSubfacePolynomial y z w T F) := by
  intro d hd
  by_contra hnot
  have hcoeff := hd
  rw [coeff_smithSubfacePolynomial] at hcoeff
  simp [hnot] at hcoeff

/-- Filtering to a Smith subface preserves ordinary homogeneity. -/
theorem smithSubfacePolynomial_isHomogeneous
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D) :
    (smithSubfacePolynomial y z w T F).IsHomogeneous D := by
  intro d hd
  rw [coeff_smithSubfacePolynomial] at hd
  by_cases hmem :
      smithSupportExponentOf y z w d ∈ T
  · simp [hmem] at hd
    exact hhom hd
  · simp [hmem] at hd

/-- Every element of the projected support is represented by an actual
nonzero coefficient of `F`. -/
theorem smithProjectedSupport_realised
    (y z w : σ)
    (F : MvPolynomial σ K) :
    ∀ e ∈ smithProjectedSupport y z w F,
      ∃ d : σ →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 ∧
        smithSupportExponentOf y z w d = e := by
  classical
  intro e he
  unfold smithProjectedSupport at he
  rcases Finset.mem_image.mp he with
    ⟨d, hd, hde⟩
  refine
    ⟨d,
      MvPolynomial.mem_support_iff.mp hd,
      hde⟩

/-- A finite Smith subface is realised in `F` when every one of its Smith
exponents comes from an actual nonzero monomial of `F`. -/
def IsSmithSubfaceRealisedInPolynomial
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K) : Prop :=
  ∀ e ∈ T,
    ∃ d : σ →₀ ℕ,
      MvPolynomial.coeff d F ≠ 0 ∧
      smithSupportExponentOf y z w d = e

/-- Inclusion in the projected support is enough for realisation. -/
theorem smithSubfaceRealised_of_subset_projectedSupport
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K)
    (hsub :
      T ⊆ smithProjectedSupport y z w F) :
    IsSmithSubfaceRealisedInPolynomial y z w T F := by
  intro e heT
  exact
    smithProjectedSupport_realised
      y z w F e (hsub heT)

/-- A nonempty realised Smith subface gives a nonzero canonical restricted
polynomial. -/
theorem smithSubfacePolynomial_ne_zero_of_nonempty_realised
    (y z w : σ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial σ K)
    (hne : T.Nonempty)
    (hreal :
      IsSmithSubfaceRealisedInPolynomial y z w T F) :
    smithSubfacePolynomial y z w T F ≠ 0 := by
  rcases hne with ⟨e, heT⟩
  rcases hreal e heT with
    ⟨d, hd, hproj⟩
  intro hzero
  have hcoeffzero :
      MvPolynomial.coeff d
        (smithSubfacePolynomial y z w T F) = 0 := by
    rw [hzero]
    simp
  rw [coeff_smithSubfacePolynomial] at hcoeffzero
  rw [hproj] at hcoeffzero
  simp [heT] at hcoeffzero
  exact hd hcoeffzero

/-- **Canonical symmetric restriction lands in the Phase 92 packet
model.**
No externally supplied refined-face polynomial is required. -/
theorem poleMinimal_symmetricSmithRestriction_rankOnePacket
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
          ¬ IsWLinearSmithPattern e) :
    let T :=
      smithSymmetricBalancedSubface S m base
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport
        x y z D
        (smithSubfacePolynomial y z w T F) := by
  dsimp
  let T :=
    smithSymmetricBalancedSubface S m base
  have hhomT :
      (smithSubfacePolynomial y z w T F).IsHomogeneous D :=
    smithSubfacePolynomial_isHomogeneous
      y z w T hhom
  have hsuppT :
      IsSupportedOnSmithSubface
        y z w T
        (smithSubfacePolynomial y z w T F) :=
    smithSubfacePolynomial_supported
      y z w T F
  exact
    poleMinimal_symmetricSmithRefinement_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhomT
      S m base hpole hmin hattain hshape hnoW
      hsuppT

/-- **Canonical refined packet rigidity at the first nonzero transverse
wall.**
Once the actual restart geometry supplies a nonzero wall point and the
leading transverse gradient equations, the canonical symmetric restriction
is forced into the green Phase 93.4 rigid square/axis branch. -/
theorem poleMinimal_symmetricSmithRestriction_rigid_of_nonzero_collision
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
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D
        (smithSubfacePolynomial
          y z w
          (smithSymmetricBalancedSubface S m base)
          F)
        Y Z) :
    HasRigidRankOnePacket
      x y z D
      (smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F) := by
  have hpacket :=
    poleMinimal_symmetricSmithRestriction_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom
      S m base hpole hmin hattain hshape hnoW
  have hFne :
      smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface S m base)
        F ≠ 0 :=
    smithSubfacePolynomial_ne_zero_of_nonempty_realised
      y z w
      (smithSymmetricBalancedSubface S m base)
      F
      hpacket.1
      hreal
  exact
    rankOnePersistentPacket_rigid_of_nonzero_collision
      hxy hxz hyz
      hpacket.2
      hFne
      Y Z hpoint hgrad


/-! ## Exact-axis collision discharges the abstract low-pattern hypotheses

The Smith balance/refinement layer above was deliberately factored through
abstract hypotheses `HasGeneralSurvivingSmithFaceShape` and exclusion of the
`w`-linear zero-grade pattern.  At an actual homogeneous exact axis collision
those hypotheses are not additional assumptions.

Indeed, a projected support exponent with one of the four low Smith patterns
lifts, by ordinary homogeneity and the four-coordinate chart, to exactly one
of the already-excluded axis blockers

* `x^D`,
* `x^(D-1) z`,
* `x^(D-1) y`,
* `x^(D-1) w`.

The following lemmas make that reconstruction explicit and then package the
result in the precise interfaces consumed by the symmetric Smith refinement.
-/

/-- A projected pure-longitudinal Smith support exponent reconstructs the
actual monomial `x^D`. -/
theorem homogeneous_projectedSupport_pureLongitudinal_forces_blocker
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
    {e : SmithSupportExponent}
    (he : e ∈ smithProjectedSupport y z w F)
    (hpat : IsPureLongitudinalSmithPattern e) :
    longitudinalAxisBlockerExponent x D ∈ F.support := by
  rcases smithProjectedSupport_realised y z w F e he with
    ⟨d, hcoeff, hproj⟩
  have hsupport : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hy : d y = 0 := by
    have := hpat.1
    rw [← hproj] at this
    exact this
  have hz : d z = 0 := by
    have := hpat.2.1
    rw [← hproj] at this
    exact this
  have hw : d w = 0 := by
    have := hpat.2.2
    rw [← hproj] at this
    exact this
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      x y z w hxy hxz hxw hyz hyw hzw hchart d
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeff
  rw [hdecomp] at hdeg
  have htotal : d x + d y + d z + d w = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  have hdx : d x = D := by
    omega
  have hdblock :
      d = longitudinalAxisBlockerExponent x D := by
    calc
      d =
          Finsupp.single x (d x) +
          Finsupp.single y (d y) +
          Finsupp.single z (d z) +
          Finsupp.single w (d w) := hdecomp
      _ = longitudinalAxisBlockerExponent x D := by
        simp [hy, hz, hw, hdx, longitudinalAxisBlockerExponent]
  rw [← hdblock]
  exact hsupport

/-- A projected low negative-first Smith exponent `(b,c,d)=(0,1,0)`
reconstructs the actual blocker `x^(D-1) z`. -/
theorem homogeneous_projectedSupport_lowNegativeFirst_forces_blocker
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
    {e : SmithSupportExponent}
    (he : e ∈ smithProjectedSupport y z w F)
    (hpat : IsLowNegativeFirstSmithPattern e) :
    transverseAxisBlockerExponent x z D ∈ F.support := by
  rcases smithProjectedSupport_realised y z w F e he with
    ⟨d, hcoeff, hproj⟩
  have hsupport : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hy : d y = 0 := by
    have := hpat.1
    rw [← hproj] at this
    exact this
  have hz : d z = 1 := by
    have := hpat.2.1
    rw [← hproj] at this
    exact this
  have hw : d w = 0 := by
    have := hpat.2.2
    rw [← hproj] at this
    exact this
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      x y z w hxy hxz hxw hyz hyw hzw hchart d
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeff
  rw [hdecomp] at hdeg
  have htotal : d x + d y + d z + d w = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  have hdx : d x = D - 1 := by
    omega
  have hdblock :
      d = transverseAxisBlockerExponent x z D := by
    calc
      d =
          Finsupp.single x (d x) +
          Finsupp.single y (d y) +
          Finsupp.single z (d z) +
          Finsupp.single w (d w) := hdecomp
      _ = transverseAxisBlockerExponent x z D := by
        simp [hy, hz, hw, hdx, transverseAxisBlockerExponent, add_assoc]
  rw [← hdblock]
  exact hsupport

/-- A projected low negative-second Smith exponent `(b,c,d)=(1,0,0)`
reconstructs the actual blocker `x^(D-1) y`. -/
theorem homogeneous_projectedSupport_lowNegativeSecond_forces_blocker
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
    {e : SmithSupportExponent}
    (he : e ∈ smithProjectedSupport y z w F)
    (hpat : IsLowNegativeSecondSmithPattern e) :
    transverseAxisBlockerExponent x y D ∈ F.support := by
  rcases smithProjectedSupport_realised y z w F e he with
    ⟨d, hcoeff, hproj⟩
  have hsupport : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hy : d y = 1 := by
    have := hpat.1
    rw [← hproj] at this
    exact this
  have hz : d z = 0 := by
    have := hpat.2.1
    rw [← hproj] at this
    exact this
  have hw : d w = 0 := by
    have := hpat.2.2
    rw [← hproj] at this
    exact this
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      x y z w hxy hxz hxw hyz hyw hzw hchart d
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeff
  rw [hdecomp] at hdeg
  have htotal : d x + d y + d z + d w = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  have hdx : d x = D - 1 := by
    omega
  have hdblock :
      d = transverseAxisBlockerExponent x y D := by
    calc
      d =
          Finsupp.single x (d x) +
          Finsupp.single y (d y) +
          Finsupp.single z (d z) +
          Finsupp.single w (d w) := hdecomp
      _ = transverseAxisBlockerExponent x y D := by
        simp [hy, hz, hw, hdx, transverseAxisBlockerExponent, add_assoc]
  rw [← hdblock]
  exact hsupport

/-- A projected `w`-linear zero-grade Smith exponent reconstructs the
actual blocker `x^(D-1) w`. -/
theorem homogeneous_projectedSupport_wLinear_forces_blocker
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
    {e : SmithSupportExponent}
    (he : e ∈ smithProjectedSupport y z w F)
    (hpat : IsWLinearSmithPattern e) :
    transverseAxisBlockerExponent x w D ∈ F.support := by
  rcases smithProjectedSupport_realised y z w F e he with
    ⟨d, hcoeff, hproj⟩
  have hsupport : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hy : d y = 0 := by
    have := hpat.1
    rw [← hproj] at this
    exact this
  have hz : d z = 0 := by
    have := hpat.2.1
    rw [← hproj] at this
    exact this
  have hw : d w = 1 := by
    have := hpat.2.2
    rw [← hproj] at this
    exact this
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      x y z w hxy hxz hxw hyz hyw hzw hchart d
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeff
  rw [hdecomp] at hdeg
  have htotal : d x + d y + d z + d w = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  have hdx : d x = D - 1 := by
    omega
  have hdblock :
      d = transverseAxisBlockerExponent x w D := by
    calc
      d =
          Finsupp.single x (d x) +
          Finsupp.single y (d y) +
          Finsupp.single z (d z) +
          Finsupp.single w (d w) := hdecomp
      _ = transverseAxisBlockerExponent x w D := by
        simp [hy, hz, hw, hdx, transverseAxisBlockerExponent, add_assoc]
  rw [← hdblock]
  exact hsupport

/-- **Exact collision removes all three negative low Smith patterns from
actual projected support.** -/
theorem homogeneous_exactAxisCollision_projectedSupport_noNegativeLowPatterns
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x)) :
    ∀ e ∈ smithProjectedSupport y z w F,
      HasNoNegativeLowSmithPatterns e := by
  have hlow :=
    homogeneous_exactAxisCollision_no_lowBlockers
      hhom hD x hcoll
  intro e he
  refine ⟨?_, ?_, ?_⟩
  · intro hpat
    exact hlow.1
      (homogeneous_projectedSupport_pureLongitudinal_forces_blocker
        x y z w hxy hxz hxw hyz hyw hzw hchart hhom he hpat)
  · intro hpat
    exact (hlow.2 z (Ne.symm hxz))
      (homogeneous_projectedSupport_lowNegativeFirst_forces_blocker
        x y z w hxy hxz hxw hyz hyw hzw hchart hhom he hpat)
  · intro hpat
    exact (hlow.2 y (Ne.symm hxy))
      (homogeneous_projectedSupport_lowNegativeSecond_forces_blocker
        x y z w hxy hxz hxw hyz hyw hzw hchart hhom he hpat)

/-- **Exact collision also removes the `w`-linear zero-grade blocker from
actual projected support.** -/
theorem homogeneous_exactAxisCollision_projectedSupport_noWLinear
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x)) :
    ∀ e ∈ smithProjectedSupport y z w F,
      ¬ IsWLinearSmithPattern e := by
  have hlow :=
    homogeneous_exactAxisCollision_no_lowBlockers
      hhom hD x hcoll
  intro e he hpat
  exact (hlow.2 w (Ne.symm hxw))
    (homogeneous_projectedSupport_wLinear_forces_blocker
      x y z w hxy hxz hxw hyz hyw hzw hchart hhom he hpat)

/-- The abstract general surviving-face classification required by the Smith
balance layer is automatic on the actual projected support of a homogeneous
exact axis collision. -/
theorem homogeneous_exactAxisCollision_generalSurvivingSmithFaceShape
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) :
    HasGeneralSurvivingSmithFaceShape
      (smithProjectedSupport y z w F) m base := by
  apply generalSurvivingSmithFaceShape_of_noNegativeLowPatterns
  intro e he _
  exact
    homogeneous_exactAxisCollision_projectedSupport_noNegativeLowPatterns
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll e he

/-- **Collision-to-Smith-input package.**
For the actual projected support, exact homogeneous axis collision supplies
both abstract hypotheses consumed by the symmetric Smith refinement: the
general surviving-grade shape and exclusion of the `w`-linear old-face
pattern. -/
theorem homogeneous_exactAxisCollision_smithRefinementInputs
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) :
    HasGeneralSurvivingSmithFaceShape
        (smithProjectedSupport y z w F) m base ∧
      (∀ e ∈ smithProjectedSupport y z w F,
        base e = m -> ¬ IsWLinearSmithPattern e) := by
  constructor
  · exact
      homogeneous_exactAxisCollision_generalSurvivingSmithFaceShape
        x y z w hxy hxz hxw hyz hyw hzw hchart
        hhom hD hcoll m base
  · intro e he _
    exact
      homogeneous_exactAxisCollision_projectedSupport_noWLinear
        x y z w hxy hxz hxw hyz hyw hzw hchart
        hhom hD hcoll e he

/-- **Actual-collision Smith refinement lands in the persistent packet model.**
This removes the two abstract first-wall classification hypotheses from
`poleMinimal_symmetricSmithRestriction_rankOnePacket` when `S` is the actual
projected support of `F`. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rankOnePacket
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport
        x y z D
        (smithSubfacePolynomial y z w T F) := by
  dsimp
  have hinputs :=
    homogeneous_exactAxisCollision_smithRefinementInputs
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base
  exact
    poleMinimal_symmetricSmithRestriction_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom
      (smithProjectedSupport y z w F) m base
      hpole hmin hattain hinputs.1 hinputs.2


/-! ## Canonical realisation and the packaged Smith rank-one entrance

For the actual projected support there is no additional realisation
hypothesis to discharge.  The symmetric balanced subface is literally a
`Finset.filter` of that projected support, hence each of its exponents is
represented by a genuine nonzero coefficient of the original polynomial.

Combining this observation with the exact-collision wrapper above removes
all auxiliary Smith-face hypotheses from the local RS1 conclusion.  The
only remaining geometric input is exactly the one stated in the restart
manuscript: a nonzero transverse first-wall point at which the leading
quadratic gradient vanishes.
-/

/-- Every symmetric balanced subface is a sub-finset of the support set from
which it was filtered. -/
theorem smithSymmetricBalancedSubface_subset
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) :
    smithSymmetricBalancedSubface S m base ⊆ S := by
  intro e he
  exact (mem_smithSymmetricBalancedSubface.mp he).1

/-- When the ambient Smith set is the actual projected support of `F`, its
symmetric balanced subface is automatically realised by genuine monomials
of `F`. -/
theorem smithSymmetricBalancedSubface_realisedInPolynomial
    (y z w : σ)
    (F : MvPolynomial σ K)
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ) :
    IsSmithSubfaceRealisedInPolynomial
      y z w
      (smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base)
      F := by
  apply smithSubfaceRealised_of_subset_projectedSupport
  exact
    smithSymmetricBalancedSubface_subset
      (smithProjectedSupport y z w F) m base

/-- **Exact-collision Smith entrance, nonzero packet form.**

Pole minimality, attainment of the old minimum, homogeneity and the exact
axis collision are enough to construct a nonempty, nonzero canonical Smith
restriction with rank-one persistent packet support.  In particular there
is no separate `hshape`, `hnoW`, or realisation assumption left at this
stage. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonzero_rankOnePacket
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport
        x y z D
        (smithSubfacePolynomial y z w T F) ∧
      smithSubfacePolynomial y z w T F ≠ 0 := by
  dsimp
  have hpacket :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  have hreal :
      IsSmithSubfaceRealisedInPolynomial
        y z w
        (smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base)
        F :=
    smithSymmetricBalancedSubface_realisedInPolynomial
      y z w F m base
  have hne :
      smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base)
        F ≠ 0 :=
    smithSubfacePolynomial_ne_zero_of_nonempty_realised
      y z w
      (smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base)
      F hpacket.1 hreal
  exact ⟨hpacket.1, hpacket.2, hne⟩

/-- The remaining first-wall geometric certificate after the finite Smith
balance and exact-collision exclusions have been discharged. -/
def HasNonzeroSmithFirstWallGradientCertificate
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  ∃ Y Z : K,
    (Y ≠ 0 ∨ Z ≠ 0) ∧
      HasPersistentQuadraticGradientZero
        x y z D F Y Z

/-- **Packaged local RS1 conclusion.**

For an exact homogeneous axis collision in a pole-minimal Smith chart, the
finite first-wall classification, balance, homogeneous refinement,
canonical realisation and quadratic rank-one argument are now one theorem.
The only remaining local geometric input is a nonzero first-wall point with
vanishing leading transverse gradient. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rigid_of_firstWallCertificate
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (hwall :
      HasNonzeroSmithFirstWallGradientCertificate
        x y z D
        (smithSubfacePolynomial
          y z w
          (smithSymmetricBalancedSubface
            (smithProjectedSupport y z w F) m base)
          F)) :
    HasRigidRankOnePacket
      x y z D
      (smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base)
        F) := by
  have hpacket :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonzero_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  rcases hwall with ⟨Y, Z, hpoint, hgrad⟩
  exact
    rankOnePersistentPacket_rigid_of_nonzero_collision
      hxy hxz hyz
      hpacket.2.1
      hpacket.2.2
      Y Z hpoint hgrad

/-- Explicit-arguments version of the packaged RS1 conclusion, convenient
when the restart extraction already exposes the wall coordinates. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rigid_of_nonzero_wall
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (Y Z : K)
    (hpoint : Y ≠ 0 ∨ Z ≠ 0)
    (hgrad :
      HasPersistentQuadraticGradientZero
        x y z D
        (smithSubfacePolynomial
          y z w
          (smithSymmetricBalancedSubface
            (smithProjectedSupport y z w F) m base)
          F)
        Y Z) :
    HasRigidRankOnePacket
      x y z D
      (smithSubfacePolynomial
        y z w
        (smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base)
        F) := by
  apply
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rigid_of_firstWallCertificate
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  exact ⟨Y, Z, hpoint, hgrad⟩


/-! ## Certificate-free Smith first-wall re-entry

The preceding wall-certificate theorem is useful when the degeneration
already exposes a nonzero transverse collision.  For restart assembly,
however, we can avoid making that geometric extraction a prerequisite.

The canonical Smith restriction is already known above to be nonzero and to
have persistent rank-one packet support.  The Phase 92 re-entry theorem then
applies unconditionally.  Hence the first Smith wall has only two algebraic
outcomes:

* determinant-zero square/axis geometry; or
* a nondegenerate transverse block with trivial kernel, i.e. genuine
  rank-two re-entry.

This is exactly the dichotomy needed by the repair spine.  In particular,
the nonzero first-wall gradient certificate is only required if one wants to
force the first branch immediately; it is not needed merely to leave the
unclassified rank-one regime.
-/

/-- **Certificate-free Smith re-entry package.**

At an exact homogeneous axis collision, pole minimality and attainment of the
old Smith minimum construct the canonical nonzero persistent packet and
immediately feed it into the already-green rank-one re-entry theorem.

No nonzero transverse wall point and no leading-gradient equations are
assumed. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_reentry
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport x y z D G ∧
      G ≠ 0 ∧
      HasRankOnePacketReentry x y z D G := by
  dsimp
  have hpacket :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonzero_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  refine ⟨hpacket.1, hpacket.2.1, hpacket.2.2, ?_⟩
  exact
    rankOnePersistentPacket_reentry
      hxy hxz hyz
      hpacket.2.1 hpacket.2.2

/-- **Expanded certificate-free Smith first-wall dichotomy.**

This is the re-entry package with `HasRankOnePacketReentry` unfolded.  It is
convenient for the global restart proof: the left branch is the explicit
determinant-zero square/axis geometry, while the right branch already carries
both nonzero determinant and trivial transverse kernel. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_or_rankTwo
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    (rankOnePacketDiscriminant x y z D G = 0 ∧
      (((rankOnePacketQuadraticBlock x y z D G).LeftPivot ∧
        (∀ Y Z : K,
          (rankOnePacketQuadraticBlock x y z D G).a *
              (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
            ((rankOnePacketQuadraticBlock x y z D G).a * Y +
              (rankOnePacketQuadraticBlock x y z D G).b * Z) ^ 2)) ∨
       ((rankOnePacketQuadraticBlock x y z D G).RightAxisPivot ∧
        (∀ Y Z : K,
          (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
            (rankOnePacketQuadraticBlock x y z D G).c * Z * Z)))) ∨
    (rankOnePacketDiscriminant x y z D G ≠ 0 ∧
      (rankOnePacketQuadraticBlock x y z D G).detCore ≠ 0 ∧
      (rankOnePacketQuadraticBlock x y z D G).HasTrivialKernel) := by
  dsimp
  have hreentry :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_reentry
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  exact hreentry.2.2.2

/-- If the genuine rank-two branch is unavailable at the restart state, the
certificate-free Smith dichotomy automatically collapses to the
determinant-zero square/axis branch. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_of_no_rankTwo
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (hnoRankTwo :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      ¬ (rankOnePacketDiscriminant x y z D G ≠ 0 ∧
          (rankOnePacketQuadraticBlock x y z D G).detCore ≠ 0 ∧
          (rankOnePacketQuadraticBlock x y z D G).HasTrivialKernel)) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    rankOnePacketDiscriminant x y z D G = 0 ∧
      (((rankOnePacketQuadraticBlock x y z D G).LeftPivot ∧
        (∀ Y Z : K,
          (rankOnePacketQuadraticBlock x y z D G).a *
              (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
            ((rankOnePacketQuadraticBlock x y z D G).a * Y +
              (rankOnePacketQuadraticBlock x y z D G).b * Z) ^ 2)) ∨
       ((rankOnePacketQuadraticBlock x y z D G).RightAxisPivot ∧
        (∀ Y Z : K,
          (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
            (rankOnePacketQuadraticBlock x y z D G).c * Z * Z))) := by
  dsimp at hnoRankTwo ⊢
  rcases
      homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_or_rankTwo
        x y z w hxy hxz hxw hyz hyw hzw hchart
        hhom hD hcoll m base hpole hmin hattain with
    hsquare | hrankTwo
  · exact hsquare
  · exact False.elim (hnoRankTwo hrankTwo)

/-- Conversely, a nonzero discriminant at the canonical Smith packet
immediately gives the full genuine rank-two escape certificate. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rankTwo_of_discriminant_ne_zero
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (hdisc :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      rankOnePacketDiscriminant x y z D G ≠ 0) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    rankOnePacketDiscriminant x y z D G ≠ 0 ∧
      (rankOnePacketQuadraticBlock x y z D G).detCore ≠ 0 ∧
      (rankOnePacketQuadraticBlock x y z D G).HasTrivialKernel := by
  dsimp at hdisc ⊢
  have hreentry :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_or_rankTwo
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  rcases hreentry with hsquare | hrankTwo
  · exact False.elim (hdisc hsquare.1)
  · exact hrankTwo


/-! ## Smith first-wall strict-repair interface

Phase 93.44 removes the need for a separate nonzero-wall certificate merely
to leave the rank-one regime.  This section connects its algebraic
square-or-rank-two dichotomy to the *existing* finite repair state and
measure.

No new termination relation is introduced.  The nondegenerate Smith branch
is interpreted as the already-certified rank promotion

    rank 1 -> rank 2

at unchanged finite complexity.  Hence it is `RepairProgress`, strictly
lowers `RepairState.measure`, and in fact lowers that measure by exactly one.
-/

/-- Explicit determinant-zero Smith packet geometry, named for use by the
global restart dispatcher. -/
def HasSmithSquareOrAxisPacket
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K) : Prop :=
  rankOnePacketDiscriminant x y z D G = 0 ∧
    (((rankOnePacketQuadraticBlock x y z D G).LeftPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D G).a *
            (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
          ((rankOnePacketQuadraticBlock x y z D G).a * Y +
            (rankOnePacketQuadraticBlock x y z D G).b * Z) ^ 2)) ∨
     ((rankOnePacketQuadraticBlock x y z D G).RightAxisPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D G).quadratic Y Z =
          (rankOnePacketQuadraticBlock x y z D G).c * Z * Z)))

/-- Explicit nondegenerate Smith packet geometry: nonzero discriminant,
nonzero binary determinant, and trivial transverse kernel. -/
def HasSmithRankTwoEscape
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K) : Prop :=
  rankOnePacketDiscriminant x y z D G ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D G).detCore ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D G).HasTrivialKernel

/-- Restart-facing form of the nondegenerate Smith branch.  Besides the
rank-two algebraic certificate, it carries the exact existing
`RepairProgress` step and strict decrease of the existing repair measure. -/
def HasSmithStrictRepairOutcome
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K)
    (complexity : ℕ) : Prop :=
  HasSmithRankTwoEscape x y z D G ∧
    RepairProgress
      (preterminalRankOneRepairState complexity)
      (preterminalRankTwoRepairState complexity) ∧
    (preterminalRankTwoRepairState complexity).measure <
      (preterminalRankOneRepairState complexity).measure

/-- The complete local Smith-wall result in the form wanted by restart
assembly: either the packet is already in explicit square/axis geometry, or
the same wall gives a strict step in the existing finite repair system. -/
def HasSmithFirstWallRepairOutcome
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K)
    (complexity : ℕ) : Prop :=
  HasSmithSquareOrAxisPacket x y z D G ∨
    HasSmithStrictRepairOutcome x y z D G complexity

/-- The Phase 93.44 re-entry predicate is exactly the named
square-or-rank-two dichotomy used here. -/
theorem hasRankOnePacketReentry_iff_smithSquare_or_rankTwo
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K) :
    HasRankOnePacketReentry x y z D G ↔
      HasSmithSquareOrAxisPacket x y z D G ∨
        HasSmithRankTwoEscape x y z D G := by
  rfl

/-- A nondegenerate Smith packet automatically produces a strict repair
step at every finite complexity. -/
theorem smithRankTwoEscape_strictRepair
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K)
    (complexity : ℕ)
    (hrankTwo : HasSmithRankTwoEscape x y z D G) :
    HasSmithStrictRepairOutcome x y z D G complexity := by
  refine ⟨hrankTwo, ?_, ?_⟩
  · exact preterminal_rankOne_to_rankTwo_repairProgress complexity
  · exact preterminal_mixedPivot_strictly_lowers_repairMeasure complexity

/-- The same strict repair step lowers the canonical measure by exactly one. -/
theorem smithRankTwoEscape_measure_drop_exact
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K)
    (complexity : ℕ)
    (_hrankTwo : HasSmithRankTwoEscape x y z D G) :
    (preterminalRankTwoRepairState complexity).measure + 1 =
      (preterminalRankOneRepairState complexity).measure := by
  exact preterminal_rankOne_to_rankTwo_measure_drop_exact complexity

/-- **Smith first-wall strict-repair theorem.**

Exact homogeneous axis collision + pole minimality + attainment constructs
the canonical nonzero Smith packet and dispatches it immediately into one of
the two restart channels:

* explicit determinant-zero square/axis geometry; or
* genuine rank-two escape together with `RepairProgress` and strict decrease
  of the already-existing finite repair measure.

The theorem also retains nonemptiness, packet support and nonzeroness, so a
later restart file does not need to reconstruct any local Smith data. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_firstWallRepair
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport x y z D G ∧
      G ≠ 0 ∧
      HasSmithFirstWallRepairOutcome x y z D G complexity := by
  dsimp
  have hpacket :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_reentry
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  refine ⟨hpacket.1, hpacket.2.1, hpacket.2.2.1, ?_⟩
  have hsplit :
      HasSmithSquareOrAxisPacket x y z D
          (smithSubfacePolynomial y z w
            (smithSymmetricBalancedSubface
              (smithProjectedSupport y z w F) m base) F) ∨
        HasSmithRankTwoEscape x y z D
          (smithSubfacePolynomial y z w
            (smithSymmetricBalancedSubface
              (smithProjectedSupport y z w F) m base) F) := by
    exact
      (hasRankOnePacketReentry_iff_smithSquare_or_rankTwo
        x y z D
        (smithSubfacePolynomial y z w
          (smithSymmetricBalancedSubface
            (smithProjectedSupport y z w F) m base) F)).1
        hpacket.2.2.2
  rcases hsplit with hsquare | hrankTwo
  · exact Or.inl hsquare
  · exact Or.inr
      (smithRankTwoEscape_strictRepair
        x y z D
        (smithSubfacePolynomial y z w
          (smithSymmetricBalancedSubface
            (smithProjectedSupport y z w F) m base) F)
        complexity hrankTwo)

/-- If the Smith packet is not already square/axis, its first-wall outcome
is necessarily a strict repair step in the existing finite system. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_strictRepair_of_not_square
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ)
    (hnotSquare :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      ¬ HasSmithSquareOrAxisPacket x y z D G) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    HasSmithStrictRepairOutcome x y z D G complexity := by
  dsimp at hnotSquare ⊢
  have hout :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_firstWallRepair
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain complexity
  rcases hout.2.2.2 with hsquare | hrepair
  · exact False.elim (hnotSquare hsquare)
  · exact hrepair

/-- Conversely, if no strict rank-two repair is available, the canonical
Smith packet must already lie in the determinant-zero square/axis channel. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_of_no_strictRepair
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ)
    (hnoRepair :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      ¬ HasSmithStrictRepairOutcome x y z D G complexity) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    HasSmithSquareOrAxisPacket x y z D G := by
  dsimp at hnoRepair ⊢
  have hout :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_firstWallRepair
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain complexity
  rcases hout.2.2.2 with hsquare | hrepair
  · exact hsquare
  · exact False.elim (hnoRepair hrepair)

/-- In the nonsquare Smith branch the global repair measure drops by exactly
one, not merely strictly. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_measure_drop_exact_of_not_square
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ)
    (hnotSquare :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      ¬ HasSmithSquareOrAxisPacket x y z D G) :
    (preterminalRankTwoRepairState complexity).measure + 1 =
      (preterminalRankOneRepairState complexity).measure := by
  have _hrepair :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_strictRepair_of_not_square
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain complexity hnotSquare
  exact preterminal_rankOne_to_rankTwo_measure_drop_exact complexity



/-! ## Canonical Smith-to-repair exhaustion -/

/-- The Smith square/axis predicate is exactly the canonical rigid rank-one
packet predicate used by `RankOneRepairProgress`. -/
theorem hasSmithSquareOrAxisPacket_iff_hasRigidRankOnePacket
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K) :
    HasSmithSquareOrAxisPacket x y z D G ↔
      HasRigidRankOnePacket x y z D G := by
  rfl

/-- The Smith rank-two escape predicate is exactly the canonical
rank-two-escalation predicate. -/
theorem hasSmithRankTwoEscape_iff_hasRankTwoPacketEscalation
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K) :
    HasSmithRankTwoEscape x y z D G ↔
      HasRankTwoPacketEscalation x y z D G := by
  rfl

/-- Single canonical repair outcome used by restart assembly. -/
def HasSmithCanonicalRepairOutcome
    (x y z : σ)
    (D : ℕ)
    (G : MvPolynomial σ K)
    (complexity : ℕ) : Prop :=
  HasRigidRankOnePacket x y z D G ∨
    (HasRankTwoPacketEscalation x y z D G ∧
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure)

/-- **Canonical Smith first-wall repair theorem.**

The canonical Smith restriction now lands directly in the same repair-state
API as the mixed-departure and rank-two terminal machinery.  There is no
remaining state-translation layer. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_canonicalRepair
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport x y z D G ∧
      G ≠ 0 ∧
      HasSmithCanonicalRepairOutcome
        x y z D G complexity := by
  dsimp
  have hpacket :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonzero_rankOnePacket
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
  refine ⟨hpacket.1, hpacket.2.1, hpacket.2.2, ?_⟩
  rcases
      rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        hxy hxz hyz hpacket.2.1 hpacket.2.2 with
    hrigid | hrepair
  · exact Or.inl hrigid
  · right
    exact
      ⟨hrepair.1, hrepair.2,
        repairState_measure_lt_of_progress hrepair.2⟩

/-- In the non-rigid Smith branch, the entire remaining fixed-complexity
rank ladder is already controlled: the wall gives `1 -> 2`; any next
rank-two repair either lowers complexity or reaches rank three; and every
repair after rank three must lower complexity. -/
theorem homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonsquareRepairExhaustion
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
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ)
    (hnotRigid :
      let T :=
        smithSymmetricBalancedSubface
          (smithProjectedSupport y z w F) m base
      let G :=
        smithSubfacePolynomial y z w T F
      ¬ HasRigidRankOnePacket x y z D G) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    HasRankTwoPacketEscalation x y z D G ∧
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure ∧
      (∀ t : RepairState,
        RepairProgress (rankTwoRepairState complexity) t ->
          t.complexity < complexity ∨
            (t.complexity = complexity ∧ t.rank = 3)) ∧
      (∀ t : RepairState,
        RepairProgress (rankThreeRepairState complexity) t ->
          t.complexity < complexity) := by
  dsimp at hnotRigid ⊢
  have hout :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_canonicalRepair
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain complexity
  rcases hout.2.2.2 with hrigid | hrepair
  · exact False.elim (hnotRigid hrigid)
  · refine ⟨hrepair.1, hrepair.2.1, hrepair.2.2, ?_, ?_⟩
    · intro t hnext
      exact
        rankTwo_repairProgress_complexityDrop_or_rankThree
          complexity hnext
    · intro t hnext
      exact
        rankThree_repairProgress_forces_complexityDrop
          complexity hnext


end

end HC4.Newton
