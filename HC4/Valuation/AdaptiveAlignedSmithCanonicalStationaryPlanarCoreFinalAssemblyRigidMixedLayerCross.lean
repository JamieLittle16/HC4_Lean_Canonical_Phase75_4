import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidTopKernel
import Mathlib.Tactic

/-!
# Final assembly A17.3D: exact mixed-layer tangent equation for the rigid branch

A17.3B identified the maximal nonlinear ordinary-homogeneous layer of the
literal rigid special fibre as `a * L^D`.  A17.3C extracted an explicit
transverse constant kernel direction for that top layer.

The full special fibre is genuinely mixed in ordinary degree, so it is not
just the top layer.  This file peels the next occupied homogeneous layer
`G_E`, proves `E < D`, and extracts the exact degree `(D-2)+(E-2)` part of
every vanishing `2 x 2` Hessian minor.  The result is the bilinear
polarisation identity between the Hessians of the top layer and `G_E`.

For `H_D = a L^D`, the `(p,p,q,q)` polarisation factors by the nonzero top
Hessian scalar and leaves the tangent-space equation

    c_p^2 G_qq - c_p c_q G_qp - c_p c_q G_pq + c_q^2 G_pp = 0

for every coordinate `q`, where `p` is the nonzero top coefficient pivot.
Equivalently, every two-coordinate vector `c_p e_q - c_q e_p` has zero
second directional derivative on the next layer.

No descent is declared here.  This is the exact cross-degree algebra needed
by the finite direction-lock/staircase eliminator.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Bilinear polarisation of one `2 x 2` Hessian minor. -/
def fourHessianMinorCross
    (P Q : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.hessian P i j * HC4.Polynomial.hessian Q k l +
    HC4.Polynomial.hessian Q i j * HC4.Polynomial.hessian P k l -
    HC4.Polynomial.hessian P i l * HC4.Polynomial.hessian Q k j -
    HC4.Polynomial.hessian Q i l * HC4.Polynomial.hessian P k j

/-- Quadratic Hessian expression in the canonical two-coordinate direction
`c_p e_q - c_q e_p`.  We deliberately retain both mixed Hessian orientations;
this avoids introducing any symmetry rewrite into the exact factorisation. -/
def rigidTopPairTangentExpression
    (c : Fin 4 → K)
    (p q : Fin 4)
    (G : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C (c p * c p) * HC4.Polynomial.hessian G q q -
    MvPolynomial.C (c p * c q) * HC4.Polynomial.hessian G q p -
    MvPolynomial.C (c p * c q) * HC4.Polynomial.hessian G p q +
    MvPolynomial.C (c q * c q) * HC4.Polynomial.hessian G p p

/-- Exact polarisation identity for one Hessian minor. -/
theorem fourHessianMinor_add_cross
    (P Q : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4) :
    HC4.Polynomial.hessian (P + Q) i j *
          HC4.Polynomial.hessian (P + Q) k l -
        HC4.Polynomial.hessian (P + Q) i l *
          HC4.Polynomial.hessian (P + Q) k j =
      (HC4.Polynomial.hessian P i j * HC4.Polynomial.hessian P k l -
        HC4.Polynomial.hessian P i l * HC4.Polynomial.hessian P k j) +
      fourHessianMinorCross P Q i j k l +
      (HC4.Polynomial.hessian Q i j * HC4.Polynomial.hessian Q k l -
        HC4.Polynomial.hessian Q i l * HC4.Polynomial.hessian Q k j) := by
  unfold fourHessianMinorCross
  simp only [HC4.Polynomial.hessian_apply, map_add]
  ring

/-- Ordinary-weight homogeneity of a four-variable Hessian entry of a
homogeneous polynomial. -/
theorem fourHessianEntry_isWeightedHomogeneous
    (H : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous
      fourOrdinaryIntegerWeight H D)
    (i j : Fin 4) :
    MvPolynomial.IsWeightedHomogeneous fourOrdinaryIntegerWeight
      (HC4.Polynomial.hessian H i j) ((D : ℤ) - 2) := by
  have h := HC4.Polynomial.hessian_entry_isWeightedHomogeneous hH i j
  have hshift :
      (D : ℤ) - fourOrdinaryIntegerWeight i - fourOrdinaryIntegerWeight j =
        (D : ℤ) - 2 := by
    simp [fourOrdinaryIntegerWeight]
    ring
  rw [hshift] at h
  exact h

/-- Ordinary-weight upper bound for a four-variable Hessian entry. -/
theorem fourHessianEntry_isWeightLE
    (Q : MvPolynomial (Fin 4) K)
    (E : ℕ)
    (hQ : IsWeightLE fourOrdinaryIntegerWeight E Q)
    (i j : Fin 4) :
    IsWeightLE fourOrdinaryIntegerWeight ((E : ℤ) - 2)
      (HC4.Polynomial.hessian Q i j) := by
  have h := hQ.hessian_entry i j
  have hshift :
      (E : ℤ) - fourOrdinaryIntegerWeight i - fourOrdinaryIntegerWeight j =
        (E : ℤ) - 2 := by
    simp [fourOrdinaryIntegerWeight]
    ring
  rw [hshift] at h
  exact h

/-- A `2 x 2` Hessian minor of a polynomial of ordinary degree at most `E`
has ordinary weight at most `2(E-2)`. -/
theorem fourHessianMinor_isWeightLE
    (Q : MvPolynomial (Fin 4) K)
    (E : ℕ)
    (hQ : IsWeightLE fourOrdinaryIntegerWeight E Q)
    (i j k l : Fin 4) :
    IsWeightLE fourOrdinaryIntegerWeight
      (((E : ℤ) - 2) + ((E : ℤ) - 2))
      (HC4.Polynomial.hessian Q i j * HC4.Polynomial.hessian Q k l -
        HC4.Polynomial.hessian Q i l * HC4.Polynomial.hessian Q k j) := by
  have hleft :=
    (fourHessianEntry_isWeightLE Q E hQ i j).mul
      (fourHessianEntry_isWeightLE Q E hQ k l)
  have hright :=
    (fourHessianEntry_isWeightLE Q E hQ i l).mul
      (fourHessianEntry_isWeightLE Q E hQ k j)
  exact hleft.sub hright

/-- The exact degree-`E-2` part of a Hessian entry is the Hessian entry of the
exact degree-`E` component. -/
theorem initialForm_fourHessianEntry_eq_componentHessian
    (R : MvPolynomial (Fin 4) K)
    (E : ℕ)
    (i j : Fin 4) :
    initialForm fourOrdinaryIntegerWeight ((E : ℤ) - 2)
        (HC4.Polynomial.hessian R i j) =
      HC4.Polynomial.hessian (fourOrdinaryDegreeComponent R E) i j := by
  have h := HC4.Polynomial.hessian_initialForm_entry
    fourOrdinaryIntegerWeight (E : ℤ) R i j
  have hshift :
      (E : ℤ) - fourOrdinaryIntegerWeight i - fourOrdinaryIntegerWeight j =
        (E : ℤ) - 2 := by
    simp [fourOrdinaryIntegerWeight]
    ring
  rw [hshift] at h
  simpa [fourOrdinaryDegreeComponent] using h.symm

/-- Exact extraction of the mixed top/next-layer Hessian polarisation. -/
theorem initialForm_fourHessianMinorCross_eq_nextComponent
    (H R : MvPolynomial (Fin 4) K)
    (D E : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous
      fourOrdinaryIntegerWeight H D)
    (hR : IsWeightLE fourOrdinaryIntegerWeight E R)
    (i j k l : Fin 4) :
    initialForm fourOrdinaryIntegerWeight
        (((D : ℤ) - 2) + ((E : ℤ) - 2))
        (fourHessianMinorCross H R i j k l) =
      fourHessianMinorCross H (fourOrdinaryDegreeComponent R E) i j k l := by
  let w := fourOrdinaryIntegerWeight
  let Hij := HC4.Polynomial.hessian H i j
  let Hkl := HC4.Polynomial.hessian H k l
  let Hil := HC4.Polynomial.hessian H i l
  let Hkj := HC4.Polynomial.hessian H k j
  let Rij := HC4.Polynomial.hessian R i j
  let Rkl := HC4.Polynomial.hessian R k l
  let Ril := HC4.Polynomial.hessian R i l
  let Rkj := HC4.Polynomial.hessian R k j
  let G := fourOrdinaryDegreeComponent R E
  have hHij : MvPolynomial.IsWeightedHomogeneous w Hij ((D : ℤ) - 2) := by
    dsimp [w, Hij]
    exact fourHessianEntry_isWeightedHomogeneous H D hH i j
  have hHkl : MvPolynomial.IsWeightedHomogeneous w Hkl ((D : ℤ) - 2) := by
    dsimp [w, Hkl]
    exact fourHessianEntry_isWeightedHomogeneous H D hH k l
  have hHil : MvPolynomial.IsWeightedHomogeneous w Hil ((D : ℤ) - 2) := by
    dsimp [w, Hil]
    exact fourHessianEntry_isWeightedHomogeneous H D hH i l
  have hHkj : MvPolynomial.IsWeightedHomogeneous w Hkj ((D : ℤ) - 2) := by
    dsimp [w, Hkj]
    exact fourHessianEntry_isWeightedHomogeneous H D hH k j
  have hRij : IsWeightLE w ((E : ℤ) - 2) Rij := by
    dsimp [w, Rij]
    exact fourHessianEntry_isWeightLE R E hR i j
  have hRkl : IsWeightLE w ((E : ℤ) - 2) Rkl := by
    dsimp [w, Rkl]
    exact fourHessianEntry_isWeightLE R E hR k l
  have hRil : IsWeightLE w ((E : ℤ) - 2) Ril := by
    dsimp [w, Ril]
    exact fourHessianEntry_isWeightLE R E hR i l
  have hRkj : IsWeightLE w ((E : ℤ) - 2) Rkj := by
    dsimp [w, Rkj]
    exact fourHessianEntry_isWeightLE R E hR k j
  have hentry_kl :
      initialForm fourOrdinaryIntegerWeight ((E : ℤ) - 2)
          ((MvPolynomial.pderiv l) ((MvPolynomial.pderiv k) R)) =
        (MvPolynomial.pderiv l)
          ((MvPolynomial.pderiv k) (fourOrdinaryDegreeComponent R E)) := by
    simpa only [HC4.Polynomial.hessian_apply] using
      (initialForm_fourHessianEntry_eq_componentHessian R E k l)
  have hentry_ij :
      initialForm fourOrdinaryIntegerWeight ((E : ℤ) - 2)
          ((MvPolynomial.pderiv j) ((MvPolynomial.pderiv i) R)) =
        (MvPolynomial.pderiv j)
          ((MvPolynomial.pderiv i) (fourOrdinaryDegreeComponent R E)) := by
    simpa only [HC4.Polynomial.hessian_apply] using
      (initialForm_fourHessianEntry_eq_componentHessian R E i j)
  have hentry_kj :
      initialForm fourOrdinaryIntegerWeight ((E : ℤ) - 2)
          ((MvPolynomial.pderiv j) ((MvPolynomial.pderiv k) R)) =
        (MvPolynomial.pderiv j)
          ((MvPolynomial.pderiv k) (fourOrdinaryDegreeComponent R E)) := by
    simpa only [HC4.Polynomial.hessian_apply] using
      (initialForm_fourHessianEntry_eq_componentHessian R E k j)
  have hentry_il :
      initialForm fourOrdinaryIntegerWeight ((E : ℤ) - 2)
          ((MvPolynomial.pderiv l) ((MvPolynomial.pderiv i) R)) =
        (MvPolynomial.pderiv l)
          ((MvPolynomial.pderiv i) (fourOrdinaryDegreeComponent R E)) := by
    simpa only [HC4.Polynomial.hessian_apply] using
      (initialForm_fourHessianEntry_eq_componentHessian R E i l)
  have htop_ij_kl :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Hij * Rkl) =
        Hij * HC4.Polynomial.hessian G k l := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hHij hRkl]
    dsimp [w, Rkl, G]
    rw [hentry_kl]
  have htop_kl_ij :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Rij * Hkl) =
        HC4.Polynomial.hessian G i j * Hkl := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hHkl hRij]
    dsimp [w, Rij, G]
    rw [hentry_ij]
    ring
  have htop_il_kj :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Hil * Rkj) =
        Hil * HC4.Polynomial.hessian G k j := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hHil hRkj]
    dsimp [w, Rkj, G]
    rw [hentry_kj]
  have htop_kj_il :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Ril * Hkj) =
        HC4.Polynomial.hessian G i l * Hkj := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hHkj hRil]
    dsimp [w, Ril, G]
    rw [hentry_il]
    ring
  unfold fourHessianMinorCross
  change initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2))
      (Hij * Rkl + Rij * Hkl - Hil * Rkj - Ril * Hkj) = _
  simp only [map_sub, initialForm_add]
  rw [htop_ij_kl, htop_kl_ij, htop_il_kj, htop_kj_il]

/-- Exact next-layer consequence of a full vanishing Hessian minor. -/
theorem fourHessianMinorCross_nextComponent_eq_zero
    (Q H R : MvPolynomial (Fin 4) K)
    (D E : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      fourOrdinaryIntegerWeight H D)
    (hR : IsWeightLE fourOrdinaryIntegerWeight E R)
    (hED : E < D)
    (i j k l : Fin 4)
    (hQminor :
      HC4.Polynomial.hessian Q i j * HC4.Polynomial.hessian Q k l -
        HC4.Polynomial.hessian Q i l * HC4.Polynomial.hessian Q k j = 0)
    (hHminor :
      HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
        HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0) :
    fourHessianMinorCross H (fourOrdinaryDegreeComponent R E) i j k l = 0 := by
  let n : ℤ := ((D : ℤ) - 2) + ((E : ℤ) - 2)
  have hRminorLE := fourHessianMinor_isWeightLE R E hR i j k l
  have hboundlt :
      (((E : ℤ) - 2) + ((E : ℤ) - 2)) < n := by
    dsimp [n]
    have hcast : (E : ℤ) < (D : ℤ) := by exact_mod_cast hED
    omega
  have hRminorTop :
      initialForm fourOrdinaryIntegerWeight n
        (HC4.Polynomial.hessian R i j * HC4.Polynomial.hessian R k l -
          HC4.Polynomial.hessian R i l * HC4.Polynomial.hessian R k j) = 0 :=
    initialForm_eq_zero_of_isWeightLE hRminorLE hboundlt
  have hsum :
      fourHessianMinorCross H R i j k l +
          (HC4.Polynomial.hessian R i j * HC4.Polynomial.hessian R k l -
            HC4.Polynomial.hessian R i l * HC4.Polynomial.hessian R k j) = 0 := by
    have hexpand := fourHessianMinor_add_cross H R i j k l
    have heq :
        fourHessianMinorCross H R i j k l +
            (HC4.Polynomial.hessian R i j * HC4.Polynomial.hessian R k l -
              HC4.Polynomial.hessian R i l * HC4.Polynomial.hessian R k j) =
          (HC4.Polynomial.hessian (H + R) i j *
              HC4.Polynomial.hessian (H + R) k l -
            HC4.Polynomial.hessian (H + R) i l *
              HC4.Polynomial.hessian (H + R) k j) -
          (HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
            HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j) := by
      rw [hexpand]
      ring
    rw [heq, ← hdecomp, hQminor, hHminor]
    ring
  have hcomponent := congrArg
    (fun P : MvPolynomial (Fin 4) K =>
      initialForm fourOrdinaryIntegerWeight n P) hsum
  have hcrossTop := initialForm_fourHessianMinorCross_eq_nextComponent
    H R D E hH hR i j k l
  dsimp [n] at hcomponent hRminorTop
  rw [initialForm_add, hcrossTop, hRminorTop, add_zero, initialForm_zero]
    at hcomponent
  exact hcomponent

/-- Factor the `(p,p,q,q)` mixed minor against a four-variable linear power. -/
theorem fourHessianMinorCross_linearPower_pair_factor
    (a : K)
    (c : Fin 4 → K)
    (n : ℕ)
    (G : MvPolynomial (Fin 4) K)
    (p q : Fin 4) :
    fourHessianMinorCross
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2))
        G p p q q =
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        (gradientRatioLinearForm c) ^ n) *
        rigidTopPairTangentExpression c p q G := by
  have hpp := hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour
    a c n p p
  have hqq := hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour
    a c n q q
  have hpq := hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour
    a c n p q
  have hqp := hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour
    a c n q p
  unfold fourHessianMinorCross rigidTopPairTangentExpression
  rw [hpp, hqq, hpq, hqp]
  simp only [MvPolynomial.C_mul]
  ring

/-- A zero mixed minor against a nonzero top linear power forces the exact
pairwise tangent equation on the lower layer. -/
theorem fourLinearPower_cross_zero_implies_pair_tangent_zero
    (H G : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hD : 2 ≤ D)
    (hHne : H ≠ 0)
    (a : K)
    (c : Fin 4 → K)
    (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (p q : Fin 4)
    (hcross : fourHessianMinorCross H G p p q q = 0) :
    rigidTopPairTangentExpression c p q G = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, D = n + 2 := by
    exact ⟨D - 2, (Nat.sub_add_cancel hD).symm⟩
  let L : MvPolynomial (Fin 4) K := gradientRatioLinearForm c
  have ha : a ≠ 0 := by
    intro ha
    apply hHne
    rw [normalForm, ha]
    simp
  have hL : L ≠ 0 := by
    intro hL
    apply hHne
    rw [normalForm]
    change MvPolynomial.C a * L ^ (n + 2) = 0
    rw [hL]
    simp
  have hn2 : (((n + 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  have hn1 : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hs :
      a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha hn2) hn1
  have hfactor :
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        L ^ n : MvPolynomial (Fin 4) K) ≠ 0 := by
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hs) (pow_ne_zero n hL)
  have hfac := fourHessianMinorCross_linearPower_pair_factor
    a c n G p q
  rw [← normalForm] at hfac
  have hprod :
      (MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))) *
        L ^ n) * rigidTopPairTangentExpression c p q G = 0 := by
    rw [← hfac, hcross]
  exact (mul_eq_zero.mp hprod).resolve_left hfactor

/-- A17.3D packet: the first lower occupied homogeneous layer of the literal
rigid special fibre, with the exact all-minor cross equation and its
pairwise tangent consequence. -/
structure AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) where
  topKernel : AdaptiveAlignedSmithCanonicalRigidTopKernelData S
  remainder : MvPolynomial (Fin 4) K
  remainder_eq :
    remainder =
      longitudinalRightRecenterHom
          (K := K) S.blocker.aligned.endpoint.rawSpecialFiber -
        topKernel.topLayer.top
  remainder_ne_zero : remainder ≠ 0
  degree : ℕ
  layer : MvPolynomial (Fin 4) K
  degree_lt_top : degree < topKernel.topLayer.degree
  layer_eq : layer = fourOrdinaryDegreeComponent remainder degree
  layer_ne_zero : layer ≠ 0
  remainder_maximal :
    ∀ d ∈ remainder.support, HC4.Polynomial.ordinaryDegree4 d ≤ degree
  layer_homogeneous : layer.IsHomogeneous degree
  cross_zero :
    ∀ i j k l : Fin 4,
      fourHessianMinorCross topKernel.topLayer.top layer i j k l = 0
  pair_tangent_zero :
    ∀ q : Fin 4,
      rigidTopPairTangentExpression
        topKernel.topLayer.ratio topKernel.pivot q layer = 0

namespace AdaptiveAlignedSmithCanonicalRigidTopKernelData

/-- The rigid special fibre cannot collapse to its top homogeneous layer,
because the source-complete obstruction retains two occupied monomials of
different ordinary degree on that exact fibre. -/
theorem remainder_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (T : AdaptiveAlignedSmithCanonicalRigidTopKernelData S) :
    longitudinalRightRecenterHom
          (K := K) S.blocker.aligned.endpoint.rawSpecialFiber -
        T.topLayer.top ≠ 0 := by
  let Q := longitudinalRightRecenterHom
    (K := K) S.blocker.aligned.endpoint.rawSpecialFiber
  intro hzero
  have hQH : Q = T.topLayer.top := by
    apply sub_eq_zero.mp
    simpa [Q] using hzero
  rcases T.topLayer.rigid.mixedDegree_pair with
    ⟨d₀, d₁, hd₀, hd₁, hdegree⟩
  have hd₀Q : d₀ ∈ Q.support := by
    dsimp [Q]
    rw [← S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    exact hd₀
  have hd₁Q : d₁ ∈ Q.support := by
    dsimp [Q]
    rw [← S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    exact hd₁
  have hhom : T.topLayer.top.IsHomogeneous T.topLayer.degree := by
    rw [T.topLayer.top_eq]
    exact fourOrdinaryDegreeComponent_isHomogeneous Q T.topLayer.degree
  rw [hQH] at hd₀Q hd₁Q
  have hdeg₀ := ordinaryDegree4_eq_of_isHomogeneous hhom hd₀Q
  have hdeg₁ := ordinaryDegree4_eq_of_isHomogeneous hhom hd₁Q
  exact hdegree (hdeg₀.trans hdeg₁.symm)

/-- **A17.3D exact rigid mixed-layer theorem.** -/
theorem toRigidMixedLayerCrossData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (T : AdaptiveAlignedSmithCanonicalRigidTopKernelData S) :
    Nonempty (AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData S) := by
  let Q := longitudinalRightRecenterHom
    (K := K) S.blocker.aligned.endpoint.rawSpecialFiber
  let H := T.topLayer.top
  let D := T.topLayer.degree
  let R := Q - H
  have hRne : R ≠ 0 := by
    simpa [R, Q, H] using T.remainder_ne_zero
  have hQLE : IsWeightLE fourOrdinaryIntegerWeight D Q := by
    dsimp [D, Q]
    exact isWeightLE_fourOrdinary_of_degree_le
      (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber)
      T.topLayer.degree T.topLayer.maximal
  have hRlt0 :
      IsWeightLT fourOrdinaryIntegerWeight D
        (Q - fourOrdinaryDegreeComponent Q D) :=
    sub_initialForm_isWeightLT hQLE
  have hRlt : IsWeightLT fourOrdinaryIntegerWeight D R := by
    have htop : H = fourOrdinaryDegreeComponent Q D := by
      simpa [H, Q, D] using T.topLayer.top_eq
    simpa [R, htop] using hRlt0
  rcases exists_maximal_fourOrdinaryDegreeComponent R hRne with
    ⟨E, hGne0, hRmax⟩
  let G := fourOrdinaryDegreeComponent R E
  have hED : E < D := by
    by_contra hnot
    have hDE : D ≤ E := Nat.le_of_not_gt hnot
    have hzero : fourOrdinaryDegreeComponent R E = 0 := by
      unfold fourOrdinaryDegreeComponent
      apply initialForm_eq_zero_of_isWeightLT hRlt
      exact_mod_cast hDE
    exact hGne0 hzero
  have hGne : G ≠ 0 := by simpa [G] using hGne0
  have hGhom : G.IsHomogeneous E := by
    exact fourOrdinaryDegreeComponent_isHomogeneous R E
  have hRLE : IsWeightLE fourOrdinaryIntegerWeight E R :=
    isWeightLE_fourOrdinary_of_degree_le R E hRmax
  have hHwh :
      MvPolynomial.IsWeightedHomogeneous fourOrdinaryIntegerWeight H D := by
    dsimp [H, D]
    rw [T.topLayer.top_eq]
    simpa [fourOrdinaryDegreeComponent, Q] using
      (initialForm_isWeightedHomogeneous
        fourOrdinaryIntegerWeight (T.topLayer.degree : ℤ) Q)
  have hdecomp : Q = H + R := by
    dsimp [R]
    ring
  have hallQ :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian Q i j * HC4.Polynomial.hessian Q k l -
          HC4.Polynomial.hessian Q i l * HC4.Polynomial.hessian Q k j = 0 := by
    simpa [Q] using T.topLayer.rigid.raw_allMinors
  have hallH :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
          HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0 := by
    intro i j k l
    dsimp [H, D]
    rw [T.topLayer.top_eq]
    exact fourOrdinaryDegreeComponent_allMinors_zero_of_maximal
      Q T.topLayer.degree (by simpa [Q] using T.topLayer.maximal)
      hallQ i j k l
  have hcross :
      ∀ i j k l : Fin 4,
        fourHessianMinorCross H G i j k l = 0 := by
    intro i j k l
    have h := fourHessianMinorCross_nextComponent_eq_zero
      Q H R D E hdecomp hHwh hRLE hED i j k l
      (hallQ i j k l) (hallH i j k l)
    simpa [G] using h
  have htangent :
      ∀ q : Fin 4,
        rigidTopPairTangentExpression
          T.topLayer.ratio T.pivot q G = 0 := by
    intro q
    exact fourLinearPower_cross_zero_implies_pair_tangent_zero
      H G D (by simpa [D] using T.topLayer.degree_ge_two)
      (by simpa [H] using T.topLayer.top_ne_zero)
      T.topLayer.coefficient T.topLayer.ratio
      (by simpa [H, D] using T.topLayer.linearPower)
      T.pivot q (hcross T.pivot T.pivot q q)
  exact ⟨{
    topKernel := T
    remainder := R
    remainder_eq := rfl
    remainder_ne_zero := hRne
    degree := E
    layer := G
    degree_lt_top := hED
    layer_eq := rfl
    layer_ne_zero := hGne
    remainder_maximal := hRmax
    layer_homogeneous := hGhom
    cross_zero := by simpa [H, G] using hcross
    pair_tangent_zero := by simpa [G] using htangent
  }⟩

end AdaptiveAlignedSmithCanonicalRigidTopKernelData

end

end HC4.Valuation
