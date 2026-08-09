import HC4.Polynomial.ComplementaryEdgeAssembly
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# Fraction-field bridge for the complementary rank-two obstruction

Phases 68--70 proved the determinant identity, the local logarithmic slope,
and the contradiction once the denominator-cleared polynomial equation is
available.  This file supplies the fraction-field denominator-clearing bridge.

For a polynomial `phi`, write

    E = X phi',
    A = X E' * phi - E^2.

In the fraction field of `K[X]`, `rho = E/phi` and `eta = A/phi^2`.  The
normalised complementary scalar equation

    (d0 + d1*rho) * eta = rho * (M-rho) * (r0 + d1*rho)

is shown to imply exactly `ComplementaryClearedEquation phi ...` in `K[X]`.
We also package the logarithmic-Hessian core determinant directly in the
fraction field and show that its vanishing gives the fraction equation when
the expected nonzero factors are present.

This file deliberately stops at the logarithmic-Hessian core.  Identifying an
actual complementary edge Hessian with this core is a separate upstream
formalisation obligation unless already proved elsewhere.
-/

namespace HC4.Polynomial

noncomputable section

/-- The normalised complementary `eta` equation in the fraction field of
`K[X]`, after substituting `rho = E/phi` and `eta = A/phi^2`. -/
def ComplementaryFractionEquation
    {K : Type*} [Field K]
    (phi : Polynomial K) (A0 B0 M h k : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p := ι phi
  let E := ι (eulerDerivative phi)
  let A := ι (logarithmicEtaNumerator phi)
  let d0 := ι (Polynomial.C (A0 * M * h * (B0 * M * k - 1)))
  let d1 := ι (Polynomial.C (A0 * h - B0 * k))
  let r0 := ι (Polynomial.C (B0 * M * k - 1))
  let MR := ι (Polynomial.C M)
  (d0 + d1 * (E / p)) * (A / p^2) =
    (E / p) * (MR - E / p) * (r0 + d1 * (E / p))

/-- The complementary logarithmic-Hessian core, evaluated in the fraction
field at `rho = E/phi` and `eta = A/phi^2`, has zero determinant. -/
def ComplementaryFractionCoreDetZero
    {K : Type*} [Field K]
    (phi : Polynomial K) (a1 a2 b1 b2 h k M : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p := ι phi
  let E := ι (eulerDerivative phi)
  let A := ι (logarithmicEtaNumerator phi)
  (complementaryLogHessianCore
      (ι (Polynomial.C a1)) (ι (Polynomial.C a2))
      (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
      (ι (Polynomial.C h)) (ι (Polynomial.C k))
      (ι (Polynomial.C M))
      (E / p) (A / p^2)).det = 0

/-- Pure field algebra: clearing the common denominator `p^3` in the
normalised complementary `eta` equation. -/
theorem complementary_scalar_fraction_equation_clears
    {F : Type*} [Field F]
    {p E A d0 d1 M r0 : F}
    (hp : p ≠ 0)
    (hEq :
      (d0 + d1 * (E / p)) * (A / p^2) =
        (E / p) * (M - E / p) * (r0 + d1 * (E / p))) :
    A * (d0 * p + d1 * E) =
      E * (M * p - E) * (r0 * p + d1 * E) := by
  have h := hEq
  field_simp [hp] at h
  ring_nf at h ⊢
  exact h

/-- A fraction-field complementary equation gives the exact polynomial
`ComplementaryClearedEquation`.  Injectivity of the polynomial embedding into
its fraction field is the only descent principle used. -/
theorem complementary_cleared_equation_of_fraction_equation
    {K : Type*} [Field K]
    {phi : Polynomial K} {A0 B0 M h k : K}
    (hphi : phi ≠ 0)
    (hEq : ComplementaryFractionEquation phi A0 B0 M h k) :
    ComplementaryClearedEquation phi A0 B0 M h k := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hp : ι phi ≠ 0 := by
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr hphi
  have hfrac :
      (ι (Polynomial.C (A0 * M * h * (B0 * M * k - 1))) +
          ι (Polynomial.C (A0 * h - B0 * k)) *
            (ι (eulerDerivative phi) / ι phi)) *
          (ι (logarithmicEtaNumerator phi) / (ι phi)^2) =
        (ι (eulerDerivative phi) / ι phi) *
          (ι (Polynomial.C M) - ι (eulerDerivative phi) / ι phi) *
          (ι (Polynomial.C (B0 * M * k - 1)) +
            ι (Polynomial.C (A0 * h - B0 * k)) *
              (ι (eulerDerivative phi) / ι phi)) := by
    simpa [ComplementaryFractionEquation, F, ι] using hEq
  have hclear :=
    complementary_scalar_fraction_equation_clears
      (F := F)
      (p := ι phi)
      (E := ι (eulerDerivative phi))
      (A := ι (logarithmicEtaNumerator phi))
      (d0 := ι (Polynomial.C (A0 * M * h * (B0 * M * k - 1))))
      (d1 := ι (Polynomial.C (A0 * h - B0 * k)))
      (M := ι (Polynomial.C M))
      (r0 := ι (Polynomial.C (B0 * M * k - 1)))
      hp hfrac
  unfold ComplementaryClearedEquation
  apply IsFractionRing.injective (Polynomial K) F
  simpa only [map_mul, map_add, map_sub] using hclear

/-- Repackage the scalar complementary `eta` equation into the factored
form used for denominator clearing.  Keeping `rho` and `eta` as abstract ring
elements prevents fraction-field normalisation from unfolding them. -/
theorem complementary_eta_equation_repackaged
    {F : Type*} [CommRing F]
    {a1 a2 b1 b2 h k M rho eta : F}
    (hEq :
      ((a1 + a2) * (b1 + b2) * M^2 * h * k
          - (a1 + a2) * M * h
          + ((a1 + a2) * h - (b1 + b2) * k) * rho) * eta =
        rho * (M - rho) *
          ((b1 + b2) * M * k
            + ((a1 + a2) * h - (b1 + b2) * k) * rho - 1)) :
    (((a1 + a2) * M * h * ((b1 + b2) * M * k - 1)
          + ((a1 + a2) * h - (b1 + b2) * k) * rho) * eta =
      rho * (M - rho) *
        (((b1 + b2) * M * k - 1)
          + ((a1 + a2) * h - (b1 + b2) * k) * rho)) := by
  ring_nf at hEq ⊢
  exact hEq

/-- Vanishing of the complementary logarithmic-Hessian core in the fraction
field gives the normalised fraction equation, provided `phi`, `E`, and
`M*phi-E` are nonzero. -/
theorem complementary_fraction_equation_of_core_det_zero
    {K : Type*} [Field K]
    {phi : Polynomial K} {a1 a2 b1 b2 h k M : K}
    (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (hh : h ≠ 0) (hk : k ≠ 0)
    (hphi : phi ≠ 0)
    (hE : eulerDerivative phi ≠ 0)
    (hME : Polynomial.C M * phi - eulerDerivative phi ≠ 0)
    (hdet : ComplementaryFractionCoreDetZero phi a1 a2 b1 b2 h k M) :
    ComplementaryFractionEquation phi (a1 + a2) (b1 + b2) M h k := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let p : F := ι phi
  let E : F := ι (eulerDerivative phi)
  let A : F := ι (logarithmicEtaNumerator phi)
  let rho : F := E / p
  let eta : F := A / p^2

  have hp : p ≠ 0 := by
    dsimp [p]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr hphi
  have hER : E ≠ 0 := by
    dsimp [E]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr hE
  have hMER :
      ι (Polynomial.C M) * p - E ≠ 0 := by
    have hmap : ι (Polynomial.C M * phi - eulerDerivative phi) ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff).not.mpr hME
    dsimp [p, E]
    simpa only [map_sub, map_mul] using hmap
  have hrho : rho ≠ 0 := by
    dsimp [rho]
    exact div_ne_zero hER hp
  have hMrho : ι (Polynomial.C M) - rho ≠ 0 := by
    intro hz
    have heq : ι (Polynomial.C M) = E / p := sub_eq_zero.mp hz
    have hmul : ι (Polynomial.C M) * p = E := (eq_div_iff hp).mp heq
    exact hMER (sub_eq_zero.mpr hmul)

  have ha1R : ι (Polynomial.C a1) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr ha1)
  have ha2R : ι (Polynomial.C a2) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr ha2)
  have hb1R : ι (Polynomial.C b1) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr hb1)
  have hb2R : ι (Polynomial.C b2) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr hb2)
  have hhR : ι (Polynomial.C h) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr hh)
  have hkR : ι (Polynomial.C k) ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff).not.mpr (Polynomial.C_ne_zero.mpr hk)

  have hdet' :
      (complementaryLogHessianCore
          (ι (Polynomial.C a1)) (ι (Polynomial.C a2))
          (ι (Polynomial.C b1)) (ι (Polynomial.C b2))
          (ι (Polynomial.C h)) (ι (Polynomial.C k))
          (ι (Polynomial.C M)) rho eta).det = 0 := by
    simpa [ComplementaryFractionCoreDetZero, F, ι, p, E, A, rho, eta] using hdet

  have hscalar :=
    complementary_eta_equation_of_det_zero
      (K := F)
      (a1 := ι (Polynomial.C a1)) (a2 := ι (Polynomial.C a2))
      (b1 := ι (Polynomial.C b1)) (b2 := ι (Polynomial.C b2))
      (h := ι (Polynomial.C h)) (k := ι (Polynomial.C k))
      (M := ι (Polynomial.C M)) (rho := rho) (eta := eta)
      ha1R ha2R hb1R hb2R hhR hkR hrho hMrho hdet'

  have hpacked := complementary_eta_equation_repackaged hscalar
  simpa [ComplementaryFractionEquation, F, ι, p, E, A, rho, eta,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul,
    Polynomial.C_1, map_add, map_sub, map_mul, map_one] using hpacked

/-- The fraction-field complementary equation is impossible for a genuine
least-positive local term under the natural positive-exponent hypotheses. -/
theorem complementary_fraction_equation_local_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k m : ℕ}
    {c : K} {q : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hEq : ComplementaryFractionEquation
      (Polynomial.C c + Polynomial.X ^ m * q)
      ((alpha1 + alpha2 : ℕ) : K)
      ((beta1 + beta2 : ℕ) : K)
      (M : K) (h : K) (k : K)) : False := by
  let phi : Polynomial K := Polynomial.C c + Polynomial.X ^ m * q
  have hphi : phi ≠ 0 := by
    intro hz
    have hz0 := congrArg (Polynomial.eval 0) hz
    apply hc
    simpa [phi, Nat.ne_of_gt hm] using hz0
  have hclear :=
    complementary_cleared_equation_of_fraction_equation
      (K := K) hphi hEq
  exact complementary_cleared_equation_impossible
    (K := K) ha1 ha2 hb1 hb2 hM hh hk hm hc hq0 hclear

/-- End-to-end obstruction from the *fraction-field logarithmic-Hessian core*
to contradiction for a genuine complementary local term.

This closes the algebra from the core determinant onward.  It does not by
itself prove that every actual complementary Newton edge has this core; that
upstream identification remains a separate theorem if not already present. -/
theorem complementary_fraction_core_local_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k m : ℕ}
    {c : K} {q : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hdet : ComplementaryFractionCoreDetZero
      (Polynomial.C c + Polynomial.X ^ m * q)
      (alpha1 : K) (alpha2 : K) (beta1 : K) (beta2 : K)
      (h : K) (k : K) (M : K)) : False := by
  let phi : Polynomial K := Polynomial.C c + Polynomial.X ^ m * q
  have hmK : (m : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hMK : (M : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  have hphi : phi ≠ 0 := by
    intro hz
    have hz0 := congrArg (Polynomial.eval 0) hz
    apply hc
    simpa [phi, Nat.ne_of_gt hm] using hz0
  have hE : eulerDerivative phi ≠ 0 := by
    intro hz
    have hzcoeff : (eulerDerivative phi).coeff m = 0 := by
      rw [hz]
      rfl
    have hcoeff := coeff_m_eulerDerivative_local_form c q m
    change (eulerDerivative phi).coeff m = (m : K) * q.coeff 0 at hcoeff
    rw [hzcoeff] at hcoeff
    exact (mul_ne_zero hmK hq0) hcoeff.symm
  have hME : Polynomial.C (M : K) * phi - eulerDerivative phi ≠ 0 := by
    intro hz
    have hz0 := congrArg (Polynomial.eval 0) hz
    have hzero : (M : K) * c = 0 := by
      simpa [phi, eulerDerivative, Nat.ne_of_gt hm] using hz0
    exact (mul_ne_zero hMK hc) hzero

  have ha1K : (alpha1 : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha1)
  have ha2K : (alpha2 : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha2)
  have hb1K : (beta1 : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb1)
  have hb2K : (beta2 : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb2)
  have hhK : (h : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hh)
  have hkK : (k : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)

  have hfrac :=
    complementary_fraction_equation_of_core_det_zero
      (K := K)
      ha1K ha2K hb1K hb2K hhK hkK hphi hE hME
      (by simpa [phi] using hdet)
  have hfrac' : ComplementaryFractionEquation phi
      ((alpha1 + alpha2 : ℕ) : K)
      ((beta1 + beta2 : ℕ) : K)
      (M : K) (h : K) (k : K) := by
    simpa [Nat.cast_add] using hfrac
  exact complementary_fraction_equation_local_impossible
    (K := K) ha1 ha2 hb1 hb2 hM hh hk hm hc hq0
    (by simpa [phi] using hfrac')

end

end HC4.Polynomial
