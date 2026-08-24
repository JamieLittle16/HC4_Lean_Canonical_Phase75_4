import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTransverseOrder
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurHomogeneousLinearPower
import Mathlib.Tactic

/-!
# Terminal transverse jets of the stationary binary staircase

The preceding stationary-core stages produce exact transverse-order data for
homogeneous binary layers with respect to

    D_perp = c₁ ∂₀ - c₀ ∂₁,
    L      = c₀ X₀ + c₁ X₁.

The older homogeneous-linear-power machinery already proves the hard
characteristic-zero statement needed here: a positive-degree homogeneous
polynomial whose gradient has one fixed constant ratio is a scalar multiple
of a power of the corresponding linear form.

This file connects those two developments.

If a homogeneous layer `P` has exact transverse order `r`, its terminal jet

    J = D_perp^r P

is nonzero and is killed by `D_perp`.  Hence `J` is exactly

    b * L^(E-r)

(up to the degree-zero constant case, which is the same formula with power
zero).  In particular, for the curved stationary branch

    D_perp G      = b₁ L^(E-1),
    D_perp² K     = b₂ L^(F-2),

with both coefficients nonzero.

The Hessian determinant of `G` is itself homogeneous and `D_perp`-locked by
the already-green negative-square argument, so it too has an exact power
profile

    det Hess G = κ L^((E-2)+(E-2)),   κ != 0.

These are the scalar terminal jets used by the final finite staircase.  No
new coordinate change or coefficient recurrence is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Scaling the old gradient-ratio linear form -/

/-- Scaling every coefficient of `gradientRatioLinearForm` scales the whole
linear form by the same constant polynomial. -/
theorem gradientRatioLinearForm_scale_finTwo
    (s : K)
    (c : Fin 2 → K) :
    gradientRatioLinearForm (fun i => s * c i) =
      MvPolynomial.C s * gradientRatioLinearForm c := by
  classical
  unfold gradientRatioLinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.C_mul, mul_assoc]

/-- Normalising by the first nonzero coefficient merely rescales the same
linear form. -/
theorem gradientRatioLinearForm_div_zero
    (c : Fin 2 → K)
    (hc0 : c 0 ≠ 0) :
    gradientRatioLinearForm (fun i => c i / c 0) =
      MvPolynomial.C ((c 0)⁻¹) * gradientRatioLinearForm c := by
  have hfun :
      (fun i : Fin 2 => c i / c 0) =
        (fun i : Fin 2 => (c 0)⁻¹ * c i) := by
    funext i
    simp only [div_eq_mul_inv]
    ring
  rw [hfun, gradientRatioLinearForm_scale_finTwo]

/-- Symmetric normalisation by the second nonzero coefficient. -/
theorem gradientRatioLinearForm_div_one
    (c : Fin 2 → K)
    (hc1 : c 1 ≠ 0) :
    gradientRatioLinearForm (fun i => c i / c 1) =
      MvPolynomial.C ((c 1)⁻¹) * gradientRatioLinearForm c := by
  have hfun :
      (fun i : Fin 2 => c i / c 1) =
        (fun i : Fin 2 => (c 1)⁻¹ * c i) := by
    funext i
    simp only [div_eq_mul_inv]
    ring
  rw [hfun, gradientRatioLinearForm_scale_finTwo]

/-! ## A locked homogeneous binary polynomial is a power of the top line -/

/-- The transverse lock is the denominator-free proportionality of the two
binary partial derivatives. -/
theorem transverseLock_scaled_pderivs
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K)
    (hlock : binaryLinearFormTransverseDeriv c P = 0) :
    MvPolynomial.C (c 0) * MvPolynomial.pderiv (1 : Fin 2) P =
      MvPolynomial.C (c 1) * MvPolynomial.pderiv (0 : Fin 2) P := by
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv at hlock
  rw [MvPolynomial.C_neg] at hlock
  linear_combination -hlock

/-- In the first-pivot orientation a positive-degree nonzero locked
homogeneous polynomial has nonzero first partial derivative. -/
theorem pderiv_zero_ne_zero_of_transverseLock
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K)
    (m : ℕ)
    (hhom : P.IsHomogeneous m)
    (hm : 0 < m)
    (hP : P ≠ 0)
    (hc0 : c 0 ≠ 0)
    (hlock : binaryLinearFormTransverseDeriv c P = 0) :
    MvPolynomial.pderiv (0 : Fin 2) P ≠ 0 := by
  intro hp0
  have hscaled := transverseLock_scaled_pderivs c P hlock
  have hp1 : MvPolynomial.pderiv (1 : Fin 2) P = 0 := by
    have hz :
        MvPolynomial.C (c 0) * MvPolynomial.pderiv (1 : Fin 2) P = 0 := by
      simpa [hp0] using hscaled
    exact (mul_eq_zero.mp hz).resolve_left (MvPolynomial.C_ne_zero.mpr hc0)
  rcases homogeneous_exists_pderiv_ne_zero P m hhom hP hm with ⟨i, hi⟩
  fin_cases i
  · exact hi hp0
  · exact hi hp1

/-- Symmetric second-pivot version. -/
theorem pderiv_one_ne_zero_of_transverseLock
    (c : Fin 2 → K)
    (P : MvPolynomial (Fin 2) K)
    (m : ℕ)
    (hhom : P.IsHomogeneous m)
    (hm : 0 < m)
    (hP : P ≠ 0)
    (hc1 : c 1 ≠ 0)
    (hlock : binaryLinearFormTransverseDeriv c P = 0) :
    MvPolynomial.pderiv (1 : Fin 2) P ≠ 0 := by
  intro hp1
  have hscaled := transverseLock_scaled_pderivs c P hlock
  have hp0 : MvPolynomial.pderiv (0 : Fin 2) P = 0 := by
    have hz :
        MvPolynomial.C (c 1) * MvPolynomial.pderiv (0 : Fin 2) P = 0 := by
      simpa [hp1] using hscaled.symm
    exact (mul_eq_zero.mp hz).resolve_left (MvPolynomial.C_ne_zero.mpr hc1)
  rcases homogeneous_exists_pderiv_ne_zero P m hhom hP hm with ⟨i, hi⟩
  fin_cases i
  · exact hi hp0
  · exact hi hp1

/-- **Locked homogeneous binary power theorem.**

This is the stationary-core specialization of the older
`homogeneous_eq_C_mul_gradientRatioLinearForm_pow`: the annihilating
transverse direction is converted into global gradient ratios by choosing
whichever coefficient of `L` is nonzero, and the harmless normalising scalar
is absorbed into the final coefficient. -/
theorem homogeneous_eq_C_mul_topLinearForm_pow_of_transverseLock
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (P : MvPolynomial (Fin 2) K)
    (m : ℕ)
    (hhom : P.IsHomogeneous m)
    (hm : 0 < m)
    (hP : P ≠ 0)
    (hlock : binaryLinearFormTransverseDeriv c P = 0) :
    ∃ b : K,
      P = MvPolynomial.C b * (gradientRatioLinearForm c) ^ m := by
  rcases gradientRatioLinearForm_component_ne_zero c hL with hc0 | hc1
  · let ratio : Fin 2 → K := fun i => c i / c 0
    have hpivot : MvPolynomial.pderiv (0 : Fin 2) P ≠ 0 :=
      pderiv_zero_ne_zero_of_transverseLock c P m hhom hm hP hc0 hlock
    have hscaled := transverseLock_scaled_pderivs c P hlock
    have hprop :
        ∀ i : Fin 2,
          MvPolynomial.pderiv i P =
            MvPolynomial.C (ratio i) *
              MvPolynomial.pderiv (0 : Fin 2) P := by
      intro i
      fin_cases i
      · simp [ratio, hc0]
      · apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hc0)
        calc
          MvPolynomial.C (c 0) * MvPolynomial.pderiv (1 : Fin 2) P =
              MvPolynomial.C (c 1) * MvPolynomial.pderiv (0 : Fin 2) P :=
            hscaled
          _ = MvPolynomial.C (c 0) *
                (MvPolynomial.C (ratio 1) *
                  MvPolynomial.pderiv (0 : Fin 2) P) := by
              rw [← mul_assoc, ← MvPolynomial.C_mul]
              have hs : c 0 * ratio 1 = c 1 := by
                dsimp [ratio]
                field_simp [hc0]
              rw [hs]
    rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
        m P hhom hm (0 : Fin 2) hpivot ratio hprop with ⟨a, ha⟩
    have hratio :
        gradientRatioLinearForm ratio =
          MvPolynomial.C ((c 0)⁻¹) * gradientRatioLinearForm c := by
      simpa [ratio] using gradientRatioLinearForm_div_zero c hc0
    refine ⟨a * ((c 0)⁻¹) ^ m, ?_⟩
    rw [ha, hratio, mul_pow]
    rw [← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]
  · let ratio : Fin 2 → K := fun i => c i / c 1
    have hpivot : MvPolynomial.pderiv (1 : Fin 2) P ≠ 0 :=
      pderiv_one_ne_zero_of_transverseLock c P m hhom hm hP hc1 hlock
    have hscaled := transverseLock_scaled_pderivs c P hlock
    have hprop :
        ∀ i : Fin 2,
          MvPolynomial.pderiv i P =
            MvPolynomial.C (ratio i) *
              MvPolynomial.pderiv (1 : Fin 2) P := by
      intro i
      fin_cases i
      · apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hc1)
        calc
          MvPolynomial.C (c 1) * MvPolynomial.pderiv (0 : Fin 2) P =
              MvPolynomial.C (c 0) * MvPolynomial.pderiv (1 : Fin 2) P :=
            hscaled.symm
          _ = MvPolynomial.C (c 1) *
                (MvPolynomial.C (ratio 0) *
                  MvPolynomial.pderiv (1 : Fin 2) P) := by
              rw [← mul_assoc, ← MvPolynomial.C_mul]
              have hs : c 1 * ratio 0 = c 0 := by
                dsimp [ratio]
                field_simp [hc1]
              rw [hs]
      · simp [ratio, hc1]
    rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
        m P hhom hm (1 : Fin 2) hpivot ratio hprop with ⟨a, ha⟩
    have hratio :
        gradientRatioLinearForm ratio =
          MvPolynomial.C ((c 1)⁻¹) * gradientRatioLinearForm c := by
      simpa [ratio] using gradientRatioLinearForm_div_one c hc1
    refine ⟨a * ((c 1)⁻¹) ^ m, ?_⟩
    rw [ha, hratio, mul_pow]
    rw [← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]

/-! ## Terminal jet normal form for arbitrary exact order -/

/-- The terminal nonzero transverse jet of a homogeneous binary layer is a
nonzero scalar times the corresponding power of the locked top line.

The degree-zero endpoint is included: then the power is `L^0 = 1` and the
terminal jet is simply a nonzero constant. -/
theorem exactTransverseOrder_terminalJet_linearPower
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (P : MvPolynomial (Fin 2) K)
    (E r : ℕ)
    (hhom : P.IsHomogeneous E)
    (horder : HasExactBinaryLinearFormTransverseOrder c r P) :
    ∃ b : K,
      b ≠ 0 ∧
      iteratedBinaryLinearFormTransverseDeriv c r P =
        MvPolynomial.C b * (gradientRatioLinearForm c) ^ (E - r) := by
  let J := iteratedBinaryLinearFormTransverseDeriv c r P
  have hJhom : J.IsHomogeneous (E - r) := by
    dsimp [J]
    exact iteratedBinaryLinearFormTransverseDeriv_isHomogeneous c P E r hhom
  have hJne : J ≠ 0 := by
    simpa [J] using horder.1
  have hJlock : binaryLinearFormTransverseDeriv c J = 0 := by
    have hz := horder.2
    change binaryLinearFormTransverseDeriv c J = 0
    simpa [J] using hz
  by_cases hm : E - r = 0
  · have hzero : J.IsHomogeneous 0 := by simpa [hm] using hJhom
    have hconst := homogeneous_zero_eq_C_constantCoeff_fin hzero
    let b : K := MvPolynomial.constantCoeff J
    have hb : b ≠ 0 := by
      intro hb
      apply hJne
      rw [hconst]
      simpa [b, hb]
    refine ⟨b, hb, ?_⟩
    rw [hm]
    simpa [b] using hconst
  · have hmpos : 0 < E - r := Nat.pos_of_ne_zero hm
    rcases homogeneous_eq_C_mul_topLinearForm_pow_of_transverseLock
        c hL J (E - r) hJhom hmpos hJne hJlock with ⟨b, hbform⟩
    have hb : b ≠ 0 := by
      intro hb0
      apply hJne
      rw [hbform, hb0]
      simp
    exact ⟨b, hb, hbform⟩

/-! ## Exact power profile of a homogeneous binary Hessian determinant -/

/-- The Hessian determinant of an ordinary homogeneous binary form of degree
`E` is homogeneous of degree `(E-2)+(E-2)`. -/
theorem binaryDirectionalHessianDet_isHomogeneous
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hhom : G.IsHomogeneous E) :
    (binaryDirectionalHessianDet (0 : Fin 2) 1 G).IsHomogeneous
      ((E - 2) + (E - 2)) := by
  have h0 :
      (MvPolynomial.pderiv (0 : Fin 2) G).IsHomogeneous (E - 1) := by
    simpa using hhom.pderiv
  have h1 :
      (MvPolynomial.pderiv (1 : Fin 2) G).IsHomogeneous (E - 1) := by
    simpa using hhom.pderiv
  have h00 :
      (directionalSecondDerivative (0 : Fin 2) G).IsHomogeneous (E - 2) := by
    have h :
        (MvPolynomial.pderiv (0 : Fin 2)
          (MvPolynomial.pderiv (0 : Fin 2) G)).IsHomogeneous ((E - 1) - 1) := by
      simpa using h0.pderiv
    have hdeg : (E - 1) - 1 = E - 2 := by omega
    simpa [directionalSecondDerivative, hdeg] using h
  have h11 :
      (directionalSecondDerivative (1 : Fin 2) G).IsHomogeneous (E - 2) := by
    have h :
        (MvPolynomial.pderiv (1 : Fin 2)
          (MvPolynomial.pderiv (1 : Fin 2) G)).IsHomogeneous ((E - 1) - 1) := by
      simpa using h1.pderiv
    have hdeg : (E - 1) - 1 = E - 2 := by omega
    simpa [directionalSecondDerivative, hdeg] using h
  have h01 :
      (directionalMixedDerivative (0 : Fin 2) 1 G).IsHomogeneous (E - 2) := by
    have h :
        (MvPolynomial.pderiv (0 : Fin 2)
          (MvPolynomial.pderiv (1 : Fin 2) G)).IsHomogeneous ((E - 1) - 1) := by
      simpa using h1.pderiv
    have hdeg : (E - 1) - 1 = E - 2 := by omega
    simpa [directionalMixedDerivative, hdeg] using h
  have hprod := h00.mul h11
  have hsq := h01.mul h01
  simpa [binaryDirectionalHessianDet, pow_two] using hprod.sub hsq

/-- A curved homogeneous order-one layer has a Hessian determinant which is
not only nonzero, but exactly a nonzero scalar times a power of the same
locked line. -/
theorem curvedOrderOne_hessianDet_linearPower
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hE : 2 ≤ E)
    (hhom : G.IsHomogeneous E)
    (horder : HasExactBinaryLinearFormTransverseOrder c 1 G) :
    ∃ κ : K,
      κ ≠ 0 ∧
      binaryDirectionalHessianDet (0 : Fin 2) 1 G =
        MvPolynomial.C κ *
          (gradientRatioLinearForm c) ^ ((E - 2) + (E - 2)) := by
  have hfirst : binaryLinearFormTransverseDeriv c G ≠ 0 := by
    simpa [HasExactBinaryLinearFormTransverseOrder,
      iteratedBinaryLinearFormTransverseDeriv] using horder.1
  have hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0 := by
    simpa [HasExactBinaryLinearFormTransverseOrder,
      iteratedBinaryLinearFormTransverseDeriv] using horder.2
  have hdetne : binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0 :=
    binaryHessianDet_ne_zero_of_transverse_sq_zero_of_transverse_ne_zero
      c G E hE hhom hsq hfirst
  have hdetlock :
      binaryLinearFormTransverseDeriv c
        (binaryDirectionalHessianDet (0 : Fin 2) 1 G) = 0 :=
    binaryLinearFormTransverseDeriv_hessianDet_eq_zero_of_sq_zero
      c G hL hsq
  have hdetHom := binaryDirectionalHessianDet_isHomogeneous G E hhom
  let M := (E - 2) + (E - 2)
  have hdetOrder :
      HasExactBinaryLinearFormTransverseOrder c 0
        (binaryDirectionalHessianDet (0 : Fin 2) 1 G) := by
    constructor
    · simpa [iteratedBinaryLinearFormTransverseDeriv] using hdetne
    · simpa [iteratedBinaryLinearFormTransverseDeriv] using hdetlock
  rcases exactTransverseOrder_terminalJet_linearPower
      c hL (binaryDirectionalHessianDet (0 : Fin 2) 1 G)
      M 0 (by simpa [M] using hdetHom) hdetOrder with ⟨κ, hκ, hform⟩
  refine ⟨κ, hκ, ?_⟩
  simpa [M, iteratedBinaryLinearFormTransverseDeriv] using hform

/-- The terminal first jet of an order-one curved homogeneous layer is an
exact nonzero `L^(E-1)` profile. -/
theorem curvedOrderOne_terminalJet_linearPower
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hhom : G.IsHomogeneous E)
    (horder : HasExactBinaryLinearFormTransverseOrder c 1 G) :
    ∃ b : K,
      b ≠ 0 ∧
      binaryLinearFormTransverseDeriv c G =
        MvPolynomial.C b * (gradientRatioLinearForm c) ^ (E - 1) := by
  rcases exactTransverseOrder_terminalJet_linearPower
      c hL G E 1 hhom horder with ⟨b, hb, hform⟩
  exact ⟨b, hb, by simpa [iteratedBinaryLinearFormTransverseDeriv] using hform⟩

/-- The terminal second jet of the forced order-two compensator is an exact
nonzero `L^(F-2)` profile. -/
theorem orderTwo_terminalJet_linearPower
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (Klower : MvPolynomial (Fin 2) K)
    (F : ℕ)
    (hhom : Klower.IsHomogeneous F)
    (horder : HasExactBinaryLinearFormTransverseOrder c 2 Klower) :
    ∃ b : K,
      b ≠ 0 ∧
      binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c Klower) =
        MvPolynomial.C b * (gradientRatioLinearForm c) ^ (F - 2) := by
  rcases exactTransverseOrder_terminalJet_linearPower
      c hL Klower F 2 hhom horder with ⟨b, hb, hform⟩
  exact ⟨b, hb, by simpa [iteratedBinaryLinearFormTransverseDeriv] using hform⟩

/-! ## Scalar balance at the first forced compensation -/

/-- After the exact terminal-jet profiles are substituted, the polynomial
compensation identity is a single nonzero power of `L` times a scalar
identity.  Cancelling that power records the coefficient recurrence which
seeds the final staircase. -/
theorem forcedCompensator_terminalCoefficient_balance
    (H G Klower : MvPolynomial (Fin 2) K)
    (D E F : ℕ)
    (hD : 2 ≤ D)
    (hE : 2 ≤ E)
    (hF : 2 ≤ F)
    (F_eq : F = 2 * E - D)
    (a : K)
    (c : Fin 2 → K)
    (hL : gradientRatioLinearForm c ≠ 0)
    (normalForm :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (compensation :
      binaryHessianDetCross H Klower =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G)
    (κ bK : K)
    (det_profile :
      binaryDirectionalHessianDet (0 : Fin 2) 1 G =
        MvPolynomial.C κ *
          (gradientRatioLinearForm c) ^ ((E - 2) + (E - 2)))
    (K_terminal_jet :
      binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c Klower) =
        MvPolynomial.C bK * (gradientRatioLinearForm c) ^ (F - 2)) :
    a * ((((D - 2) + 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) * bK = -κ := by
  let n := D - 2
  have hDn : D = n + 2 := by
    dsimp [n]
    omega
  have hfac := binaryHessianDetCross_linearPower_factor a c n Klower
  have hnormal :
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2) := by
    rw [← hDn]
    exact normalForm
  rw [← hnormal] at hfac
  let A : K := a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K))
  have hcomp :
      MvPolynomial.C A * (gradientRatioLinearForm c) ^ n *
          binaryLinearFormTransverseDeriv c
            (binaryLinearFormTransverseDeriv c Klower) =
        - binaryDirectionalHessianDet (0 : Fin 2) 1 G := by
    dsimp [A]
    rw [← hfac]
    exact compensation
  rw [K_terminal_jet, det_profile] at hcomp
  have hexp :
      n + (F - 2) = (E - 2) + (E - 2) := by
    dsimp [n]
    omega
  let M := (E - 2) + (E - 2)
  have hpoly :
      MvPolynomial.C (A * bK) * (gradientRatioLinearForm c) ^ M =
        MvPolynomial.C (-κ) * (gradientRatioLinearForm c) ^ M := by
    calc
      MvPolynomial.C (A * bK) * (gradientRatioLinearForm c) ^ M =
          MvPolynomial.C A * (gradientRatioLinearForm c) ^ n *
            (MvPolynomial.C bK * (gradientRatioLinearForm c) ^ (F - 2)) := by
        dsimp [M]
        rw [MvPolynomial.C_mul, ← hexp, pow_add]
        ring
      _ = - (MvPolynomial.C κ *
          (gradientRatioLinearForm c) ^ ((E - 2) + (E - 2))) := hcomp
      _ = MvPolynomial.C (-κ) * (gradientRatioLinearForm c) ^ M := by
        simp [M]
  have hpow : (gradientRatioLinearForm c) ^ M ≠ 0 := pow_ne_zero M hL
  have hC :
      (MvPolynomial.C (A * bK) : MvPolynomial (Fin 2) K) =
        MvPolynomial.C (-κ) := by
    exact mul_right_cancel₀ hpow hpoly
  have hscalar : A * bK = -κ := by
    exact MvPolynomial.C_injective (Fin 2) K hC
  change A * bK = -κ
  exact hscalar

/-! ## Assembly-facing terminal-jet frontier -/

/-- The order frontier with the genuinely curved branch upgraded to exact
scalar terminal-jet normal forms. -/
inductive BinarySingularHessianTransverseJetFrontier
    (Q : MvPolynomial (Fin 2) K) : Type (u + 1)
  | lowDegree
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
  | nonlinearCollapsed
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (Q_eq_H : Q = H)
  | nonlinearNextAffine
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (E_le_one : E ≤ 1)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero :
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) = 0)
  | nonlinearNextLocked
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (E_ge_two : 2 ≤ E)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (transverse_sq_zero :
        binaryLinearFormTransverseDeriv c
          (binaryLinearFormTransverseDeriv c G) = 0)
      (transverse_first_zero : binaryLinearFormTransverseDeriv c G = 0)
  | nonlinearNextCurvedJets
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (E_ge_two : 2 ≤ E)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (G_order_one : HasExactBinaryLinearFormTransverseOrder c 1 G)
      (next_det_ne_zero :
        binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0)
      (F : ℕ)
      (Klower : MvPolynomial (Fin 2) K)
      (F_eq : F = 2 * E - D)
      (F_ge_two : 2 ≤ F)
      (F_lt_E : F < E)
      (Klower_eq : Klower = binaryOrdinaryDegreeComponent R F)
      (Klower_ne_zero : Klower ≠ 0)
      (Klower_homogeneous : Klower.IsHomogeneous F)
      (compensation :
        binaryHessianDetCross H Klower =
          - binaryDirectionalHessianDet (0 : Fin 2) 1 G)
      (Klower_order_two : HasExactBinaryLinearFormTransverseOrder c 2 Klower)
      (G_jet_coefficient : K)
      (G_jet_coefficient_ne_zero : G_jet_coefficient ≠ 0)
      (G_terminal_jet :
        binaryLinearFormTransverseDeriv c G =
          MvPolynomial.C G_jet_coefficient *
            (gradientRatioLinearForm c) ^ (E - 1))
      (det_coefficient : K)
      (det_coefficient_ne_zero : det_coefficient ≠ 0)
      (G_det_profile :
        binaryDirectionalHessianDet (0 : Fin 2) 1 G =
          MvPolynomial.C det_coefficient *
            (gradientRatioLinearForm c) ^ ((E - 2) + (E - 2)))
      (K_jet_coefficient : K)
      (K_jet_coefficient_ne_zero : K_jet_coefficient ≠ 0)
      (K_terminal_jet :
        binaryLinearFormTransverseDeriv c
            (binaryLinearFormTransverseDeriv c Klower) =
          MvPolynomial.C K_jet_coefficient *
            (gradientRatioLinearForm c) ^ (F - 2))
      (coefficient_balance :
        a * ((((D - 2) + 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) *
            K_jet_coefficient = -det_coefficient)

/-- Every exact-order frontier upgrades to scalar terminal-jet normal forms. -/
theorem binarySingularHessian_transverseJetFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianTransverseJetFrontier Q) := by
  rcases binarySingularHessian_transverseOrderFrontier Q hQ hdet with ⟨F0⟩
  cases F0 with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
        a c normalForm Q_eq_H⟩
  | nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero =>
      exact ⟨.nonlinearNextAffine D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero
        remainder_maximal G_homogeneous transverse_sq_zero⟩
  | nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
      remainder_maximal G_homogeneous transverse_sq_zero transverse_first_zero =>
      exact ⟨.nonlinearNextLocked D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
        remainder_maximal G_homogeneous transverse_sq_zero transverse_first_zero⟩
  | nonlinearNextCurvedOrderTwo D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
      G_homogeneous G_order_one next_det_ne_zero F Klower F_eq F_ge_two F_lt_E
      Klower_eq Klower_ne_zero Klower_homogeneous compensation Klower_order_two =>
      have hL : gradientRatioLinearForm c ≠ 0 :=
        gradientRatioLinearForm_ne_zero_of_linearPower_ne_zero
          H D (by omega) H_ne_zero a c normalForm
      rcases curvedOrderOne_terminalJet_linearPower
          c hL G E G_homogeneous G_order_one with ⟨bG, hbG, hGjet⟩
      rcases curvedOrderOne_hessianDet_linearPower
          c hL G E E_ge_two G_homogeneous G_order_one with ⟨κ, hκ, hdetprof⟩
      rcases orderTwo_terminalJet_linearPower
          c hL Klower F Klower_homogeneous Klower_order_two with
        ⟨bK, hbK, hKjet⟩
      have hbalance := forcedCompensator_terminalCoefficient_balance
        H G Klower D E F hD E_ge_two F_ge_two F_eq a c hL normalForm
        compensation κ bK hdetprof hKjet
      exact ⟨.nonlinearNextCurvedJets D H hD H_eq H_ne_zero maximal
        a c normalForm R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero
        remainder_maximal G_homogeneous G_order_one next_det_ne_zero
        F Klower F_eq F_ge_two F_lt_E Klower_eq Klower_ne_zero
        Klower_homogeneous compensation Klower_order_two
        bG hbG hGjet κ hκ hdetprof bK hbK hKjet hbalance⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing terminal-jet frontier for the stationary HC4 binary face. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.transverseJetFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianTransverseJetFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_transverseJetFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
