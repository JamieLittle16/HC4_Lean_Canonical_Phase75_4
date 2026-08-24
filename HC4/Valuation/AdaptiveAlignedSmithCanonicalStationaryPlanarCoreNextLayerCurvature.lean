import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreDirectionLock
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Curvature certificate for the first layer below a locked binary top layer

The direction-lock stage gives, for the next homogeneous layer `G`,

    D_perp (D_perp G) = 0,

where `D_perp = c₁ ∂₀ - c₀ ∂₁` is transverse to the top linear form
`L = c₀ X₀ + c₁ X₁`.

There are two genuinely different nonlinear possibilities.

* If `D_perp G = 0`, the next layer is already invariant in the same
  transverse direction as the top layer.
* If `D_perp G != 0`, then the Hessian determinant of `G` is nonzero.

The second assertion follows from a coordinate-free negative-square
identity.  Put `P = D_perp G`.  From `D_perp P = 0` one gets

    c₁² det(Hess G) = -(∂₁ P)²,
    c₀² det(Hess G) = -(∂₀ P)².

For a homogeneous layer of degree at least two, `P` has positive homogeneous
binary degree.  If `P != 0`, the derivative selected by any nonzero pivot
component of `c` cannot vanish: together with `D_perp P = 0` that would make
both partial derivatives of `P` vanish, contradicting positive homogeneous
degree in characteristic zero.

Thus a nontrivial transverse tangent at the next layer produces an honest
nonzero Hessian determinant at that layer.  This is stronger than an
explicit two-term coordinate normal form for the next global step: because
the full binary core still has determinant zero, the nonzero degree
`2E-4` curvature must be compensated by a strictly lower homogeneous layer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Homogeneous binary support bookkeeping -/

/-- Ordinary homogeneity on `Fin 2` is the same as exact degree in the two
binary coordinates. -/
theorem binaryHomogeneous_hasExactTransverseDegree
    (P : MvPolynomial (Fin 2) K)
    (n : ℕ)
    (hhom : P.IsHomogeneous n) :
    HasExactTransverseDegree (0 : Fin 2) 1 n P := by
  intro d hd
  have hdeg : d.degree = n := by
    have hweightOne :
        Finsupp.weight (1 : Fin 2 → ℕ) d = d.degree :=
      (congrFun Finsupp.degree_eq_weight_one d).symm
    exact hweightOne.symm.trans (hhom hd)
  calc
    d (0 : Fin 2) + d (1 : Fin 2) = d.degree := by
      rw [Finsupp.degree_eq_weight_one]
      rw [Finsupp.weight_apply, Finsupp.sum_fintype]
      · simp
      · intro i
        simp
    _ = n := hdeg

/-- A constant binary directional derivative lowers ordinary homogeneous
degree by one. -/
theorem binaryLinearFormTransverseDeriv_isHomogeneous
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hhom : G.IsHomogeneous E) :
    (binaryLinearFormTransverseDeriv c G).IsHomogeneous (E - 1) := by
  have h0 :
      (MvPolynomial.pderiv (0 : Fin 2) G).IsHomogeneous (E - 1) := by
    simpa using hhom.pderiv
  have h1 :
      (MvPolynomial.pderiv (1 : Fin 2) G).IsHomogeneous (E - 1) := by
    simpa using hhom.pderiv
  unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv
  exact (h0.C_mul (c 1)).add (h1.C_mul (-c 0))

/-- Hence the first transverse derivative of a homogeneous binary layer has
exact transverse degree `E-1`. -/
theorem binaryLinearFormTransverseDeriv_hasExactTransverseDegree
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hhom : G.IsHomogeneous E) :
    HasExactTransverseDegree (0 : Fin 2) 1 (E - 1)
      (binaryLinearFormTransverseDeriv c G) :=
  binaryHomogeneous_hasExactTransverseDegree
    (binaryLinearFormTransverseDeriv c G) (E - 1)
      (binaryLinearFormTransverseDeriv_isHomogeneous c G E hhom)

/-! ## The two negative-square identities -/

/-- The second coordinate derivative of the transverse first derivative. -/
theorem pderiv_one_binaryLinearFormTransverseDeriv
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv (1 : Fin 2)
        (binaryLinearFormTransverseDeriv c G) =
      MvPolynomial.C (c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G -
        MvPolynomial.C (c 0) *
          directionalSecondDerivative (1 : Fin 2) G := by
  unfold binaryLinearFormTransverseDeriv
  rw [pderiv_binaryDirectionalDeriv_second]
  unfold binaryDirectionalDeriv directionalMixedDerivative
    directionalSecondDerivative
  rw [MvPolynomial.C_neg]
  ring

/-- The first coordinate derivative of the transverse first derivative. -/
theorem pderiv_zero_binaryLinearFormTransverseDeriv
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv (0 : Fin 2)
        (binaryLinearFormTransverseDeriv c G) =
      MvPolynomial.C (c 1) *
          directionalSecondDerivative (0 : Fin 2) G -
        MvPolynomial.C (c 0) *
          directionalMixedDerivative (0 : Fin 2) 1 G := by
  unfold binaryLinearFormTransverseDeriv
  rw [pderiv_binaryDirectionalDeriv_first]
  unfold binaryDirectionalDeriv directionalMixedDerivative
    directionalSecondDerivative
  rw [MvPolynomial.C_neg]
  rw [pderiv_comm_backport (1 : Fin 2) 0 G]
  ring

/-- If the second transverse directional derivative vanishes, multiplying
the Hessian determinant by `c₁²` gives a negative square. -/
theorem binaryHessianDet_mul_c1_sq_eq_neg_sq
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0) :
    MvPolynomial.C (c 1 * c 1) *
        binaryDirectionalHessianDet (0 : Fin 2) 1 G =
      - (MvPolynomial.pderiv (1 : Fin 2)
          (binaryLinearFormTransverseDeriv c G)) ^ 2 := by
  have hquad := binaryLinearFormTransverseDeriv_sq_expand c G
  rw [hsq] at hquad
  have hquad' :
      MvPolynomial.C (c 1 * c 1) *
          directionalSecondDerivative (0 : Fin 2) G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G +
        MvPolynomial.C (c 0 * c 0) *
          directionalSecondDerivative (1 : Fin 2) G = 0 := by
    exact hquad.symm
  simp only [MvPolynomial.C_mul] at hquad'
  rw [pderiv_one_binaryLinearFormTransverseDeriv]
  unfold binaryDirectionalHessianDet
  simp only [MvPolynomial.C_mul]
  linear_combination
    (directionalSecondDerivative (1 : Fin 2) G) * hquad'

/-- Symmetric negative-square identity using the `c₀` pivot. -/
theorem binaryHessianDet_mul_c0_sq_eq_neg_sq
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0) :
    MvPolynomial.C (c 0 * c 0) *
        binaryDirectionalHessianDet (0 : Fin 2) 1 G =
      - (MvPolynomial.pderiv (0 : Fin 2)
          (binaryLinearFormTransverseDeriv c G)) ^ 2 := by
  have hquad := binaryLinearFormTransverseDeriv_sq_expand c G
  rw [hsq] at hquad
  have hquad' :
      MvPolynomial.C (c 1 * c 1) *
          directionalSecondDerivative (0 : Fin 2) G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G -
        MvPolynomial.C (c 0 * c 1) *
          directionalMixedDerivative (0 : Fin 2) 1 G +
        MvPolynomial.C (c 0 * c 0) *
          directionalSecondDerivative (1 : Fin 2) G = 0 := by
    exact hquad.symm
  simp only [MvPolynomial.C_mul] at hquad'
  rw [pderiv_zero_binaryLinearFormTransverseDeriv]
  unfold binaryDirectionalHessianDet
  simp only [MvPolynomial.C_mul]
  linear_combination
    (directionalSecondDerivative (0 : Fin 2) G) * hquad'

/-! ## A nonzero transverse tangent has a nonzero selected derivative -/

/-- If `c₁` is nonzero, a nonzero positive-degree transverse first derivative
cannot have zero `∂₁`: together with `D_perp P = 0` this would force both
partials of `P` to vanish. -/
theorem pderiv_one_transverseDeriv_ne_zero_of_positiveDegree
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hE : 2 ≤ E)
    (hhom : G.IsHomogeneous E)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
    (hPne : binaryLinearFormTransverseDeriv c G ≠ 0)
    (hc1 : c 1 ≠ 0) :
    MvPolynomial.pderiv (1 : Fin 2)
        (binaryLinearFormTransverseDeriv c G) ≠ 0 := by
  let P : MvPolynomial (Fin 2) K := binaryLinearFormTransverseDeriv c G
  have hPhom : P.IsHomogeneous (E - 1) := by
    dsimp [P]
    exact binaryLinearFormTransverseDeriv_isHomogeneous c G E hhom
  have hPexact :
      HasExactTransverseDegree (0 : Fin 2) 1 (E - 1) P :=
    binaryHomogeneous_hasExactTransverseDegree P (E - 1) hPhom
  have hPpos : 0 < E - 1 := by omega
  have hPne' : P ≠ 0 := by
    simpa [P] using hPne
  have hdir : binaryLinearFormTransverseDeriv c P = 0 := by
    simpa [P] using hsq
  intro h1
  have h1' : MvPolynomial.pderiv (1 : Fin 2) P = 0 := by
    simpa [P] using h1
  have hscaled :
      MvPolynomial.C (c 1) * MvPolynomial.pderiv (0 : Fin 2) P = 0 := by
    unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv at hdir
    rw [h1'] at hdir
    simpa using hdir
  have h0 : MvPolynomial.pderiv (0 : Fin 2) P = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left (MvPolynomial.C_ne_zero.mpr hc1)
  have hind : IsTransverselyIndependent (0 : Fin 2) 1 P :=
    isTransverselyIndependent_of_pderiv_eq_zero
      (0 : Fin 2) 1 P h0 h1'
  have hzero : P = 0 :=
    eq_zero_of_exactPositiveTransverseDegree_of_independent
      (0 : Fin 2) 1 (E - 1) P hPpos hPexact hind
  exact hPne' hzero

/-- Symmetric pivot lemma: if `c₀` is nonzero, a nonzero positive-degree
transverse first derivative has nonzero `∂₀`. -/
theorem pderiv_zero_transverseDeriv_ne_zero_of_positiveDegree
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hE : 2 ≤ E)
    (hhom : G.IsHomogeneous E)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
    (hPne : binaryLinearFormTransverseDeriv c G ≠ 0)
    (hc0 : c 0 ≠ 0) :
    MvPolynomial.pderiv (0 : Fin 2)
        (binaryLinearFormTransverseDeriv c G) ≠ 0 := by
  let P : MvPolynomial (Fin 2) K := binaryLinearFormTransverseDeriv c G
  have hPhom : P.IsHomogeneous (E - 1) := by
    dsimp [P]
    exact binaryLinearFormTransverseDeriv_isHomogeneous c G E hhom
  have hPexact :
      HasExactTransverseDegree (0 : Fin 2) 1 (E - 1) P :=
    binaryHomogeneous_hasExactTransverseDegree P (E - 1) hPhom
  have hPpos : 0 < E - 1 := by omega
  have hPne' : P ≠ 0 := by
    simpa [P] using hPne
  have hdir : binaryLinearFormTransverseDeriv c P = 0 := by
    simpa [P] using hsq
  intro h0
  have h0' : MvPolynomial.pderiv (0 : Fin 2) P = 0 := by
    simpa [P] using h0
  have hscaled :
      MvPolynomial.C (-c 0) * MvPolynomial.pderiv (1 : Fin 2) P = 0 := by
    unfold binaryLinearFormTransverseDeriv binaryDirectionalDeriv at hdir
    rw [h0'] at hdir
    simpa using hdir
  have hC0 : (MvPolynomial.C (-c 0) : MvPolynomial (Fin 2) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (neg_ne_zero.mpr hc0)
  have h1 : MvPolynomial.pderiv (1 : Fin 2) P = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hC0
  have hind : IsTransverselyIndependent (0 : Fin 2) 1 P :=
    isTransverselyIndependent_of_pderiv_eq_zero
      (0 : Fin 2) 1 P h0' h1
  have hzero : P = 0 :=
    eq_zero_of_exactPositiveTransverseDegree_of_independent
      (0 : Fin 2) 1 (E - 1) P hPpos hPexact hind
  exact hPne' hzero

/-! ## Curvature consequence -/

/-- **Nontrivial tangent implies nonzero next-layer Hessian determinant.**

For a homogeneous binary layer of degree at least two, a nonzero first
transverse derivative together with zero second transverse derivative forces
an honest nonzero Hessian determinant. -/
theorem binaryHessianDet_ne_zero_of_transverse_sq_zero_of_transverse_ne_zero
    (c : Fin 2 → K)
    (G : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hE : 2 ≤ E)
    (hhom : G.IsHomogeneous E)
    (hsq :
      binaryLinearFormTransverseDeriv c
        (binaryLinearFormTransverseDeriv c G) = 0)
    (hPne : binaryLinearFormTransverseDeriv c G ≠ 0) :
    binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0 := by
  by_cases hc1 : c 1 = 0
  · have hc0 : c 0 ≠ 0 := by
      intro hc0
      apply hPne
      simp [binaryLinearFormTransverseDeriv, binaryDirectionalDeriv, hc0, hc1]
    have hp0 :=
      pderiv_zero_transverseDeriv_ne_zero_of_positiveDegree
        c G E hE hhom hsq hPne hc0
    intro hdet
    have hid := binaryHessianDet_mul_c0_sq_eq_neg_sq c G hsq
    rw [hdet] at hid
    simp only [mul_zero] at hid
    have hsquare :
        (MvPolynomial.pderiv (0 : Fin 2)
          (binaryLinearFormTransverseDeriv c G)) ^ 2 = 0 := by
      exact neg_eq_zero.mp hid.symm
    have hmul :
        MvPolynomial.pderiv (0 : Fin 2)
            (binaryLinearFormTransverseDeriv c G) *
          MvPolynomial.pderiv (0 : Fin 2)
            (binaryLinearFormTransverseDeriv c G) = 0 := by
      simpa [pow_two] using hsquare
    exact hp0 (mul_self_eq_zero.mp hmul)
  · have hp1 :=
      pderiv_one_transverseDeriv_ne_zero_of_positiveDegree
        c G E hE hhom hsq hPne hc1
    intro hdet
    have hid := binaryHessianDet_mul_c1_sq_eq_neg_sq c G hsq
    rw [hdet] at hid
    simp only [mul_zero] at hid
    have hsquare :
        (MvPolynomial.pderiv (1 : Fin 2)
          (binaryLinearFormTransverseDeriv c G)) ^ 2 = 0 := by
      exact neg_eq_zero.mp hid.symm
    have hmul :
        MvPolynomial.pderiv (1 : Fin 2)
            (binaryLinearFormTransverseDeriv c G) *
          MvPolynomial.pderiv (1 : Fin 2)
            (binaryLinearFormTransverseDeriv c G) = 0 := by
      simpa [pow_two] using hsquare
    exact hp1 (mul_self_eq_zero.mp hmul)

/-! ## Frontier carried by the actual stationary binary core -/

/-- After the top-layer direction lock, the next active homogeneous layer is
one of:

* affine (`E <= 1`);
* nonlinear but already first-order locked to the top direction;
* nonlinear with a nonzero Hessian determinant, which therefore requires
  compensation from a strictly lower layer in the full determinant-zero
  polynomial.
-/
inductive BinarySingularHessianNextLayerCurvatureFrontier
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
  | nonlinearNextCurved
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
      (transverse_first_ne_zero : binaryLinearFormTransverseDeriv c G ≠ 0)
      (next_det_ne_zero :
        binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0)

/-- Every nonzero binary singular-Hessian polynomial reaches the next-layer
curvature frontier. -/
theorem binarySingularHessian_nextLayerCurvatureFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianNextLayerCurvatureFrontier Q) := by
  rcases binarySingularHessian_topLayerDirectionLockFrontier Q hQ hdet with ⟨F⟩
  cases F with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
      exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
        a c normalForm Q_eq_H⟩
  | nonlinearNextLayer D H hD H_eq H_ne_zero maximal a c normalForm
      R R_eq R_ne_zero E G E_lt_D G_eq G_ne_zero remainder_maximal
      G_homogeneous transverse_sq_zero =>
      by_cases hE : 2 ≤ E
      · by_cases hfirst : binaryLinearFormTransverseDeriv c G = 0
        · exact ⟨.nonlinearNextLocked D H hD H_eq H_ne_zero maximal
            a c normalForm R R_eq R_ne_zero E G E_lt_D hE G_eq G_ne_zero
            remainder_maximal G_homogeneous transverse_sq_zero hfirst⟩
        · have hGdet : binaryDirectionalHessianDet (0 : Fin 2) 1 G ≠ 0 :=
            binaryHessianDet_ne_zero_of_transverse_sq_zero_of_transverse_ne_zero
              c G E hE G_homogeneous transverse_sq_zero hfirst
          exact ⟨.nonlinearNextCurved D H hD H_eq H_ne_zero maximal
            a c normalForm R R_eq R_ne_zero E G E_lt_D hE G_eq G_ne_zero
            remainder_maximal G_homogeneous transverse_sq_zero hfirst hGdet⟩
      · have hEle : E ≤ 1 := by omega
        exact ⟨.nonlinearNextAffine D H hD H_eq H_ne_zero maximal
          a c normalForm R R_eq R_ne_zero E G E_lt_D hEle G_eq G_ne_zero
          remainder_maximal G_homogeneous transverse_sq_zero⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing curvature frontier for the actual stationary HC4 binary
face. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.nextLayerCurvatureFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianNextLayerCurvatureFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_nextLayerCurvatureFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
