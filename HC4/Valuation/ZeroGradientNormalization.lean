import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.KernelInflationHessianDefect
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# Zero-gradient normalization of a polynomial family

Subtracting the parameter-dependent linear Taylor part at the zero section
normalizes the entire family gradient there to zero.  This leaves the
Hessian, its pure determinant clock, exact collisions, and nonlinear source
support unchanged.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The source-gradient coefficient of a polynomial family at the zero
section. -/
def polynomialFamilyGradientAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i : Fin 4) : Polynomial K :=
  MvPolynomial.eval (fun _ => (0 : Polynomial K))
    (MvPolynomial.pderiv i P)

/-- The parameter-dependent linear Taylor part of `P` at the zero section. -/
def polynomialFamilyLinearPartAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  ∑ i : Fin 4,
    MvPolynomial.monomial (Finsupp.single i 1)
      (polynomialFamilyGradientAtZero P i)

/-- Subtract the parameter-dependent linear Taylor part at zero. -/
def zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  P - polynomialFamilyLinearPartAtZero P

/-- Differentiating the linear correction recovers its corresponding
gradient coefficient. -/
theorem pderiv_polynomialFamilyLinearPartAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : Fin 4) :
    MvPolynomial.pderiv j (polynomialFamilyLinearPartAtZero P) =
      MvPolynomial.C (polynomialFamilyGradientAtZero P j) := by
  classical
  unfold polynomialFamilyLinearPartAtZero
  rw [map_sum, Finset.sum_eq_single j]
  · simp [MvPolynomial.pderiv_monomial]
  · intro i _hi hij
    simp [MvPolynomial.pderiv_monomial, hij]
  · simp

/-- The normalized family has zero gradient at the zero section. -/
theorem zeroGradientNormalizedFamily_gradientAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : Fin 4) :
    MvPolynomial.eval (fun _ => (0 : Polynomial K))
        (MvPolynomial.pderiv j (zeroGradientNormalizedFamily P)) = 0 := by
  rw [show MvPolynomial.pderiv j (zeroGradientNormalizedFamily P) =
      MvPolynomial.pderiv j P -
        MvPolynomial.C (polynomialFamilyGradientAtZero P j) by
    simp [zeroGradientNormalizedFamily,
      pderiv_polynomialFamilyLinearPartAtZero]]
  simp [polynomialFamilyGradientAtZero]

/-- Subtracting a common linear form preserves an exact gradient collision. -/
theorem polynomialFamilyExactGradientCollision_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (zeroGradientNormalizedFamily P) a b := by
  intro i
  simp only [zeroGradientNormalizedFamily, map_sub,
    pderiv_polynomialFamilyLinearPartAtZero,
    MvPolynomial.eval_C]
  rw [hcoll i]

/-- Every second source derivative is unchanged by zero-gradient
normalization. -/
theorem pderiv_pderiv_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i (zeroGradientNormalizedFamily P)) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  rw [show MvPolynomial.pderiv i (zeroGradientNormalizedFamily P) =
      MvPolynomial.pderiv i P -
        MvPolynomial.C (polynomialFamilyGradientAtZero P i) by
    simp [zeroGradientNormalizedFamily,
      pderiv_polynomialFamilyLinearPartAtZero]]
  simp

/-- The formal Hessian matrix is unchanged. -/
theorem hessian_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian (zeroGradientNormalizedFamily P) =
      HC4.Polynomial.hessian P := by
  apply Matrix.ext
  intro i j
  exact pderiv_pderiv_zeroGradientNormalizedFamily P i j

/-- Consequently the Hessian determinant is unchanged. -/
theorem hessianDeterminant_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant (zeroGradientNormalizedFamily P) =
      HC4.Polynomial.hessianDeterminant P := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_zeroGradientNormalizedFamily]

/-- Every pure Hessian-defect clock survives normalization. -/
theorem polynomialFamilyHessianDefect_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K) (zeroGradientNormalizedFamily P) Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_zeroGradientNormalizedFamily]
  exact hdef

/-- The correction has source degree one, so normalization preserves every
nonlinear source-degree ceiling. -/
theorem nonlinearDegreeBound_zeroGradientNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (zeroGradientNormalizedFamily P) := by
  intro d hd hnonlinear
  have hdunion :
      d ∈ P.support ∪ (polynomialFamilyLinearPartAtZero P).support :=
    MvPolynomial.support_sub (Fin 4) P
      (polynomialFamilyLinearPartAtZero P) hd
  rcases Finset.mem_union.mp hdunion with hdP | hdlinear
  · exact hP d hdP hnonlinear
  · classical
    have hdlinear' :
        d ∈ (Finset.univ : Finset (Fin 4)).biUnion
          (fun i =>
            (MvPolynomial.monomial (Finsupp.single i 1)
              (polynomialFamilyGradientAtZero P i)).support) := by
      exact MvPolynomial.support_sum hdlinear
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hdlinear'
    rcases hdlinear' with ⟨i, hi⟩
    have hdEq : d = Finsupp.single i 1 := by
      have hi' :
          Finsupp.single i 1 = d ∧
            polynomialFamilyGradientAtZero P i ≠ 0 := by
        simpa [MvPolynomial.mem_support_iff] using hi
      exact hi'.1.symm
    subst d
    fin_cases i <;>
      simp [HC4.Polynomial.ordinaryDegree4] at hnonlinear

/-! ## Full zero-jet normalization -/

/-- The parameter-dependent value of a family at the zero source section. -/
def polynomialFamilyValueAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Polynomial K :=
  MvPolynomial.eval (fun _ => (0 : Polynomial K)) P

/-- Remove both the value and the linear Taylor part at the zero section. -/
def zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  zeroGradientNormalizedFamily P -
    MvPolynomial.C (polynomialFamilyValueAtZero P)

/-- Zero-jet normalization makes the family value vanish at the zero
section. -/
theorem zeroJetNormalizedFamily_valueAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.eval (fun _ => (0 : Polynomial K))
      (zeroJetNormalizedFamily P) = 0 := by
  classical
  have hlinear :
      MvPolynomial.eval (fun _ => (0 : Polynomial K))
        (polynomialFamilyLinearPartAtZero P) = 0 := by
    rw [MvPolynomial.eval_zero']
    unfold polynomialFamilyLinearPartAtZero
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [MvPolynomial.constantCoeff_monomial]
    have hne : Finsupp.single i 1 ≠ (0 : Fin 4 →₀ ℕ) := by
      intro hsingle
      have hi := congrArg (fun d : Fin 4 →₀ ℕ => d i) hsingle
      simp at hi
    simp [hne]
  unfold zeroJetNormalizedFamily
  rw [map_sub, MvPolynomial.eval_C]
  unfold zeroGradientNormalizedFamily
  rw [map_sub, hlinear]
  simp [polynomialFamilyValueAtZero]

/-- Its source gradient also vanishes there. -/
theorem zeroJetNormalizedFamily_gradientAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : Fin 4) :
    MvPolynomial.eval (fun _ => (0 : Polynomial K))
        (MvPolynomial.pderiv j (zeroJetNormalizedFamily P)) = 0 := by
  simpa [zeroJetNormalizedFamily] using
    zeroGradientNormalizedFamily_gradientAtZero P j

/-- Removing the zero-jet preserves every exact gradient collision. -/
theorem polynomialFamilyExactGradientCollision_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (zeroJetNormalizedFamily P) a b := by
  have hgrad :=
    polynomialFamilyExactGradientCollision_zeroGradientNormalizedFamily
      P a b hcoll
  intro i
  simpa [zeroJetNormalizedFamily] using hgrad i

/-- The full zero-jet correction leaves all second derivatives unchanged. -/
theorem pderiv_pderiv_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i (zeroJetNormalizedFamily P)) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  simpa [zeroJetNormalizedFamily] using
    pderiv_pderiv_zeroGradientNormalizedFamily P i j

theorem hessian_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian (zeroJetNormalizedFamily P) =
      HC4.Polynomial.hessian P := by
  apply Matrix.ext
  intro i j
  exact pderiv_pderiv_zeroJetNormalizedFamily P i j

theorem hessianDeterminant_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant (zeroJetNormalizedFamily P) =
      HC4.Polynomial.hessianDeterminant P := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_zeroJetNormalizedFamily]

theorem polynomialFamilyHessianDefect_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K) (zeroJetNormalizedFamily P) Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_zeroJetNormalizedFamily]
  exact hdef

/-- Constant and linear corrections cannot create nonlinear source
support. -/
theorem nonlinearDegreeBound_zeroJetNormalizedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (zeroJetNormalizedFamily P) := by
  intro d hd hnonlinear
  have hdunion :
      d ∈ (zeroGradientNormalizedFamily P).support ∪
        (MvPolynomial.C (polynomialFamilyValueAtZero P)).support :=
    MvPolynomial.support_sub (Fin 4) _ _ hd
  rcases Finset.mem_union.mp hdunion with hdgrad | hdconst
  · exact nonlinearDegreeBound_zeroGradientNormalizedFamily P m hP
      d hdgrad hnonlinear
  · have hdEq : d = 0 := by
      have h := hdconst
      simp [MvPolynomial.mem_support_iff] at h
      exact h.1.symm
    subst d
    simp [HC4.Polynomial.ordinaryDegree4] at hnonlinear

/-- Source evaluation commutes with taking the parameter special fibre. -/
theorem polynomialFamilySpecialFiber_valueAt
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval (polynomialSectionSpecialPoint a)
        (polynomialFamilySpecialFiber P) =
      Polynomial.constantCoeff (MvPolynomial.eval a P) := by
  unfold polynomialFamilySpecialFiber polynomialSectionSpecialPoint
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp Polynomial.constantCoeff a P).symm

/-- The special fibre of the zero-jet-normalized family has zero value at
the distinguished zero section. -/
theorem zeroJetNormalizedSpecialFiber_valueAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.eval (fun _ => (0 : K))
      (polynomialFamilySpecialFiber (zeroJetNormalizedFamily P)) = 0 := by
  have h := polynomialFamilySpecialFiber_valueAt
    (zeroJetNormalizedFamily P) (fun _ => (0 : Polynomial K))
  have hsection :
      polynomialSectionSpecialPoint
          (fun _ : Fin 4 => (0 : Polynomial K)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext i
    simp [polynomialSectionSpecialPoint]
  rw [hsection] at h
  rw [h, zeroJetNormalizedFamily_valueAtZero]
  simp

/-- If a moving translation section specializes to the distinguished right
endpoint `e₀`, its special fibre is exactly the longitudinal-only
recentring `old x = new x + 1`.  In particular no transverse exponent is
mixed at this boundary. -/
theorem polynomialFamilySpecialFiber_translation_eq_longitudinalRightRecenter
    (a : Fin 4 → Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber
        (polynomialFamilyTranslationHom (K := K) a P) =
      longitudinalRightRecenterHom (K := K)
        (polynomialFamilySpecialFiber P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [polynomialFamilySpecialFiber, longitudinalRightRecenterHom]
  · intro p q hp hq
    simpa [polynomialFamilySpecialFiber] using congrArg₂ (fun x y => x + y) hp hq
  · intro p n hp
    have hvariable :
        polynomialFamilySpecialFiber
            (polynomialFamilyTranslationVariable (K := K) a n) =
          longitudinalRightRecenterHom (K := K)
            (MvPolynomial.X n) := by
      refine Fin.cases ?_ (fun j => ?_) n
      · have h0 := congrFun ha (0 : Fin 4)
        simp [polynomialSectionSpecialPoint, coordinateAxisPoint] at h0
        simp [polynomialFamilySpecialFiber,
          polynomialFamilyTranslationVariable,
          longitudinalRightRecenterHom, h0]
      · have hj := congrFun ha j.succ
        simp [polynomialSectionSpecialPoint, coordinateAxisPoint] at hj
        simp [polynomialFamilySpecialFiber,
          polynomialFamilyTranslationVariable,
          longitudinalRightRecenterHom, hj]
    have hmul := congrArg₂ (fun x y => x * y) hp hvariable
    simpa [polynomialFamilySpecialFiber, map_mul,
      polynomialFamilyTranslationHom_X] using hmul

/-! ## Normalized special-fibre blocker divisibility -/

/-- At the canonical boundary, full zero-jet normalization supplies the
axis collision, zero gradient, and zero value simultaneously.  Smith
certificates should be constructed only after entering this boundary. -/
theorem zeroJetNormalizedSpecialFiber_axisData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P
        (fun _ => (0 : Polynomial K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let F := polynomialFamilySpecialFiber (zeroJetNormalizedFamily P)
    HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) ∧
      (∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0) ∧
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0 := by
  dsimp only
  let Q := zeroJetNormalizedFamily P
  let F := polynomialFamilySpecialFiber Q
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision Q
        (fun _ => (0 : Polynomial K)) b :=
    polynomialFamilyExactGradientCollision_zeroJetNormalizedFamily
      P (fun _ => (0 : Polynomial K)) b hcoll
  have hspecial :=
    polynomialFamilyExactGradientCollision_specialFiber
      Q (fun _ => (0 : Polynomial K)) b hQcoll
  have hleft :
      polynomialSectionSpecialPoint (fun _ : Fin 4 => (0 : Polynomial K)) =
        Fin.cons (0 : K) (fun _ : Fin 3 => 0) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [polynomialSectionSpecialPoint]
  have hright :
      polynomialSectionSpecialPoint b =
        Fin.cons (1 : K) (fun _ : Fin 3 => 0) := by
    rw [hb]
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [coordinateAxisPoint]
  have haxisCollision :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [F, hleft, hright] using hspecial
  have hfamilyZero :
      ∀ i : Fin 4,
        MvPolynomial.eval (fun _ => (0 : Polynomial K))
          (MvPolynomial.pderiv i Q) = 0 :=
    zeroJetNormalizedFamily_gradientAtZero P
  have hspecialZero :=
    polynomialFamilyGradientZero_specialFiber Q
      (fun _ => (0 : Polynomial K)) hfamilyZero
  refine ⟨haxisCollision, ?_, ?_⟩
  · intro i
    have hi := hspecialZero i
    simpa [mvGradientComponentAt, F, hleft] using hi
  · have hvalue := zeroJetNormalizedSpecialFiber_valueAtZero P
    have haxisZero :
        Fin.cons (0 : K) (fun _ : Fin 3 => 0) =
          (fun _ : Fin 4 => (0 : K)) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp
    rw [haxisZero]
    exact hvalue

/-- Collision and zero-gradient data on the special fibre of the normalized
family, expressed in the `Fin.cons` coordinates used by the longitudinal
coefficient API. -/
theorem zeroGradientNormalizedSpecialFiber_axisData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P
        (fun _ => (0 : Polynomial K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let F := polynomialFamilySpecialFiber (zeroGradientNormalizedFamily P)
    HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) ∧
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0 := by
  dsimp only
  let Q := zeroGradientNormalizedFamily P
  let F := polynomialFamilySpecialFiber Q
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision Q
        (fun _ => (0 : Polynomial K)) b :=
    polynomialFamilyExactGradientCollision_zeroGradientNormalizedFamily
      P (fun _ => (0 : Polynomial K)) b hcoll
  have hspecial :=
    polynomialFamilyExactGradientCollision_specialFiber
      Q (fun _ => (0 : Polynomial K)) b hQcoll
  have hleft :
      polynomialSectionSpecialPoint (fun _ => (0 : Polynomial K)) =
        Fin.cons (0 : K) (fun _ : Fin 3 => 0) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [polynomialSectionSpecialPoint]
  have hright :
      polynomialSectionSpecialPoint b =
        Fin.cons (1 : K) (fun _ : Fin 3 => 0) := by
    rw [hb]
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [coordinateAxisPoint]
  have haxisCollision :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [F, hleft, hright] using hspecial
  have hfamilyZero :
      ∀ i : Fin 4,
        MvPolynomial.eval (fun _ => (0 : Polynomial K))
          (MvPolynomial.pderiv i Q) = 0 :=
    zeroGradientNormalizedFamily_gradientAtZero P
  have hspecialZero :=
    polynomialFamilyGradientZero_specialFiber Q
      (fun _ => (0 : Polynomial K)) hfamilyZero
  refine ⟨haxisCollision, ?_⟩
  intro i
  have hi := hspecialZero i
  simpa [mvGradientComponentAt, F, hleft] using hi

/-- On the special fibre of a zero-gradient-normalized pointed family, each
of the three transverse-linear longitudinal coefficient polynomials has the
clean endpoint factor `X - 1`. -/
theorem specialFiber_X_sub_one_dvd_transverseLinearCoefficient
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P
        (fun _ => (0 : Polynomial K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (j : Fin 3) :
    Polynomial.X - Polynomial.C 1 ∣
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1)
        (polynomialFamilySpecialFiber
          (zeroGradientNormalizedFamily P)) := by
  let F := polynomialFamilySpecialFiber (zeroGradientNormalizedFamily P)
  rcases zeroGradientNormalizedSpecialFiber_axisData P b hcoll hb with
    ⟨haxisCollision, hzero⟩
  exact
    X_sub_one_dvd_longitudinalCoefficient_single_of_collision
      j F haxisCollision (hzero j.succ)

/-- The pure-longitudinal blocker information on the normalized special
fibre: `L'` has roots at both distinguished endpoints. -/
theorem specialFiber_pureLongitudinal_derivative_endpointFactors
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision P
        (fun _ => (0 : Polynomial K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let F := polynomialFamilySpecialFiber (zeroGradientNormalizedFamily P)
    Polynomial.X ∣ (longitudinalAxisRestriction F).derivative ∧
      Polynomial.X - Polynomial.C 1 ∣
        (longitudinalAxisRestriction F).derivative := by
  dsimp only
  let F := polynomialFamilySpecialFiber (zeroGradientNormalizedFamily P)
  rcases zeroGradientNormalizedSpecialFiber_axisData P b hcoll hb with
    ⟨haxisCollision, hzero⟩
  exact
    ⟨X_dvd_axisRestriction_derivative F (hzero 0),
      X_sub_one_dvd_axisRestriction_derivative
        F haxisCollision (hzero 0)⟩

end

end HC4.Valuation
