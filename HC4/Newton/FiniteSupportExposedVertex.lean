import HC4.Newton.ExposedBalancedBoundaryStratum
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A18.5.33: construct an exposed vertex from finite multivariate support

The first-nonfacet development previously proved what happens *if* a nonlinear
singleton is further exposed, but did not construct such a singleton.  For an
actual finite `MvPolynomial` support no polytope library is needed.

Successively maximize source coordinates `0,1,2,3`.  At each stage the exact
coordinate-max component is a maximal integer initial form, hence:

* it is nonzero because the maximum is attained;
* its support is contained in the preceding support;
* Hessian determinant zero passes to it;
* torus-balanced support passes to it.

After all four coordinates have been fixed, any two surviving exponents agree
coordinatewise and are therefore equal.  The final face is literally one
monomial.  If the original support is nonlinear, that exposed monomial is
nonlinear as well.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Integer weight selecting one source coordinate. -/
def coordinateMaxWeight (i : Fin 4) : Fin 4 → ℤ :=
  fun j => if j = i then 1 else 0

/-- The coordinate weight of an exponent is exactly that coordinate. -/
theorem weight_coordinateMaxWeight
    (i : Fin 4) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (coordinateMaxWeight i) d = (d i : ℤ) := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · fin_cases i <;>
      simp [coordinateMaxWeight, Fin.sum_univ_four]
  · intro j
    simp

/-- One attained coordinate maximum and its exact initial-form face. -/
structure CoordinateMaxInitialData
    (F : MvPolynomial (Fin 4) K)
    (i : Fin 4) where
  level : ℕ
  witness : Fin 4 →₀ ℕ
  witness_mem : witness ∈ F.support
  witness_coordinate : witness i = level
  maximal : ∀ d ∈ F.support, d i ≤ level
  face : MvPolynomial (Fin 4) K
  face_eq : face = initialForm (coordinateMaxWeight i) (level : ℤ) F
  face_ne_zero : face ≠ 0
  weight_bound : IsWeightLE (coordinateMaxWeight i) (level : ℤ) F
  support_subset : face.support ⊆ F.support
  coordinate_eq : ∀ d ∈ face.support, d i = level

/-- Every nonzero finite polynomial has an attained coordinate-maximal exact
initial face. -/
noncomputable def coordinateMaxInitialData
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (i : Fin 4) : CoordinateMaxInitialData F i := by
  classical
  have hsupp : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  have hex : ∃ d ∈ F.support, ∀ q ∈ F.support, q i ≤ d i :=
    Finset.exists_max_image F.support (fun d => d i) hsupp
  let d := Classical.choose hex
  have hdspec := Classical.choose_spec hex
  have hd : d ∈ F.support := hdspec.1
  have hmax : ∀ q ∈ F.support, q i ≤ d i := hdspec.2
  let m := d i
  let G := initialForm (coordinateMaxWeight i) (m : ℤ) F
  have hbound : IsWeightLE (coordinateMaxWeight i) (m : ℤ) F := by
    intro q hq
    rw [weight_coordinateMaxWeight]
    exact_mod_cast hmax q hq
  have hGne : G ≠ 0 := by
    intro hG
    have hcoeff0 : MvPolynomial.coeff d G = 0 := by rw [hG]; simp
    have hcoeff : MvPolynomial.coeff d G = MvPolynomial.coeff d F := by
      dsimp [G]
      rw [coeff_initialForm, weight_coordinateMaxWeight]
      simp [m]
    rw [hcoeff] at hcoeff0
    exact (MvPolynomial.mem_support_iff.mp hd) hcoeff0
  have hsubset : G.support ⊆ F.support := by
    dsimp [G]
    exact support_initialForm_subset (coordinateMaxWeight i) (m : ℤ) F
  have hcoord : ∀ q ∈ G.support, q i = m := by
    intro q hq
    have hhom := initialForm_isWeightedHomogeneous
      (coordinateMaxWeight i) (m : ℤ) F
    have hw := hhom hq
    rw [weight_coordinateMaxWeight] at hw
    exact_mod_cast hw
  exact {
    level := m
    witness := d
    witness_mem := hd
    witness_coordinate := rfl
    maximal := fun q hq => hmax q hq
    face := G
    face_eq := rfl
    face_ne_zero := hGne
    weight_bound := hbound
    support_subset := hsubset
    coordinate_eq := hcoord
  }

/-- Coordinate-maximal extraction preserves Hessian singularity. -/
theorem CoordinateMaxInitialData.hessian_zero
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CoordinateMaxInitialData F i)
    (hzero : hessianDeterminant F = 0) :
    hessianDeterminant D.face = 0 := by
  rw [D.face_eq]
  exact hessianDeterminant_initialForm_eq_zero_of_eq_zero
    (coordinateMaxWeight i) (D.level : ℤ) F D.weight_bound hzero

/-- Coordinate-maximal extraction preserves balanced support. -/
theorem CoordinateMaxInitialData.balanced
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    {a b : ℕ}
    (D : CoordinateMaxInitialData F i)
    (hBal : HasBalancedMvSupport a b F) :
    HasBalancedMvSupport a b D.face := by
  rw [D.face_eq]
  exact hBal.initialForm (coordinateMaxWeight i) (D.level : ℤ)

/-- **Constructive exposed nonlinear balanced vertex.**

Starting from any nonzero balanced Hessian-singular polynomial whose complete
support is nonlinear, four coordinate-max refinements produce a balanced
Hessian-singular carrier with a final maximal initial form equal to one
nonzero nonlinear monomial. -/
theorem exists_exposed_nonlinear_balanced_monomial
    {a b : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hBal : HasBalancedMvSupport a b F)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d) :
    ∃ (G : MvPolynomial (Fin 4) K)
      (w : Fin 4 → ℤ) (level : ℤ)
      (d : Fin 4 →₀ ℕ) (c : K),
      hessianDeterminant G = 0 ∧
      HasBalancedMvSupport a b G ∧
      IsWeightLE w level G ∧
      initialForm w level G = MvPolynomial.monomial d c ∧
      c ≠ 0 ∧
      3 ≤ ordinaryDegree4 d := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : hessianDeterminant D0.face = 0 := D0.hessian_zero hzero
  have h0Bal : HasBalancedMvSupport a b D0.face := D0.balanced hBal

  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : hessianDeterminant D1.face = 0 := D1.hessian_zero h0zero
  have h1Bal : HasBalancedMvSupport a b D1.face := D1.balanced h0Bal

  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : hessianDeterminant D2.face = 0 := D2.hessian_zero h1zero
  have h2Bal : HasBalancedMvSupport a b D2.face := D2.balanced h1Bal

  let D3 := coordinateMaxInitialData D2.face D2.face_ne_zero (3 : Fin 4)

  let d := D3.witness
  let c := MvPolynomial.coeff d D3.face

  have hd2 : d ∈ D2.face.support := D3.witness_mem
  have hd1 : d ∈ D1.face.support := D2.support_subset hd2
  have hd0 : d ∈ D0.face.support := D1.support_subset hd1
  have hdF : d ∈ F.support := D0.support_subset hd0

  have hc : c ≠ 0 := by
    dsimp [c]
    have hcoeff :
        MvPolynomial.coeff d D3.face = MvPolynomial.coeff d D2.face := by
      rw [D3.face_eq, coeff_initialForm, weight_coordinateMaxWeight]
      have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simp [hd3]
    rw [hcoeff]
    exact MvPolynomial.mem_support_iff.mp D3.witness_mem

  have hunique : ∀ q ∈ D3.face.support, q = d := by
    intro q hq
    have hq2 : q ∈ D2.face.support := D3.support_subset hq
    have hq1 : q ∈ D1.face.support := D2.support_subset hq2
    have hq0 : q ∈ D0.face.support := D1.support_subset hq1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using
        (D0.coordinate_eq q hq0).trans (D0.coordinate_eq d hd0).symm
    · simpa using
        (D1.coordinate_eq q hq1).trans (D1.coordinate_eq d hd1).symm
    · simpa using
        (D2.coordinate_eq q hq2).trans (D2.coordinate_eq d hd2).symm
    · have hd3 : d (3 : Fin 4) = D3.level := by
        simpa [d] using D3.witness_coordinate
      simpa using (D3.coordinate_eq q hq).trans hd3.symm

  have hmono : D3.face = MvPolynomial.monomial d c := by
    apply MvPolynomial.ext
    intro q
    by_cases hqd : q = d
    · subst q
      simp [c]
    · have hq0 : MvPolynomial.coeff q D3.face = 0 := by
        by_contra hne
        have hqs : q ∈ D3.face.support := MvPolynomial.mem_support_iff.mpr hne
        exact hqd (hunique q hqs)
      have hdq : d ≠ q := by
        intro hdq
        exact hqd hdq.symm
      rw [hq0]
      simp [hdq]

  refine ⟨D2.face, coordinateMaxWeight (3 : Fin 4), (D3.level : ℤ),
    d, c, h2zero, h2Bal, D3.weight_bound, ?_, hc, hnonlinear d hdF⟩
  rw [← D3.face_eq]
  exact hmono

end

end HC4.Newton
