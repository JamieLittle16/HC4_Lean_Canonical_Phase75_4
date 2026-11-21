import HC4.Valuation.AdaptiveAlignedSmithVerticalFiber
import HC4.Newton.InteriorVertex
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# A18.5.14: a singular vertical line starts on the rank-three boundary

Let

    V = x₁^b x₂^c x₃^d φ(x₀),   b,c,d > 0.

If `V` has zero Hessian determinant and `φ ≠ 0`, then the least occupied
longitudinal exponent of `φ` must be zero.

Indeed, choose the least `n` with `φ_n ≠ 0`.  The weight

    (-1,0,0,0)

exposes the unique monomial `x₀^n x₁^b x₂^c x₃^d`.  Zero Hessian determinant
passes to this maximal initial form.  The generic interior-vertex theorem then
forces that nonlinear monomial to omit a coordinate.  Since `b,c,d` are all
positive, the omitted coordinate can only be `x₀`, hence `n=0`.

This removes the nonzero-constant-term hypothesis from the eventual Smith
adapter: it follows automatically once the exact vertical Smith fibre is known
to be singular and genuinely rank three transversely.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Weight exposing the least longitudinal exponent while ignoring all three
transverse exponents. -/
def rankThreeVerticalLowestWeight (i : Fin 4) : ℤ :=
  if i = 0 then -1 else 0

/-- The weight of any four-variable exponent is minus its longitudinal
coordinate. -/
theorem weight_rankThreeVerticalLowestWeight
    (q : Fin 4 →₀ ℕ) :
    Finsupp.weight rankThreeVerticalLowestWeight q =
      -((q (0 : Fin 4) : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp only [Fin.sum_univ_four]
    simp [rankThreeVerticalLowestWeight]
  · intro i
    simp

/-- Support of an honest vertical line remembers exactly the fixed transverse
exponent and one supported exponent of its coefficient polynomial. -/
theorem rankThreeVerticalPolynomial_support_data
    {b c d : ℕ} {phi : Polynomial K} {q : Fin 4 →₀ ℕ}
    (hq : q ∈ (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi).support) :
    q (1 : Fin 4) = b ∧
      q (2 : Fin 4) = c ∧
      q (3 : Fin 4) = d ∧
      phi.coeff (q (0 : Fin 4)) ≠ 0 := by
  have hcoeff :
      MvPolynomial.coeff q
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hq
  rw [coeff_rankThreeVerticalPolynomial] at hcoeff
  by_cases htrans :
      q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
  · rw [if_pos htrans] at hcoeff
    exact ⟨htrans.1, htrans.2.1, htrans.2.2, hcoeff⟩
  · rw [if_neg htrans] at hcoeff
    exact (hcoeff rfl).elim

/-- The least occupied longitudinal exponent gives a genuine maximal initial
form for the negative longitudinal weight. -/
theorem rankThreeVertical_initialForm_at_least_coefficient
    {b c d : ℕ} {phi : Polynomial K}
    (hphi : phi ≠ 0) :
    let hp : ∃ n : ℕ, phi.coeff n ≠ 0 := by
      rcases Polynomial.support_nonempty.mpr hphi with ⟨n, hn⟩
      exact ⟨n, Polynomial.mem_support_iff.mp hn⟩
    let n := Nat.find hp
    HC4.Polynomial.IsWeightLE
        rankThreeVerticalLowestWeight (-((n : ℕ) : ℤ))
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) ∧
      HC4.Polynomial.initialForm
          rankThreeVerticalLowestWeight (-((n : ℕ) : ℤ))
          (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) =
        MvPolynomial.monomial
          (HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n)
          (phi.coeff n) := by
  dsimp only
  let hp : ∃ n : ℕ, phi.coeff n ≠ 0 := by
    rcases Polynomial.support_nonempty.mpr hphi with ⟨n, hn⟩
    exact ⟨n, Polynomial.mem_support_iff.mp hn⟩
  let n := Nat.find hp
  have hncoeff : phi.coeff n ≠ 0 := Nat.find_spec hp
  have hminimal :
      ∀ m : ℕ, phi.coeff m ≠ 0 → n ≤ m := by
    intro m hm
    by_contra hnot
    have hlt : m < n := Nat.lt_of_not_ge hnot
    exact (Nat.find_min hp hlt) hm
  have hbound :
      HC4.Polynomial.IsWeightLE
        rankThreeVerticalLowestWeight (-((n : ℕ) : ℤ))
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) := by
    intro q hq
    have hdata := rankThreeVerticalPolynomial_support_data hq
    have hnle : n ≤ q (0 : Fin 4) := hminimal _ hdata.2.2.2
    have hnleZ : (n : ℤ) ≤ ((q (0 : Fin 4) : ℕ) : ℤ) := by
      exact_mod_cast hnle
    rw [weight_rankThreeVerticalLowestWeight]
    exact neg_le_neg hnleZ
  refine ⟨hbound, ?_⟩
  apply MvPolynomial.ext
  intro q
  rw [HC4.Polynomial.coeff_initialForm]
  rw [weight_rankThreeVerticalLowestWeight]
  rw [MvPolynomial.coeff_monomial]
  by_cases hqn : q (0 : Fin 4) = n
  · have hw : -((q (0 : Fin 4) : ℕ) : ℤ) = -((n : ℕ) : ℤ) := by
      rw [hqn]
    rw [if_pos hw]
    rw [coeff_rankThreeVerticalPolynomial]
    by_cases htrans :
        q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
    · rw [if_pos htrans]
      have hqexp :
          q = HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n := by
        ext i
        fin_cases i <;>
          simp [HC4.Polynomial.rankThreeVerticalExponentFinsupp,
            hqn, htrans.1, htrans.2.1, htrans.2.2]
      simp [hqexp]
    · rw [if_neg htrans]
      have hne :
          HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n ≠ q := by
        intro heq
        apply htrans
        have h1 := congrArg (fun z : Fin 4 →₀ ℕ => z (1 : Fin 4)) heq
        have h2 := congrArg (fun z : Fin 4 →₀ ℕ => z (2 : Fin 4)) heq
        have h3 := congrArg (fun z : Fin 4 →₀ ℕ => z (3 : Fin 4)) heq
        exact
          ⟨by simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h1,
           by simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h2,
           by simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h3⟩
      simp [hne]
  · have hw : -((q (0 : Fin 4) : ℕ) : ℤ) ≠ -((n : ℕ) : ℤ) := by
      intro heq
      have hcast : ((q (0 : Fin 4) : ℕ) : ℤ) = (n : ℤ) :=
        neg_inj.mp heq
      have hnat : q (0 : Fin 4) = n := by exact_mod_cast hcast
      exact hqn hnat
    rw [if_neg hw]
    have hne :
        HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n ≠ q := by
      intro heq
      have h0 := congrArg (fun z : Fin 4 →₀ ℕ => z (0 : Fin 4)) heq
      have hnat : n = q (0 : Fin 4) := by
        simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h0
      exact hqn hnat.symm
    simp [hne]

/-- **A singular genuine vertical rank-three line has nonzero constant
coefficient.** -/
theorem rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
    {b c d : ℕ} {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hphi : phi ≠ 0)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) = 0) :
    phi.coeff 0 ≠ 0 := by
  let hp : ∃ n : ℕ, phi.coeff n ≠ 0 := by
    rcases Polynomial.support_nonempty.mpr hphi with ⟨n, hn⟩
    exact ⟨n, Polynomial.mem_support_iff.mp hn⟩
  let n := Nat.find hp
  have hncoeff : phi.coeff n ≠ 0 := Nat.find_spec hp
  have hfront :=
    rankThreeVertical_initialForm_at_least_coefficient
      (K := K) (b := b) (c := c) (d := d) hphi
  dsimp only at hfront
  have hbound := hfront.1
  have hinit := hfront.2
  have hdeg :
      3 ≤ HC4.Polynomial.ordinaryDegree4
        (HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n) := by
    simp [HC4.Polynomial.ordinaryDegree4,
      HC4.Polynomial.rankThreeVerticalExponentFinsupp]
    omega
  have hboundary :
      HC4.Polynomial.MvExponentOnBoundary
        (HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d n) :=
    HC4.Newton.exposed_monomial_on_boundary_of_zero_hessian
      hbound hdet hinit hncoeff hdeg
  rw [HC4.Polynomial.mvExponentOnBoundary_iff_coordinate_zero] at hboundary
  simp [HC4.Polynomial.rankThreeVerticalExponentFinsupp] at hboundary
  have hnzero : n = 0 := by omega
  simpa [hnzero] using hncoeff

end

end HC4.Valuation
