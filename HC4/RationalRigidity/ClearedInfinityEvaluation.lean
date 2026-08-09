import HC4.RationalRigidity.LogarithmicInfinityCertificate
import Mathlib
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Cleared polynomial evaluation at the infinity chart

For a reduced rational source `rho = N / D` whose numerator and denominator
have the same degree, polynomial evaluation in `rho` has a particularly simple
homogenised numerator.  For `m >= natDegree P` set

    H_m(P;N,D) = sum_j p_j N^j D^(m-j).

If `deg N = deg D = d` and `D` is monic, then the coefficient of `X^(m*d)`
in this cleared numerator is exactly `P.eval N.leadingCoeff`.  Since the
canonical denominator is monic, this is evaluation at the exceptional
infinity value `lc(N)/lc(D)`.

This file uses that coefficient identity to package the algebraic infinity
step in the autonomous rational ODE argument.  No pointwise cancellation of a
raw numerator/denominator pair is used.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Denominator-cleared homogeneous substitution for `P(N/D)`, using a common
homogenising degree `m`.  The intended use has `P.natDegree <= m`. -/
def clearedPolynomialSubstitution
    (m : ℕ) (P N D : Polynomial K) : Polynomial K :=
  P.sum fun j a => Polynomial.C a * N ^ j * D ^ (m - j)

/-- Every summand of the cleared substitution has degree at most `m*d` when
`N` and `D` both have degree `d`. -/
theorem clearedPolynomialSubstitution_natDegree_le
    {m d : ℕ} {P N D : Polynomial K}
    (hPdeg : P.natDegree ≤ m)
    (hNdeg : N.natDegree = d)
    (hDdeg : D.natDegree = d) :
    (clearedPolynomialSubstitution m P N D).natDegree ≤ m * d := by
  rw [clearedPolynomialSubstitution, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le P.support
  intro j hj
  have hjP : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hjm : j ≤ m := le_trans hjP hPdeg
  have hleft :
      (Polynomial.C (P.coeff j) * N ^ j).natDegree ≤ j * d := by
    calc
      (Polynomial.C (P.coeff j) * N ^ j).natDegree ≤
          (N ^ j).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = j * N.natDegree := by rw [Polynomial.natDegree_pow]
      _ = j * d := by rw [hNdeg]
  have hright : (D ^ (m - j)).natDegree ≤ (m - j) * d := by
    rw [Polynomial.natDegree_pow, hDdeg]
  calc
    (Polynomial.C (P.coeff j) * N ^ j * D ^ (m - j)).natDegree ≤
        (Polynomial.C (P.coeff j) * N ^ j).natDegree +
          (D ^ (m - j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ j * d + (m - j) * d := Nat.add_le_add hleft hright
    _ = m * d := by
      have hsum : j + (m - j) = m := Nat.add_sub_of_le hjm
      calc
        j * d + (m - j) * d = (j + (m - j)) * d := by ring
        _ = m * d := by rw [hsum]

/-- Top coefficient of the cleared homogeneous substitution.  For equal-degree
`N,D` and monic `D`, it is evaluation of `P` at `lc(N)`, i.e. at the infinity
value of `N/D`. -/
theorem coeff_clearedPolynomialSubstitution_top
    {m d : ℕ} {P N D : Polynomial K}
    (hPdeg : P.natDegree ≤ m)
    (hNdeg : N.natDegree = d)
    (hDdeg : D.natDegree = d)
    (hDmonic : D.Monic) :
    (clearedPolynomialSubstitution m P N D).coeff (m * d) =
      P.eval N.leadingCoeff := by
  classical
  rw [clearedPolynomialSubstitution, Polynomial.sum_def,
    Polynomial.finset_sum_coeff]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro j hj
  have hjP : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hjm : j ≤ m := le_trans hjP hPdeg
  have hidx : j * d + (m - j) * d = m * d := by
    have hsum : j + (m - j) = m := Nat.add_sub_of_le hjm
    calc
      j * d + (m - j) * d = (j + (m - j)) * d := by ring
      _ = m * d := by rw [hsum]
  have hleft :
      (Polynomial.C (P.coeff j) * N ^ j).natDegree ≤ j * d := by
    calc
      (Polynomial.C (P.coeff j) * N ^ j).natDegree ≤
          (N ^ j).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = j * N.natDegree := by rw [Polynomial.natDegree_pow]
      _ = j * d := by rw [hNdeg]
  have hright : (D ^ (m - j)).natDegree ≤ (m - j) * d := by
    rw [Polynomial.natDegree_pow, hDdeg]
  rw [← hidx]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hleft hright]
  rw [Polynomial.coeff_C_mul]
  have hNcoeff : (N ^ j).coeff (j * d) = N.leadingCoeff ^ j := by
    rw [← hNdeg]
    exact Polynomial.coeff_pow_mul_natDegree N j
  have hDcoeff :
      (D ^ (m - j)).coeff ((m - j) * d) = D.leadingCoeff ^ (m - j) := by
    rw [← hDdeg]
    exact Polynomial.coeff_pow_mul_natDegree D (m - j)
  rw [hNcoeff, hDcoeff, hDmonic.leadingCoeff, one_pow, mul_one]

/-- In the rational-function field, a cleared homogeneous substitution is
exactly the common-denominator presentation of polynomial evaluation. -/
theorem clearedPolynomialSubstitution_map_eq
    {m : ℕ} {P N D : Polynomial K}
    (hPdeg : P.natDegree ≤ m) (hD : D ≠ 0) :
    algebraMap (Polynomial K) (RatFunc K)
        (clearedPolynomialSubstitution m P N D) =
      (algebraMap (Polynomial K) (RatFunc K) D) ^ m *
        Polynomial.aeval
          (algebraMap (Polynomial K) (RatFunc K) N /
            algebraMap (Polynomial K) (RatFunc K) D) P := by
  classical
  rw [clearedPolynomialSubstitution, Polynomial.sum_def, map_sum]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjP : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hjm : j ≤ m := le_trans hjP hPdeg
  have hmapD : algebraMap (Polynomial K) (RatFunc K) D ≠ 0 :=
    RatFunc.algebraMap_ne_zero hD
  simp only [map_mul, map_pow, RatFunc.algebraMap_C]
  rw [div_pow]
  have hpow :
      (algebraMap (Polynomial K) (RatFunc K) D) ^ m =
        (algebraMap (Polynomial K) (RatFunc K) D) ^ j *
          (algebraMap (Polynomial K) (RatFunc K) D) ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjm]
  rw [hpow]
  field_simp [hmapD]
  simpa [RatFunc.algebraMap_eq_C, mul_comm]

/-- Polynomial form of a rational autonomous identity after clearing a common
homogenising denominator. -/
theorem clearedPolynomialSubstitution_identity_of_ratFunc
    {rho eta : RatFunc K}
    {A B N D H : Polynomial K} {m : ℕ}
    (hD : D ≠ 0)
    (hRho : rho =
      algebraMap (Polynomial K) (RatFunc K) N /
        algebraMap (Polynomial K) (RatFunc K) D)
    (hEta : eta =
      algebraMap (Polynomial K) (RatFunc K) H /
        (algebraMap (Polynomial K) (RatFunc K) D) ^ 2)
    (hAdeg : A.natDegree ≤ m) (hBdeg : B.natDegree ≤ m)
    (hCross : Polynomial.aeval rho A = eta * Polynomial.aeval rho B) :
    clearedPolynomialSubstitution m A N D * D ^ 2 =
      H * clearedPolynomialSubstitution m B N D := by
  let ι : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  have hDAraw := clearedPolynomialSubstitution_map_eq
    (K := K) (m := m) (P := A) (N := N) (D := D) hAdeg hD
  have hDBraw := clearedPolynomialSubstitution_map_eq
    (K := K) (m := m) (P := B) (N := N) (D := D) hBdeg hD
  have hDA :
      ι (clearedPolynomialSubstitution m A N D) =
        ι D ^ m * Polynomial.aeval rho A := by
    simpa [ι, hRho] using hDAraw
  have hDB :
      ι (clearedPolynomialSubstitution m B N D) =
        ι D ^ m * Polynomial.aeval rho B := by
    simpa [ι, hRho] using hDBraw
  have hmapD : ι D ≠ 0 := by
    exact RatFunc.algebraMap_ne_zero hD
  apply RatFunc.algebraMap_injective K
  change
    ι (clearedPolynomialSubstitution m A N D * D ^ 2) =
      ι (H * clearedPolynomialSubstitution m B N D)
  have hEtaCleared : eta * ι D ^ 2 = ι H := by
    rw [hEta]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hmapD)
  simp only [map_mul, map_pow]
  rw [hDA, hDB, hCross]
  calc
    (ι D ^ m * (eta * Polynomial.aeval rho B)) * ι D ^ 2 =
        ι D ^ m * (Polynomial.aeval rho B * (eta * ι D ^ 2)) := by ring
    _ = ι D ^ m * (Polynomial.aeval rho B * ι H) := by rw [hEtaCleared]
    _ = ι H * (ι D ^ m * Polynomial.aeval rho B) := by ring

/-- Algebraic infinity evaluation for an autonomous rational identity.

If `rho=N/D` has equal numerator/denominator degree and monic denominator,
while `eta=H/D^2` has `deg H < 2 deg D`, then every polynomial identity
`A(rho)=eta*B(rho)` forces `A` to vanish at the infinity value of `rho`.
-/
theorem eval_at_infinity_eq_zero_of_autonomous_ratFunc_identity
    {rho eta : RatFunc K}
    {A B N D H : Polynomial K}
    (hD : D ≠ 0)
    (hDmonic : D.Monic)
    (hDegEq : N.natDegree = D.natDegree)
    (hHdeg : H.natDegree < D.natDegree + D.natDegree)
    (hRho : rho =
      algebraMap (Polynomial K) (RatFunc K) N /
        algebraMap (Polynomial K) (RatFunc K) D)
    (hEta : eta =
      algebraMap (Polynomial K) (RatFunc K) H /
        (algebraMap (Polynomial K) (RatFunc K) D) ^ 2)
    (hCross : Polynomial.aeval rho A = eta * Polynomial.aeval rho B) :
    A.eval N.leadingCoeff = 0 := by
  let m := max A.natDegree B.natDegree
  let d := D.natDegree
  have hAdeg : A.natDegree ≤ m := le_max_left _ _
  have hBdeg : B.natDegree ≤ m := le_max_right _ _
  have hNdeg : N.natDegree = d := by simpa [d] using hDegEq
  have hDdeg : D.natDegree = d := rfl
  have hPoly := clearedPolynomialSubstitution_identity_of_ratFunc
    (K := K) hD hRho hEta hAdeg hBdeg hCross

  have hLeftCoeff := congrArg
    (fun p : Polynomial K => p.coeff ((m + 2) * d)) hPoly

  have hHAdeg := clearedPolynomialSubstitution_natDegree_le
    (K := K) hAdeg hNdeg hDdeg
  have hHBdeg := clearedPolynomialSubstitution_natDegree_le
    (K := K) hBdeg hNdeg hDdeg
  have hD2deg : (D ^ 2).natDegree = 2 * d := by
    rw [Polynomial.natDegree_pow, hDdeg]

  have hLeftTop :
      (clearedPolynomialSubstitution m A N D * D ^ 2).coeff
          ((m + 2) * d) = A.eval N.leadingCoeff := by
    have hidx : m * d + 2 * d = (m + 2) * d := by ring
    rw [← hidx]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hHAdeg
      (le_of_eq hD2deg)]
    rw [coeff_clearedPolynomialSubstitution_top
      (K := K) hAdeg hNdeg hDdeg hDmonic]
    have hDtop : (D ^ 2).coeff (2 * d) = 1 := by
      rw [← hDdeg, Polynomial.coeff_pow_mul_natDegree]
      rw [hDmonic.leadingCoeff, one_pow]
    rw [hDtop, mul_one]

  have hRightDeg :
      (H * clearedPolynomialSubstitution m B N D).natDegree <
        (m + 2) * d := by
    have hHlt : H.natDegree < 2 * d := by
      simpa [d, two_mul] using hHdeg
    calc
      (H * clearedPolynomialSubstitution m B N D).natDegree ≤
          H.natDegree +
            (clearedPolynomialSubstitution m B N D).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ H.natDegree + m * d := Nat.add_le_add_left hHBdeg _
      _ < 2 * d + m * d := Nat.add_lt_add_right hHlt _
      _ = (m + 2) * d := by ring
  have hRightZero :
      (H * clearedPolynomialSubstitution m B N D).coeff
          ((m + 2) * d) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hRightDeg
  change
    (clearedPolynomialSubstitution m A N D * D ^ 2).coeff ((m + 2) * d) =
      (H * clearedPolynomialSubstitution m B N D).coeff ((m + 2) * d)
    at hLeftCoeff
  rw [hLeftTop, hRightZero] at hLeftCoeff
  exact hLeftCoeff

/-! ### Compatibility backport for the pinned rational-function API

The Mathlib revision pinned by this project predates
`RatFunc.transcendental_of_ne_C`.  We only need the elementary field-theoretic
argument behind that theorem.  Everything below is expressed using APIs that
already exist in the pinned revision.
-/

open IntermediateField Polynomial Algebra

/-- The polynomial relation `num(f) - f * denom(f)` with coefficients in
`K⟮f⟯`. -/
private noncomputable def phase88RatFuncRelation (f : RatFunc K) :
    Polynomial (K⟮f⟯) :=
  f.num.map (algebraMap K K⟮f⟯) -
    Polynomial.C (IntermediateField.AdjoinSimple.gen K f) *
      f.denom.map (algebraMap K K⟮f⟯)

/-- Evaluation at the ambient rational-function variable commutes with first
mapping coefficients from `K` into `K⟮f⟯`. -/
private theorem phase88RatFunc_aeval_X_map (f : RatFunc K) (p : Polynomial K) :
    Polynomial.aeval (RatFunc.X : RatFunc K)
        (p.map (algebraMap K K⟮f⟯)) =
      algebraMap (Polynomial K) (RatFunc K) p := by
  have htower :
      (algebraMap K⟮f⟯ (RatFunc K)).comp (algebraMap K K⟮f⟯) =
        (RingHom.id (RatFunc K)).comp (algebraMap K (RatFunc K)) := by
    ext c
    simp
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := K) (S := RatFunc K) (T := K⟮f⟯) (U := RatFunc K)
    (φ := algebraMap K K⟮f⟯) (ψ := RingHom.id (RatFunc K))
    htower p (RatFunc.X : RatFunc K)
  have h' :
      Polynomial.aeval (RatFunc.X : RatFunc K)
          (p.map (algebraMap K K⟮f⟯)) =
        Polynomial.aeval (RatFunc.X : RatFunc K) p := by
    simpa using h.symm
  rw [h', RatFunc.aeval_X_left_eq_algebraMap]

private theorem phase88RatFuncRelation_aeval_X (f : RatFunc K) :
    Polynomial.aeval (RatFunc.X : RatFunc K) (phase88RatFuncRelation f) = 0 := by
  rw [phase88RatFuncRelation]
  simp only [map_sub, map_mul, Polynomial.aeval_C]
  rw [phase88RatFunc_aeval_X_map f f.num,
    phase88RatFunc_aeval_X_map f f.denom]
  rw [IntermediateField.AdjoinSimple.algebraMap_gen K f]
  nth_rw 2 [← RatFunc.num_div_denom f]
  rw [div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

/-- If the top denominator coefficient of the relation vanishes in the ambient
field, then the rational function was constant. -/
private theorem phase88RatFunc_eq_C_of_relation_coeff_eq_zero
    (f : RatFunc K)
    (hf :
      ((phase88RatFuncRelation f).coeff f.denom.natDegree : RatFunc K) = 0) :
    ∃ c : K, f = RatFunc.C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀,
    eq_div_iff ((_root_.map_ne_zero RatFunc.C).mpr
      (Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero)),
    eq_comm]
  simpa [phase88RatFuncRelation, sub_eq_zero] using hf

private theorem phase88RatFuncRelation_ne_zero
    (f : RatFunc K) (hf : ¬ ∃ c : K, f = RatFunc.C c) :
    phase88RatFuncRelation f ≠ 0 := by
  intro hzero
  apply hf
  exact phase88RatFunc_eq_C_of_relation_coeff_eq_zero f (by simp [hzero])

private theorem phase88RatFunc_isAlgebraic_adjoin_simple_X
    (f : RatFunc K) (hf : ¬ ∃ c : K, f = RatFunc.C c) :
    IsAlgebraic K⟮f⟯ (RatFunc.X : RatFunc K) :=
  ⟨phase88RatFuncRelation f,
    phase88RatFuncRelation_ne_zero f hf,
    phase88RatFuncRelation_aeval_X f⟩

private theorem phase88RatFunc_transcendental_of_ne_C
    (f : RatFunc K) (hf : ¬ ∃ c : K, f = RatFunc.C c) :
    Transcendental K f := by
  intro hAlg
  letI : Algebra.IsAlgebraic K K⟮f⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple hAlg.isIntegral
  have hXalg : IsAlgebraic K (RatFunc.X : RatFunc K) :=
    (phase88RatFunc_isAlgebraic_adjoin_simple_X f hf).restrictScalars K
  exact RatFunc.transcendental_X hXalg

/-- Positive canonical denominator degree is enough to manufacture the
transcendence hypothesis used by the rank-three reduced-target assembly. -/
theorem ratFunc_transcendental_of_denom_natDegree_pos
    (rho : RatFunc K) (hdeg : 0 < rho.denom.natDegree) :
    Transcendental K rho := by
  apply phase88RatFunc_transcendental_of_ne_C rho
  rintro ⟨c, rfl⟩
  simpa using hdeg

end

end HC4.RationalRigidity
