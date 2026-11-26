import HC4.Polynomial.WeightedExtremalPartner
import HC4.Polynomial.RationalCharacteristicConstants

/-!
# Rank-one Hessian ratio rigidity

For a symmetric polynomial Hessian with vanishing two-by-two minors,
choose a nonzero diagonal pivot A = H_kk and write B = H_ki,
C = H_ii.  The rational ratio r = B/A satisfies

    partial_i r = r * partial_k r.

If r = p/q is reduced, clearing this transport identity forces
q to divide partial_k q, so partial_k q = 0 by total degree descent.

If A has a pure k-power monomial at its highest total degree, then
every divisor of A independent of k must be constant. With the
corresponding degree bound on B, the entire ratio is constant.

The pure-pivot hypothesis is explicit here; producing the chart
from an arbitrary rank-one Hessian is a separate step.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open nonZeroDivisors
open scoped Matrix BigOperators

noncomputable section

variable {σ K : Type*} [Field K] [CharZero K]

private abbrev R (σ K : Type*) [Field K] := MvPolynomial σ K
private abbrev E (σ K : Type*) [Field K] := FractionRing (R σ K)

private def rankOnePartial (i : σ) : Derivation K (E σ K) (E σ K) :=
  localizationDerivation (nonZeroDivisors (R σ K)) (pderiv i)

private theorem rankOnePartial_map (i : σ) (p : R σ K) :
    rankOnePartial i (algebraMap (R σ K) (E σ K) p) =
      algebraMap (R σ K) (E σ K) (pderiv i p) :=
  localizationDerivation_algebraMap (nonZeroDivisors (R σ K)) _ _

/-- The one-component transport equation is a direct consequence
of the two-by-two minor and the genuine third-derivative equations. -/
theorem rankOneHessian_ratio_transport
    (L : R σ K) (k i : σ) (hk : hessian L k k ≠ 0)
    (hminor : hessian L k k * hessian L i i = (hessian L k i)^2) :
    let f := algebraMap (R σ K) (E σ K)
    let r := f (hessian L k i) / f (hessian L k k)
    rankOnePartial i r = r * rankOnePartial k r := by
  classical
  let f : R σ K →+* E σ K := algebraMap (R σ K) (E σ K)
  let A := hessian L k k
  let B := hessian L k i
  let C := hessian L i i
  let a := f A
  let b := f B
  let c := f C
  let r := b / a
  let D := rankOnePartial (K := K) i
  let T := rankOnePartial (K := K) k
  change D r = r * T r
  have ha : a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (R σ K) (E σ K)).ne (show A ≠ 0 from hk)
  have hab : a*r = b := by dsimp [r]; rw [mul_comm, div_mul_cancel₀ _ ha]
  have hac : a*c = b^2 := by
    change f A * f C = (f B)^2
    rw [← map_mul, ← map_pow]
    exact congrArg f hminor
  have hr2 : a*(r*r) = c := by
    apply mul_left_cancel₀ ha
    calc
      a*(a*(r*r)) = (a*r)^2 := by ring
      _ = b^2 := by rw [hab]
      _ = a*c := hac.symm
  have hDA : D a = T b := by
    change rankOnePartial i (f A) = rankOnePartial k (f B)
    rw [rankOnePartial_map, rankOnePartial_map]
    congr 1
    change pderiv i (pderiv k (pderiv k L)) =
      pderiv k (pderiv i (pderiv k L))
    exact pderiv_comm_backport i k _
  have hDB : D b = T c := by
    change rankOnePartial i (f B) = rankOnePartial k (f C)
    rw [rankOnePartial_map, rankOnePartial_map]
    congr 1
    change pderiv i (pderiv i (pderiv k L)) =
      pderiv k (pderiv i (pderiv i L))
    rw [pderiv_comm_backport i k L, pderiv_comm_backport i k (pderiv i L)]
  have h1 := congrArg D hab
  have h2 := congrArg T hab
  have h3 := congrArg T hr2
  simp only [Derivation.leibniz, smul_eq_mul] at h1 h2 h3
  rw [hDA, hDB] at h1
  apply (mul_left_cancel₀ ha)
  linear_combination h1 + r*h2 - h3

private theorem rankOne_pderiv_zero_of_dvd (q : R σ K) (k : σ)
    (hq : q ≠ 0) (hd : q ∣ pderiv k q) : pderiv k q = 0 := by
  by_cases hdeg : q.totalDegree = 0
  · rw [totalDegree_eq_zero_iff_eq_C.mp hdeg, pderiv_C]
  · by_contra hn
    obtain ⟨u,hu⟩ := hd
    have hu0 : u ≠ 0 := by
      intro hz
      exact hn (by rw [hu,hz,mul_zero])
    have hlt := totalDegree_pderiv_lt_of_totalDegree_pos q k (Nat.pos_of_ne_zero hdeg)
    have he : (pderiv k q).totalDegree = q.totalDegree + u.totalDegree := by
      rw [hu]
      exact totalDegree_mul_of_isDomain hq hu0
    omega

/-- The transport equation rules out a genuine pole in the pivot
variable. No squarefreeness condition on the denominator is used. -/
theorem rankOne_ratio_denominator_pderiv_zero
    (r : E σ K) (k i : σ)
    (hr : rankOnePartial i r = r * rankOnePartial k r) :
    pderiv k (IsFractionRing.den (R σ K) r : R σ K) = 0 := by
  classical
  let f : R σ K →+* E σ K := algebraMap (R σ K) (E σ K)
  let p : R σ K := IsFractionRing.num (R σ K) r
  let q : R σ K := IsFractionRing.den (R σ K) r
  have hq : q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (R σ K) r)
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (R σ K) (E σ K)).ne hq
  have hrepr : f p / f q = r := IsFractionRing.mk'_num_den' (R σ K) r
  have hmul : r * f q = f p := by rw [← hrepr, div_mul_cancel₀ _ hqf]
  have hdiff (j : σ) : f (pderiv j p) =
      r * f (pderiv j q) + f q * rankOnePartial j r := by
    have he := congrArg (rankOnePartial (K := K) j) hmul
    change rankOnePartial j (r * f q) = rankOnePartial j (f p) at he
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      rankOnePartial_map, rankOnePartial_map] at he
    exact he.symm
  have hcross : q * (q * pderiv i p - p * pderiv i q) =
      p * (q * pderiv k p - p * pderiv k q) := by
    apply IsFractionRing.injective (R σ K) (E σ K)
    change f _ = f _
    simp only [map_mul, map_sub]
    rw [hdiff i, hdiff k, ← hmul, hr]
    ring
  have hdvd : q ∣ pderiv k q * p * p := by
    refine ⟨p * pderiv k p - (q * pderiv i p - p * pderiv i q), ?_⟩
    linear_combination hcross
  have hcop : IsRelPrime q p := (IsFractionRing.num_den_reduced (R σ K) r).symm
  exact rankOne_pderiv_zero_of_dvd q k hq
    (hcop.dvd_of_dvd_mul_right (hcop.dvd_of_dvd_mul_right hdvd))

/-- A factor independent of k of a polynomial with a pure
highest-degree k monomial must have degree zero. -/
theorem rankOne_purePivot_factor_constant
    (A q : R σ K) (k : σ) (n : ℕ)
    (hA : coeff (Finsupp.single k n) A ≠ 0)
    (hdeg : A.totalDegree ≤ n)
    (hq : pderiv k q = 0) (hd : q ∣ A) :
    q.totalDegree = 0 := by
  classical
  obtain ⟨s,hs⟩ := hd
  have hA0 : A ≠ 0 := by intro hz; exact hA (by simp [hz])
  have hq0 : q ≠ 0 := by intro hz; exact hA0 (by rw [hs,hz,zero_mul])
  have hs0 : s ≠ 0 := by intro hz; exact hA0 (by rw [hs,hz,mul_zero])
  have hsn : coeff (Finsupp.single k n) s ≠ 0 := by
    intro hn
    apply hA
    rw [hs, MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    by_cases he : coeff uv.1 q = 0
    · rw [he,zero_mul]
    · have hz := exponent_eq_zero_of_pderiv_eq_zero k q hq uv.1 he
      have hadd := Finset.mem_antidiagonal.mp huv
      have hu0 : uv.1 = 0 := by
        ext j
        by_cases hj : j = k
        · subst j
          exact hz
        · have hh := congrArg (fun a : σ →₀ ℕ => a j) hadd
          change (uv.1 + uv.2) j = (Finsupp.single k n) j at hh
          simp [Finsupp.add_apply, Finsupp.single_apply, hj] at hh
          omega
      have hv : uv.2 = Finsupp.single k n := by
        simpa only [hu0,zero_add] using hadd
      rw [hv,hn,mul_zero]
  have hsn' := le_totalDegree (MvPolynomial.mem_support_iff.mpr hsn)
  have hsdeg : n ≤ s.totalDegree := by simpa [Finsupp.sum_single_index] using hsn'
  have hcalc : A.totalDegree = q.totalDegree + s.totalDegree := by
    rw [hs]
    exact totalDegree_mul_of_isDomain hq0 hs0
  omega

/-- Under the pure highest-degree pivot condition the original
row ratio is a ground-field constant, not just pole-free in k. -/
theorem rankOneHessian_ratio_constant_of_purePivot
    (L : R σ K) (k i : σ) (n : ℕ)
    (hA : coeff (Finsupp.single k n) (hessian L k k) ≠ 0)
    (hdeg : (hessian L k k).totalDegree ≤ n)
    (hBdeg : (hessian L k i).totalDegree ≤ n)
    (hminor : hessian L k k * hessian L i i = (hessian L k i)^2) :
    ∃ c : K, hessian L k i = MvPolynomial.C c * hessian L k k := by
  classical
  let A := hessian L k k
  let B := hessian L k i
  have hA0 : A ≠ 0 := by intro hz; exact hA (by change coeff _ A = 0; rw [hz,coeff_zero])
  by_cases hB0 : B = 0
  · exact ⟨0, by change B = _; rw [hB0,map_zero,zero_mul]⟩
  let f : R σ K →+* E σ K := algebraMap (R σ K) (E σ K)
  let r := f B / f A
  let p : R σ K := IsFractionRing.num (R σ K) r
  let q : R σ K := IsFractionRing.den (R σ K) r
  have hq0 : q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (R σ K) r)
  have hAf : f A ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (R σ K) (E σ K)).ne hA0
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (R σ K) (E σ K)).ne hq0
  have hrepr : f p / f q = r := IsFractionRing.mk'_num_den' (R σ K) r
  have hcross : B*q = A*p := by
    apply IsFractionRing.injective (R σ K) (E σ K)
    change f (B*q) = f (A*p)
    simp only [map_mul]
    have he : f p / f q = f B / f A := hrepr
    have hh := (div_eq_div_iff hqf hAf).mp he
    calc
      f B * f q = f p * f A := hh.symm
      _ = f A * f p := mul_comm _ _
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hcross
    exact hB0 ((mul_eq_zero.mp hcross).resolve_right hq0)
  have hcop : IsRelPrime q p := (IsFractionRing.num_den_reduced (R σ K) r).symm
  have hdvd : q ∣ A := hcop.dvd_of_dvd_mul_right ⟨B,by rw [← hcross,mul_comm]⟩
  have hqder : pderiv k q = 0 := rankOne_ratio_denominator_pderiv_zero r k i
    (rankOneHessian_ratio_transport L k i hA0 hminor)
  have hqdeg := rankOne_purePivot_factor_constant A q k n hA hdeg hqder hdvd
  have hAn : n ≤ A.totalDegree := by
    have he := le_totalDegree (MvPolynomial.mem_support_iff.mpr hA)
    simpa [Finsupp.sum_single_index] using he
  have hdegrees := congrArg (fun z : R σ K => z.totalDegree) hcross
  change (B*q).totalDegree = (A*p).totalDegree at hdegrees
  rw [totalDegree_mul_of_isDomain hB0 hq0, totalDegree_mul_of_isDomain hA0 hp0] at hdegrees
  have hpdeg : p.totalDegree = 0 := by omega
  have hqC := totalDegree_eq_zero_iff_eq_C.mp hqdeg
  have hpC := totalDegree_eq_zero_iff_eq_C.mp hpdeg
  have hcq : coeff 0 q ≠ 0 := by
    intro hz
    exact hq0 (by rw [hqC,hz,map_zero])
  refine ⟨coeff 0 p / coeff 0 q, ?_⟩
  change B = _
  apply mul_right_cancel₀ (MvPolynomial.C_ne_zero.mpr hcq)
  calc
    B * MvPolynomial.C (coeff 0 q) = B * q := by rw [← hqC]
    _ = A * p := hcross
    _ = A * MvPolynomial.C (coeff 0 p) := by rw [← hpC]
    _ = A * MvPolynomial.C ((coeff 0 p / coeff 0 q) * coeff 0 q) := by
      rw [div_mul_cancel₀ _ hcq]
    _ = (MvPolynomial.C (coeff 0 p / coeff 0 q) * A) *
        MvPolynomial.C (coeff 0 q) := by rw [map_mul]; ring

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankOneHessian_ratio_transport
#print axioms HC4.Polynomial.rankOne_ratio_denominator_pderiv_zero
#print axioms HC4.Polynomial.rankOneHessian_ratio_constant_of_purePivot
