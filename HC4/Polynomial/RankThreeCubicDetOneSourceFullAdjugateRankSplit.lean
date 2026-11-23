import HC4.Polynomial.RankThreeCubicDetOneSourceFullPoleCofactorSplit
import HC4.Polynomial.RankThreeCubicDetOneFullAdjugateKernelRankTwo
import HC4.Polynomial.RankThreeCubicSourceRankOneElimination
import Mathlib.Tactic

/-!
# Source-honest genuine cubic pole: rank-three isotropic repair,
# full rank-two adjugate zero, or the exact triple factor

We use the actual cubic source's surviving TRANSVERSE principal
cofactor at the genuine denominator prime. This pivot is proved by
sourceCubic_genuinePole_has_principalRankTwo, not assumed.

Together with the genuine fixed full-Hessian kernel, the principal
transverse pivot has a nonzero, hence unit, ground-field kernel
coordinate in the prime quotient. If all transverse principal
cofactors of the FULL cubic Hessian vanish, the source-neutral
rank-two matrix lemma gives vanishing of the entire full adjugate.

On the complementary rank-three branch, the weight-five source
constraint forces the actual quadratic transverse repair to be
isotropic. Exact triple poles remain a separate alternative.

Neither rank-two adjugate zero nor rank-three isotropy is claimed
by itself to contradict determinant one.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] :=
  FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- In the actual determinant-one cubic source, every genuine
reduced characteristic pole either has an isotropic nonzero
quadratic transverse repair in the full-rank-three branch,
has an identically zero FULL cubic Hessian adjugate modulo the
pole (rank two, since the transverse cofactor survives), or
has the exact nonzero scalar triple transverse determinant. -/
theorem sourceCubic_genuinePole_detOne_isotropicRepair_or_fullAdjugateZero_or_exactTriple
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (u : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u))) :
    let L3 := initialForm transverseCubicWeight 3 F
    let L2 := initialForm transverseCubicWeight 2 F
    let H := sourceTransverseHessian a L3
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) :=
      φ.mapMatrix (hessian L3)
    let T2 : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (referenceSlice a
        (hessian L2 (.inr i) (.inr j))).coeff 0
    (∃ (ell : Fin 3 → K)
        (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
      (∃ i : Fin 3, (∑ j : Fin 3, T2 i j * w0 j) ≠ 0) ∧
      ((∃ k : Fin 3,
          A.adjugate (.inr k) (.inr k) ≠ 0 ∧
          (∑ i : Fin 3, ∑ j : Fin 3,
            w0 i * T2 i j * w0 j) = 0) ∨
        A.adjugate = 0))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L3
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, _htrace, ⟨i, hi⟩⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_exactTriple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    let W : Fin 3 → R := fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    have hresponse :=
      sourceCubic_quadraticTransverseRepair_quotient_eq_C
        F a p w0 i
    have hnonzero :
        (∑ j : Fin 3, T2 i j * w0 j) ≠ 0 := by
      intro hz
      apply hi
      rw [hresponse, hz]
      simp
    refine Or.inl ⟨ell, M, r, t, hlin, hM, hrt,
      ⟨i, hnonzero⟩, ?_⟩
    by_cases hcof :
        ∃ k : Fin 3, A.adjugate (.inr k) (.inr k) ≠ 0
    · obtain ⟨k, hkk⟩ := hcof
      left
      refine ⟨k, hkk, ?_⟩
      exact
        sourceCubic_rankThreePoleKernel_quadraticTransverse_isotropic_of_cofactor
          F a p ell hlin hp hcap hdetOne w0 k
          hWne hAker hkk
    · right
      have hall : ∀ k : Fin 3,
          A.adjugate (.inr k) (.inr k) = 0 := by
        intro k
        by_contra hk
        exact hcof ⟨k, hk⟩
      obtain ⟨k, hnot⟩ :=
        sourceCubic_genuinePole_has_principalRankTwo
          F a V hV hgrad hregular u p hp hpd hpn
      have hqHkk : (H.map q).adjugate k k ≠ 0 := by
        rw [(q.map_adjugate H).symm]
        intro hz
        apply hnot
        exact Ideal.mem_span_singleton.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      have hHmap :
          A.submatrix Sum.inr Sum.inr = H.map q := by
        ext j l
        rfl
      have hHkk :
          (A.submatrix Sum.inr Sum.inr).adjugate k k ≠ 0 := by
        rw [hHmap]
        exact hqHkk
      have hHker :
          (A.submatrix Sum.inr Sum.inr) *ᵥ W = 0 := by
        funext j
        have hj := congrFun hAker (.inr j)
        simpa [A, v, W, Matrix.mulVec, dotProduct,
          Matrix.submatrix_apply, Fintype.sum_sum_type] using hj
      have hwk : W k ≠ 0 :=
        principalCofactor_kernel_coordinate_ne_zero
          (A.submatrix Sum.inr Sum.inr) W k hHkk hHker hWne
      have hw0k : w0 k ≠ 0 := by
        intro hz
        apply hwk
        change q (MvPolynomial.C (w0 k)) = 0
        simp [hz]
      have hunitK : IsUnit (w0 k) :=
        isUnit_iff_ne_zero.mpr hw0k
      have hunit : IsUnit (W k) := by
        change IsUnit (q (MvPolynomial.C (w0 k)))
        exact hunitK.map
          (q.comp (MvPolynomial.C : K →+* B3 K))
      have hSym : A.IsSymm := by
        apply Matrix.IsSymm.ext
        intro j l
        change φ (pderiv j (pderiv l L3)) =
          φ (pderiv l (pderiv j L3))
        rw [HC4.Newton.pderiv_comm_backport j l L3]
      exact symmetricFour_fullAdjugate_zero_of_transverseKernel_pivot
        A hSym W k hunit hAker hHkk (hall k)
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
