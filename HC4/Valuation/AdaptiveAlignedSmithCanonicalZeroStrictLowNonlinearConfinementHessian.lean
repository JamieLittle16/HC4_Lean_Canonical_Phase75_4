import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit
import HC4.Newton.MixedDegreeAxisCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Hessian structure of the nonlinear-confinement branch

If every source monomial of ordinary degree at least three lies on one
coordinate facet, then every Hessian entry in the omitted row/column is
constant.  This is a purely coefficientwise consequence of the support
condition: any nonconstant monomial of such a Hessian entry would lift to a
source monomial of degree at least three with positive omitted-coordinate
exponent, contradicting facet confinement.

This is the first direct algebraic reduction of the final
`nonlinearConfined` constructor.  No JC2 projection, auxiliary clock, or
repair claim is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero four-variable exponent has positive ordinary degree. -/
private theorem ordinaryDegree4_pos_of_ne_zero
    (m : Fin 4 →₀ ℕ)
    (hm : m ≠ 0) :
    0 < HC4.Polynomial.ordinaryDegree4 m := by
  have hdeg : Finsupp.degree m ≠ 0 := by
    intro hz
    exact hm ((Finsupp.degree_eq_zero_iff m).mp hz)
  rw [← finsuppDegree_eq_ordinaryDegree4 m]
  exact Nat.pos_of_ne_zero hdeg

/-- **Facet confinement makes the omitted Hessian row constant.**

Only degree-at-most-two source terms may involve the omitted coordinate.
After two derivatives, every omitted-row Hessian entry is therefore a scalar
polynomial. -/
theorem hessian_omitted_eq_C_of_nonlinearConfinement
    (F : MvPolynomial (Fin 4) K)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ F.support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))
    (i : Fin 4) :
    HC4.Polynomial.hessian F
        (HC4.Polynomial.facetOmittedCoordinate facet) i =
      MvPolynomial.C
        (MvPolynomial.coeff 0
          (HC4.Polynomial.hessian F
            (HC4.Polynomial.facetOmittedCoordinate facet) i)) := by
  classical
  let j := HC4.Polynomial.facetOmittedCoordinate facet
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m
    simp [j]
  · have hmdeg : 0 < HC4.Polynomial.ordinaryDegree4 m :=
      ordinaryDegree4_pos_of_ne_zero m hm
    let n : Fin 4 →₀ ℕ :=
      (m + Finsupp.single i 1) + Finsupp.single j 1
    have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 n := by
      dsimp [n, j]
      unfold HC4.Polynomial.ordinaryDegree4 at hmdeg ⊢
      cases facet <;> fin_cases i <;>
        simp [HC4.Polynomial.facetOmittedCoordinate,
          Finsupp.add_apply, Finsupp.single_apply] <;> omega
    have hjpos : 0 < n j := by
      dsimp [n]
      simp [Finsupp.single_apply]
    have hsource : MvPolynomial.coeff n F = 0 := by
      by_contra hne
      have hnmem : n ∈ F.support :=
        MvPolynomial.mem_support_iff.mpr hne
      have hfacet := hconfined n hnmem hdeg
      have hjzero : n j = 0 := by
        dsimp [j]
        exact
          (HC4.Polynomial.onFacet_toToricExponent_iff facet n).1 hfacet
      exact (Nat.ne_of_gt hjpos) hjzero
    change
      MvPolynomial.coeff m
          (MvPolynomial.pderiv i
            (MvPolynomial.pderiv j F)) =
        MvPolynomial.coeff m
          (MvPolynomial.C
            (MvPolynomial.coeff 0
              (HC4.Polynomial.hessian F j i)))
    rw [coeff_pderiv_backport, coeff_pderiv_backport]
    dsimp [n] at hsource
    have h0m : (0 : Fin 4 →₀ ℕ) ≠ m := by
      intro h
      exact hm h.symm
    simp [hsource, h0m]

/-- A constant Hessian coupling to the distinguished longitudinal coordinate
vanishes under the normalized axis collision `0 ↔ e₀`.

This is the one-variable fundamental-theorem-of-calculus calculation used in
the older direct-closing terminal, isolated here without any terminal-specific
geometry. -/
theorem hessian_longitudinal_constant_eq_zero_of_axisCollision
    (F : MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (c : K)
    (hconst :
      HC4.Polynomial.hessian F j (0 : Fin 4) =
        MvPolynomial.C c) :
    c = 0 := by
  let G : Polynomial K :=
    longitudinalAxisRestriction (MvPolynomial.pderiv j F)
  have hCaxis :
      longitudinalAxisRestriction (MvPolynomial.C c) =
        Polynomial.C c := by
    simp [longitudinalAxisRestriction, MvPolynomial.finSuccEquiv_apply]
  have hGderiv : G.derivative = Polynomial.C c := by
    dsimp [G]
    rw [← longitudinalAxisRestriction_pderiv_zero]
    rw [show
      MvPolynomial.pderiv (0 : Fin 4) (MvPolynomial.pderiv j F) =
          MvPolynomial.C c by
        simpa [HC4.Polynomial.hessian_apply] using hconst]
    exact hCaxis
  have hgrad :
      Polynomial.eval (0 : K) G =
        Polynomial.eval (1 : K) G := by
    have h := hcoll j
    unfold mvGradientComponentAt at h
    rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
      eval_finCons_zero_eq_longitudinalAxisRestriction] at h
    simpa [G] using h
  let R : Polynomial K := G - Polynomial.C c * Polynomial.X
  have hRderiv : R.derivative = 0 := by
    dsimp [R]
    rw [Polynomial.derivative_sub, hGderiv,
      Polynomial.derivative_C_mul_X]
    simp
  have hRconst := Polynomial.eq_C_of_derivative_eq_zero hRderiv
  have heval :
      Polynomial.eval (0 : K) R =
        Polynomial.eval (1 : K) R := by
    rw [hRconst]
    simp
  have hcRelation :
      Polynomial.eval (0 : K) G =
        Polynomial.eval (1 : K) G - c := by
    simpa [R] using heval
  have hsub :
      Polynomial.eval (1 : K) G - c =
        Polynomial.eval (1 : K) G :=
    hcRelation.symm.trans hgrad
  exact sub_eq_self.mp hsub


/-- If a symmetric four-block has a zero \`(0,1)\` coupling and all five
principal minors touching row \`0\` or row \`1\` vanish, then its full
determinant vanishes.

The proof is deliberately division-free.  The \`(0,1)\` principal relation
gives \`a*d = 0\`.  If \`a = 0\`, the \`(0,2)\` and \`(0,3)\` relations kill
\`p,q\`, so row \`0\` is zero.  If \`d = 0\`, the \`(1,2)\` and \`(1,3)\`
relations kill \`r,s\`, so row \`1\` is zero. -/
theorem GeneralFourBlock.determinantCore_eq_zero_of_b_eq_zero_of_fivePrincipal
    {R : Type*} [CommRing R] [IsDomain R]
    (H : GeneralFourBlock R)
    (hb : H.b = 0)
    (h01 : H.a * H.d - H.b * H.b = 0)
    (h02 : H.a * H.x - H.p * H.p = 0)
    (h03 : H.a * H.z - H.q * H.q = 0)
    (h12 : H.d * H.x - H.r * H.r = 0)
    (h13 : H.d * H.z - H.s * H.s = 0) :
    H.determinantCore = 0 := by
  have had : H.a * H.d = 0 := by
    simpa [hb] using (sub_eq_zero.mp h01)
  rcases mul_eq_zero.mp had with ha | hd
  · have hp2 : H.p * H.p = 0 := by
      simpa [ha] using (sub_eq_zero.mp h02).symm
    have hq2 : H.q * H.q = 0 := by
      simpa [ha] using (sub_eq_zero.mp h03).symm
    have hp : H.p = 0 := by
      rcases mul_eq_zero.mp hp2 with hp | hp <;> exact hp
    have hq : H.q = 0 := by
      rcases mul_eq_zero.mp hq2 with hq | hq <;> exact hq
    simp [GeneralFourBlock.determinantCore, ha, hb, hp, hq]
  · have hr2 : H.r * H.r = 0 := by
      simpa [hd] using (sub_eq_zero.mp h12).symm
    have hs2 : H.s * H.s = 0 := by
      simpa [hd] using (sub_eq_zero.mp h13).symm
    have hr : H.r = 0 := by
      rcases mul_eq_zero.mp hr2 with hr | hr <;> exact hr
    have hs : H.s = 0 := by
      rcases mul_eq_zero.mp hs2 with hs | hs <;> exact hs
    simp [GeneralFourBlock.determinantCore, hb, hd, hr, hs]

/-- A nondegenerate symmetric four-variable Hessian with one vanishing
off-diagonal entry has a nonzero principal \`2 x 2\` minor.

This is the finite matrix fact needed by nonlinear confinement: after moving
the vanishing coupling to the displayed \`(0,1)\` slot, simultaneous vanishing
of every principal minor contradicts the nonzero full determinant. -/
theorem exists_hessianPrincipalMinor_ne_zero_of_offDiagonal_zero
    (F : MvPolynomial (Fin 4) K)
    {i j : Fin 4}
    (hij : i ≠ j)
    (hzero : HC4.Polynomial.hessian F i j = 0)
    (hdet : HC4.Polynomial.hessianDeterminant F ≠ 0) :
    ∃ a b : Fin 4,
      a ≠ b ∧ HC4.Polynomial.hessianPrincipalMinor F a b ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone

  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) i
  let tau : Equiv.Perm (Fin 4) := Equiv.swap (sigma (1 : Fin 4)) j
  let rho : Equiv.Perm (Fin 4) := sigma.trans tau

  have hs0 : sigma (0 : Fin 4) = i := by
    simp [sigma]
  have hs1_ne_i : sigma (1 : Fin 4) ≠ i := by
    intro h
    have h' : sigma (1 : Fin 4) = sigma (0 : Fin 4) := by
      rw [hs0]
      exact h
    have : (1 : Fin 4) = 0 := sigma.injective h'
    norm_num at this
  have hrho0 : rho (0 : Fin 4) = i := by
    dsimp [rho]
    rw [hs0]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hs1_ne_i) hij
  have hrho1 : rho (1 : Fin 4) = j := by
    dsimp [rho]
    simp [tau]

  let M := HC4.Polynomial.hessian F
  let H : GeneralFourBlock (MvPolynomial (Fin 4) K) :=
    GeneralFourBlock.ofSymmetricMatrix (M.submatrix rho rho)

  have hsym : ∀ a b : Fin 4, M a b = M b a := by
    intro a b
    change
      MvPolynomial.pderiv b (MvPolynomial.pderiv a F) =
        MvPolynomial.pderiv a (MvPolynomial.pderiv b F)
    exact pderiv_comm_commRing b a F

  have hmatrix :
      H.matrix = M.submatrix rho rho := by
    apply GeneralFourBlock.matrix_ofSymmetricMatrix
    intro a b
    exact hsym (rho a) (rho b)

  have hb : H.b = 0 := by
    dsimp [H, GeneralFourBlock.ofSymmetricMatrix]
    rw [hrho0, hrho1]
    exact hzero

  have hminor (a b : Fin 4) (hab : a ≠ b) :
      HC4.Polynomial.hessianPrincipalMinor F (rho a) (rho b) = 0 := by
    exact hnone (rho a) (rho b) (fun h => hab (rho.injective h))

  have h01 : H.a * H.d - H.b * H.b = 0 := by
    have h := hminor (0 : Fin 4) 1 (by decide)
    change
      M (rho 0) (rho 0) * M (rho 1) (rho 1) -
        M (rho 0) (rho 1) * M (rho 1) (rho 0) = 0 at h
    rw [hsym (rho 1) (rho 0)] at h
    change
      M (rho 0) (rho 0) * M (rho 1) (rho 1) -
        M (rho 0) (rho 1) * M (rho 0) (rho 1) = 0
    exact h
  have h02 : H.a * H.x - H.p * H.p = 0 := by
    have h := hminor (0 : Fin 4) 2 (by decide)
    change
      M (rho 0) (rho 0) * M (rho 2) (rho 2) -
        M (rho 0) (rho 2) * M (rho 2) (rho 0) = 0 at h
    rw [hsym (rho 2) (rho 0)] at h
    change
      M (rho 0) (rho 0) * M (rho 2) (rho 2) -
        M (rho 0) (rho 2) * M (rho 0) (rho 2) = 0
    exact h
  have h03 : H.a * H.z - H.q * H.q = 0 := by
    have h := hminor (0 : Fin 4) 3 (by decide)
    change
      M (rho 0) (rho 0) * M (rho 3) (rho 3) -
        M (rho 0) (rho 3) * M (rho 3) (rho 0) = 0 at h
    rw [hsym (rho 3) (rho 0)] at h
    change
      M (rho 0) (rho 0) * M (rho 3) (rho 3) -
        M (rho 0) (rho 3) * M (rho 0) (rho 3) = 0
    exact h
  have h12 : H.d * H.x - H.r * H.r = 0 := by
    have h := hminor (1 : Fin 4) 2 (by decide)
    change
      M (rho 1) (rho 1) * M (rho 2) (rho 2) -
        M (rho 1) (rho 2) * M (rho 2) (rho 1) = 0 at h
    rw [hsym (rho 2) (rho 1)] at h
    change
      M (rho 1) (rho 1) * M (rho 2) (rho 2) -
        M (rho 1) (rho 2) * M (rho 1) (rho 2) = 0
    exact h
  have h13 : H.d * H.z - H.s * H.s = 0 := by
    have h := hminor (1 : Fin 4) 3 (by decide)
    change
      M (rho 1) (rho 1) * M (rho 3) (rho 3) -
        M (rho 1) (rho 3) * M (rho 3) (rho 1) = 0 at h
    rw [hsym (rho 3) (rho 1)] at h
    change
      M (rho 1) (rho 1) * M (rho 3) (rho 3) -
        M (rho 1) (rho 3) * M (rho 1) (rho 3) = 0
    exact h

  have hdetH :
      H.determinantCore = HC4.Polynomial.hessianDeterminant F := by
    calc
      H.determinantCore = H.matrix.det :=
        (GeneralFourBlock.matrix_det H).symm
      _ = (M.submatrix rho rho).det := by rw [hmatrix]
      _ = M.det := by rw [Matrix.det_submatrix_equiv_self]
      _ = HC4.Polynomial.hessianDeterminant F := by
        rfl

  have hdet0 :
      H.determinantCore = 0 :=
    HC4.Valuation.GeneralFourBlock.determinantCore_eq_zero_of_b_eq_zero_of_fivePrincipal
      H hb h01 h02 h03 h12 h13
  apply hdet
  rw [← hdetH]
  exact hdet0

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The final `nonlinearConfined` source therefore has a constant Hessian
row in the coordinate omitted by the confinement facet. -/
theorem nonlinearConfined_hessianRow_constant
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))
    (i : Fin 4) :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
        (HC4.Polynomial.facetOmittedCoordinate facet) i =
      MvPolynomial.C
        (MvPolynomial.coeff 0
          (HC4.Polynomial.hessian
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family)
            (HC4.Polynomial.facetOmittedCoordinate facet) i)) :=
  hessian_omitted_eq_C_of_nonlinearConfinement
    (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family)
    facet hconfined i


/-- **Nonlinear confinement kills the omitted/longitudinal Hessian coupling.**

The confinement hypothesis makes the omitted Hessian row constant.  The
retained strict-low blocker lives on the genuine normalized axis collision
\`0 ↔ e₀\`, so the constant entry coupling the omitted coordinate to the
distinguished longitudinal coordinate must vanish.  This is source-level
geometry on the represented special fibre; no repair transition is used. -/
theorem nonlinearConfined_hessianOmittedLongitudinal_eq_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
        (HC4.Polynomial.facetOmittedCoordinate facet) (0 : Fin 4) = 0 := by
  have hconst :=
    T.nonlinearConfined_hessianRow_constant facet hconfined (0 : Fin 4)
  rcases T.terminal.blocker.blocker.aligned.rawSpecialFiber_axisData with
    ⟨hcollRaw, _hzero, _hvalue⟩
  have hcoll :
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
      T.terminal.blocker.family_eq] using hcollRaw
  have hc :
      MvPolynomial.coeff 0
          (HC4.Polynomial.hessian
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family)
            (HC4.Polynomial.facetOmittedCoordinate facet) (0 : Fin 4)) = 0 := by
    exact hessian_longitudinal_constant_eq_zero_of_axisCollision
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family)
      (HC4.Polynomial.facetOmittedCoordinate facet)
      hcoll
      (MvPolynomial.coeff 0
        (HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family)
          (HC4.Polynomial.facetOmittedCoordinate facet) (0 : Fin 4)))
      hconst
  rw [hconst, hc]
  simp


/-- **The nonlinear-confinement residual already has an actual rank-two chart.**

Confinement makes the omitted Hessian row constant; the normalized axis
collision kills its coupling to coordinate \`0\`.  Since complete nonlinear
confinement cannot occur on \`.qs\`, the omitted coordinate is genuinely
different from coordinate \`0\`.  The represented state has raw defect zero,
so its special-fibre Hessian determinant is exactly one.  The finite symmetric
matrix lemma above therefore supplies a nonzero principal \`2 x 2\` Hessian
minor, which is packaged by the existing source-honest chart adapter. -/
theorem nonlinearConfined_actualRankTwoHessianChart
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  let F :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let j := HC4.Polynomial.facetOmittedCoordinate facet

  have hj0 : j ≠ (0 : Fin 4) := by
    have hne := T.nonlinearConfined_facet_ne_qs facet hconfined
    cases facet <;>
      simp [j, HC4.Polynomial.facetOmittedCoordinate] at hne ⊢

  have hjcoupling :
      HC4.Polynomial.hessian F j (0 : Fin 4) = 0 := by
    simpa [F, j] using
      T.nonlinearConfined_hessianOmittedLongitudinal_eq_zero facet hconfined

  have hdetOne :
      HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact
      T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
        T.presented_zero
  have hdetNe :
      HC4.Polynomial.hessianDeterminant F ≠ 0 := by
    rw [hdetOne]
    exact one_ne_zero

  rcases exists_hessianPrincipalMinor_ne_zero_of_offDiagonal_zero
      F hj0 hjcoupling hdetNe with
    ⟨a, b, hab, hminor⟩
  exact ⟨actualRankTwoHessianChart_of_specialFiber_minor hab hminor⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
