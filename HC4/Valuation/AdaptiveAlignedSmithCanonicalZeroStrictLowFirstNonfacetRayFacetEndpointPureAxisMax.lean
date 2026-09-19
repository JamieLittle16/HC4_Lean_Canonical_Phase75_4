import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCore
import HC4.Newton.FiniteSupportExposedVertex
import Mathlib.Tactic

/-!
# Pure-axis lower-ray endpoint: maximal omitted-coordinate reduction

The lower `.qs` ray is affine and its omitted coordinate is coordinate `0`.
Consequently two supported exponents with the same coordinate-`0` exponent
are equal.  Maximising coordinate `0` therefore exposes a single monomial.

If that maximal monomial uses any transverse coordinate, its principal Hessian
minor in that coordinate and coordinate `0` is nonzero.  Two honest maximal
initial-form transports lift the minor to the represented source.

Otherwise the maximal monomial is a pure `X₀` power.  If the stored facet
endpoint lies on the base plane `(0,a)`, affine proportionality then forces
the whole ray to lie on that same binary plane.  This gives the exact binary
carrier needed by the existing pure-top binary Hessian rigidity theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- On the affine lower ray, the omitted-coordinate exponent determines the
entire exponent. -/
theorem qs_ray_exponent_eq_of_zeroCoordinate_eq
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    {d e : Fin 4 →₀ ℕ}
    (hd : d ∈ C.ray.face.support)
    (he : e ∈ C.ray.face.support)
    (hde : d (0 : Fin 4) = e (0 : Fin 4)) :
    d = e := by
  apply Finsupp.ext
  intro k
  have hdprop := C.ray.affine_proportional d hd k
  have heprop := C.ray.affine_proportional e he k
  simp only [HC4.Polynomial.facetOmittedCoordinate] at hdprop heprop
  have hout0 :
      (C.ray.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.ray.outside_coordinate_pos)
  have hdeZ :
      (d (0 : Fin 4) : ℤ) = (e (0 : Fin 4) : ℤ) := by
    exact_mod_cast hde
  have hscaled :
      (C.ray.outsideExponent (0 : Fin 4) : ℤ) *
          ((d k : ℤ) - (C.ray.facetExponent k : ℤ)) =
        (C.ray.outsideExponent (0 : Fin 4) : ℤ) *
          ((e k : ℤ) - (C.ray.facetExponent k : ℤ)) := by
    calc
      _ = (d (0 : Fin 4) : ℤ) *
          ((C.ray.outsideExponent k : ℤ) -
            (C.ray.facetExponent k : ℤ)) := hdprop
      _ = (e (0 : Fin 4) : ℤ) *
          ((C.ray.outsideExponent k : ℤ) -
            (C.ray.facetExponent k : ℤ)) := by rw [hdeZ]
      _ = _ := heprop.symm
  have hdiff :
      (d k : ℤ) - (C.ray.facetExponent k : ℤ) =
        (e k : ℤ) - (C.ray.facetExponent k : ℤ) := by
    exact mul_left_cancel₀ hout0 hscaled
  have hkZ : (d k : ℤ) = (e k : ℤ) := by linarith
  exact_mod_cast hkZ

/-- The lower ray face is nonzero because it contains the stored facet
endpoint. -/
theorem qs_ray_face_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    C.ray.face ≠ 0 := by
  intro hzero
  have hmem := C.ray.facet_mem_face
  rw [hzero] at hmem
  simpa using hmem

/-- The coordinate-`0` maximum on the lower affine ray is a literal
singleton monomial. -/
theorem qs_ray_coordinateMax_zero_initialForm_eq_monomial
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    let hface : C.ray.face ≠ 0 :=
      C.qs_ray_face_ne_zero
    let M := HC4.Newton.coordinateMaxInitialData
      C.ray.face hface (0 : Fin 4)
    M.face =
      MvPolynomial.monomial M.witness
        (MvPolynomial.coeff M.witness C.ray.face) := by
  dsimp only
  let hface : C.ray.face ≠ 0 :=
    C.qs_ray_face_ne_zero
  let M := HC4.Newton.coordinateMaxInitialData
    C.ray.face hface (0 : Fin 4)
  rw [M.face_eq]
  apply HC4.Polynomial.initialForm_eq_monomial_of_unique_max
  · exact M.witness_mem
  · rw [HC4.Newton.weight_coordinateMaxWeight]
    exact_mod_cast M.witness_coordinate
  · exact M.weight_bound
  · intro e he hweight
    have he0 : e (0 : Fin 4) = M.witness (0 : Fin 4) := by
      rw [HC4.Newton.weight_coordinateMaxWeight] at hweight
      exact_mod_cast hweight
    exact C.qs_ray_exponent_eq_of_zeroCoordinate_eq
      he M.witness_mem he0

/-- The coordinate-`0` maximal ray exponent is genuinely outside the
starting `.qs` facet. -/
theorem qs_ray_coordinateMax_zero_witness_pos
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    let hface : C.ray.face ≠ 0 :=
      C.qs_ray_face_ne_zero
    let M := HC4.Newton.coordinateMaxInitialData
      C.ray.face hface (0 : Fin 4)
    0 < M.witness (0 : Fin 4) := by
  dsimp only
  let hface : C.ray.face ≠ 0 :=
    C.qs_ray_face_ne_zero
  let M := HC4.Newton.coordinateMaxInitialData
    C.ray.face hface (0 : Fin 4)
  have hle :
      C.ray.outsideExponent (0 : Fin 4) ≤
        M.witness (0 : Fin 4) :=
    M.maximal C.ray.outsideExponent C.ray.outside_mem_face
  exact lt_of_lt_of_le C.ray.outside_coordinate_pos hle

/-- A transverse coordinate occurring in the coordinate-`0` maximal ray
monomial gives an honest principal Hessian minor on the represented source. -/
theorem qs_ray_sourceMinor_of_coordinateMax_zero_transverse
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (j : Fin 4)
    (hj0 : j ≠ (0 : Fin 4))
    (hjpos :
      let hface : C.ray.face ≠ 0 :=
        C.qs_ray_face_ne_zero
      let M := HC4.Newton.coordinateMaxInitialData
        C.ray.face hface (0 : Fin 4)
      0 < M.witness j) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (0 : Fin 4) j ≠ 0 := by
  let hface : C.ray.face ≠ 0 :=
    C.qs_ray_face_ne_zero
  let M := HC4.Newton.coordinateMaxInitialData
    C.ray.face hface (0 : Fin 4)
  have h0pos : 0 < M.witness (0 : Fin 4) :=
    C.qs_ray_coordinateMax_zero_witness_pos
  have hcoeff :
      MvPolynomial.coeff M.witness C.ray.face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp M.witness_mem
  have hmono :
      HC4.Polynomial.hessianPrincipalMinor
          (MvPolynomial.monomial M.witness
            (MvPolynomial.coeff M.witness C.ray.face))
          (0 : Fin 4) j ≠ 0 :=
    HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      hcoeff hj0.symm h0pos hjpos
  have hray :
      HC4.Polynomial.hessianPrincipalMinor C.ray.face (0 : Fin 4) j ≠ 0 := by
    apply HC4.Valuation.hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      M.weight_bound (0 : Fin 4) j
    rw [← M.face_eq]
    rw [C.qs_ray_coordinateMax_zero_initialForm_eq_monomial]
    exact hmono
  rcases C.ray_direct_initialForm_package with
    ⟨W, level, hexposed, hinitial⟩
  have hsourceBound :
      HC4.Polynomial.IsWeightLE W level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
    intro e he
    exact hexposed.weight_le (by simpa using he)
  apply HC4.Valuation.hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    hsourceBound (0 : Fin 4) j
  rw [hinitial]
  exact hray

/-- A represented-source principal minor in the pair `(0,j)` gives the
standard actual rank-two chart. -/
private noncomputable def actualRankTwoChart0j
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (j : Fin 4)
    (hj0 : j ≠ (0 : Fin 4))
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (0 : Fin 4) j ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) j
  have hrho0 : rho (0 : Fin 4) = 0 := by
    dsimp [rho]
    fin_cases j <;> simp_all
  have hrho1 : rho (1 : Fin 4) = j := by
    simp [rho]
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  rw [hrho0, hrho1]
  exact h

/-- If the coordinate-`0` maximal ray point is pure longitudinal and the
starting endpoint is supported on the base plane `(0,a)`, affine
proportionality forces every ray monomial into that binary plane. -/
theorem qs_ray_binarySupport_of_coordinateMax_zero_pure
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (a : Fin 4)
    (ha0 : a ≠ (0 : Fin 4))
    (hfacetBase :
      ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ a →
        C.ray.facetExponent k = 0)
    (hmaxPure :
      let hface : C.ray.face ≠ 0 :=
        C.qs_ray_face_ne_zero
      let M := HC4.Newton.coordinateMaxInitialData
        C.ray.face hface (0 : Fin 4)
      ∀ k : Fin 4, k ≠ (0 : Fin 4) → M.witness k = 0) :
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
      a C.ray.face := by
  let hface : C.ray.face ≠ 0 :=
    C.qs_ray_face_ne_zero
  let M := HC4.Newton.coordinateMaxInitialData
    C.ray.face hface (0 : Fin 4)
  have hM0pos : 0 < M.witness (0 : Fin 4) :=
    C.qs_ray_coordinateMax_zero_witness_pos
  have hout0pos : 0 < C.ray.outsideExponent (0 : Fin 4) :=
    C.ray.outside_coordinate_pos
  intro d hd k hk0 hka
  have hfacetk : C.ray.facetExponent k = 0 :=
    hfacetBase k hk0 hka
  have hMk : M.witness k = 0 := hmaxPure k hk0
  have hMprop := C.ray.affine_proportional M.witness M.witness_mem k
  simp only [HC4.Polynomial.facetOmittedCoordinate] at hMprop
  have houtk : C.ray.outsideExponent k = 0 := by
    have hM0Z : (0 : ℤ) < (M.witness (0 : Fin 4) : ℤ) := by
      exact_mod_cast hM0pos
    have houtkZ : (C.ray.outsideExponent k : ℤ) = 0 := by
      rw [hMk, hfacetk] at hMprop
      simp only [Nat.cast_zero, sub_self, zero_mul, sub_zero] at hMprop
      nlinarith
    exact_mod_cast houtkZ
  have hdprop := C.ray.affine_proportional d hd k
  simp only [HC4.Polynomial.facetOmittedCoordinate] at hdprop
  have hout0Z :
      (0 : ℤ) < (C.ray.outsideExponent (0 : Fin 4) : ℤ) := by
    exact_mod_cast hout0pos
  rw [hfacetk, houtk] at hdprop
  simp only [Nat.cast_zero, sub_zero, sub_self, mul_zero] at hdprop
  have hdkZ : (d k : ℤ) = 0 := by nlinarith
  exact_mod_cast hdkZ

/-- **Coordinate-`0` maximal reduction for a pure-axis starting endpoint.**
Either the represented source already has an actual rank-two chart, or the
entire lower ray lies on the binary plane determined by the starting axis. -/
theorem qs_ray_coordinateMax_actualRankTwo_or_binarySupport
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (a : Fin 4)
    (ha0 : a ≠ (0 : Fin 4))
    (hfacetBase :
      ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ a →
        C.ray.facetExponent k = 0) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
        a C.ray.face := by
  let hface : C.ray.face ≠ 0 :=
    C.qs_ray_face_ne_zero
  let M := HC4.Newton.coordinateMaxInitialData
    C.ray.face hface (0 : Fin 4)
  by_cases h1 : 0 < M.witness (1 : Fin 4)
  · left
    exact ⟨actualRankTwoChart0j (j := (1 : Fin 4)) (by decide)
      (C.qs_ray_sourceMinor_of_coordinateMax_zero_transverse
        (1 : Fin 4) (by decide) h1)⟩
  by_cases h2 : 0 < M.witness (2 : Fin 4)
  · left
    exact ⟨actualRankTwoChart0j (j := (2 : Fin 4)) (by decide)
      (C.qs_ray_sourceMinor_of_coordinateMax_zero_transverse
        (2 : Fin 4) (by decide) h2)⟩
  by_cases h3 : 0 < M.witness (3 : Fin 4)
  · left
    exact ⟨actualRankTwoChart0j (j := (3 : Fin 4)) (by decide)
      (C.qs_ray_sourceMinor_of_coordinateMax_zero_transverse
        (3 : Fin 4) (by decide) h3)⟩
  · right
    apply C.qs_ray_binarySupport_of_coordinateMax_zero_pure a ha0 hfacetBase
    intro k hk0
    have hkval0 : k.val ≠ 0 := by
      intro hk
      apply hk0
      apply Fin.ext
      simpa using hk
    have hkCases : k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by
      omega
    rcases hkCases with hk1 | hk2 | hk3
    · have hk : k = (1 : Fin 4) := by
        apply Fin.ext
        simpa using hk1
      subst k
      exact Nat.eq_zero_of_not_pos h1
    · have hk : k = (2 : Fin 4) := by
        apply Fin.ext
        simpa using hk2
      subst k
      exact Nat.eq_zero_of_not_pos h2
    · have hk : k = (3 : Fin 4) := by
        apply Fin.ext
        simpa using hk3
      subst k
      exact Nat.eq_zero_of_not_pos h3


/-- **Pure-axis endpoint reduction with an honest binary residual.**  The old
pure-axis alternative can be sharpened: after maximising the omitted
coordinate, either the represented source already has an actual rank-two
chart, or the entire lower ray is supported on one base plane `(0,a)` and
the stored facet endpoint is a genuine nonlinear pure `a`-axis power. -/
theorem qs_ray_facetEndpoint_actualRankTwo_or_binarySupport
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      ∃ a : Fin 4,
        a ≠ (0 : Fin 4) ∧
        1 < C.ray.facetExponent a ∧
        (∀ k : Fin 4,
          k ≠ (0 : Fin 4) → k ≠ a → C.ray.facetExponent k = 0) ∧
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
          a C.ray.face := by
  rcases C.qs_ray_facetEndpoint_actualRankTwo_or_pureAxis with
    hactual | h1 | h2 | h3
  · exact Or.inl hactual
  · rcases h1 with ⟨h1gt, h0, h2, h3⟩
    have hbase :
        ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ (1 : Fin 4) →
          C.ray.facetExponent k = 0 := by
      intro k hk0 hk1
      fin_cases k
      · exact (hk0 rfl).elim
      · exact (hk1 rfl).elim
      · exact h2
      · exact h3
    rcases C.qs_ray_coordinateMax_actualRankTwo_or_binarySupport
        (1 : Fin 4) (by decide) hbase with htwo | hbinary
    · exact Or.inl htwo
    · exact Or.inr ⟨(1 : Fin 4), by decide, h1gt, hbase, hbinary⟩
  · rcases h2 with ⟨h2gt, h0, h1, h3⟩
    have hbase :
        ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ (2 : Fin 4) →
          C.ray.facetExponent k = 0 := by
      intro k hk0 hk2
      fin_cases k
      · exact (hk0 rfl).elim
      · exact h1
      · exact (hk2 rfl).elim
      · exact h3
    rcases C.qs_ray_coordinateMax_actualRankTwo_or_binarySupport
        (2 : Fin 4) (by decide) hbase with htwo | hbinary
    · exact Or.inl htwo
    · exact Or.inr ⟨(2 : Fin 4), by decide, h2gt, hbase, hbinary⟩
  · rcases h3 with ⟨h3gt, h0, h1, h2⟩
    have hbase :
        ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ (3 : Fin 4) →
          C.ray.facetExponent k = 0 := by
      intro k hk0 hk3
      fin_cases k
      · exact (hk0 rfl).elim
      · exact h1
      · exact h2
      · exact (hk3 rfl).elim
    rcases C.qs_ray_coordinateMax_actualRankTwo_or_binarySupport
        (3 : Fin 4) (by decide) hbase with htwo | hbinary
    · exact Or.inl htwo
    · exact Or.inr ⟨(3 : Fin 4), by decide, h3gt, hbase, hbinary⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
