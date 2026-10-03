import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointPureAxisMax
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreBinaryPlanarisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCurvedElimination
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Binary closure of the pure-axis lower-ray endpoint

After the coordinate-max reduction the only remaining lower `.qs` ray is
supported on one honest coordinate plane `(0,a)`.  We planarise that support
exactly to two variables.

The first-contact equation gives three decisive facts on the binary support:

* every monomial has ordinary degree at most the stored top degree `D`;
* degree `D` occurs only on the transverse axis `a`;
* the stored pure-axis facet endpoint contributes the nonzero monomial
  `X_a^D`.

The stored outside ray point gives genuine support with positive longitudinal
coordinate.  Therefore the existing binary pure-top singular-Hessian rigidity
theorem applies.  If the binary Hessian determinant vanished it would forbid
that outside support, a contradiction.  Hence the binary Hessian determinant
is nonzero, and exact planarisation plus the honest ray initial-form package
lift the corresponding principal Hessian minor all the way to the represented
source.

This bypasses the auxiliary reverse-Rees first-break layer entirely.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The ordinary principal Hessian minor is exactly the binary directional
Hessian determinant in the same coordinate pair. -/
private theorem hessianPrincipalMinor_eq_binaryDirectionalHessianDet
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor F i j =
      HC4.Newton.binaryDirectionalHessianDet i j F := by
  unfold HC4.Polynomial.hessianPrincipalMinor
    HC4.Newton.binaryDirectionalHessianDet
    HC4.Newton.directionalSecondDerivative
    HC4.Newton.directionalMixedDerivative
  simp only [HC4.Polynomial.hessian_apply, pow_two]
  have hcomm :
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i F) :=
    pderiv_comm_commRing i j F
  rw [hcomm]

/-- A source principal minor in coordinates `(0,a)` gives an actual
rank-two chart. -/
private noncomputable def actualRankTwoChart0a
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (a : Fin 4)
    (ha0 : a ≠ (0 : Fin 4))
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (0 : Fin 4) a ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  by_cases ha1 : a = (1 : Fin 4)
  · subst a
    refine {
      permutation := Equiv.refl (Fin 4)
      activeDet_coeff_zero_ne_zero := ?_
    }
    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
    simpa using h
  by_cases ha2 : a = (2 : Fin 4)
  · subst a
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
    refine {
      permutation := rho
      activeDet_coeff_zero_ne_zero := ?_
    }
    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
    simpa [rho] using h
  · have ha0v : a.val ≠ 0 := by
      intro hv
      apply ha0
      apply Fin.ext
      simpa using hv
    have ha1v : a.val ≠ 1 := by
      intro hv
      apply ha1
      apply Fin.ext
      simpa using hv
    have ha2v : a.val ≠ 2 := by
      intro hv
      apply ha2
      apply Fin.ext
      simpa using hv
    have ha3v : a.val = 3 := by
      have halt : a.val < 4 := a.isLt
      omega
    have ha3 : a = (3 : Fin 4) := by
      apply Fin.ext
      simpa using ha3v
    subst a
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
    refine {
      permutation := rho
      activeDet_coeff_zero_ne_zero := ?_
    }
    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
    simpa [rho] using h

/-- A pure-axis facet endpoint has exactly the top degree on that axis. -/
private theorem qs_ray_facetExponent_eq_single_axis
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (a : Fin 4)
    (ha0 : a ≠ (0 : Fin 4))
    (hfacetBase :
      ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ a →
        C.ray.facetExponent k = 0) :
    C.ray.facetExponent =
      Finsupp.single a T.topFace.degree := by
  have h0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    C.ray.facet_coordinate_zero
  have hcontact :=
    C.ray_contact_eq C.ray.facetExponent C.ray.facet_mem_face
  simp only [HC4.Polynomial.facetOmittedCoordinate] at hcontact
  unfold HC4.Newton.scaledContactExponentWeight at hcontact
  rw [h0] at hcontact
  simp only [Nat.cast_zero, mul_zero, add_zero] at hcontact
  push_cast at hcontact
  have hsZ : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent =
        T.topFace.degree := by
    nlinarith
  fin_cases a
  · exact (ha0 rfl).elim
  · have h2 := hfacetBase (2 : Fin 4) (by decide) (by decide)
    have h3 := hfacetBase (3 : Fin 4) (by decide) (by decide)
    have h1 : C.ray.facetExponent (1 : Fin 4) = T.topFace.degree := by
      simp [HC4.Polynomial.ordinaryDegree4, h0, h2, h3] at hdeg
      exact hdeg
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [Finsupp.single_apply, h0, h1, h2, h3]
  · have h1 := hfacetBase (1 : Fin 4) (by decide) (by decide)
    have h3 := hfacetBase (3 : Fin 4) (by decide) (by decide)
    have h2 : C.ray.facetExponent (2 : Fin 4) = T.topFace.degree := by
      simp [HC4.Polynomial.ordinaryDegree4, h0, h1, h3] at hdeg
      exact hdeg
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [Finsupp.single_apply, h0, h1, h2, h3]
  · have h1 := hfacetBase (1 : Fin 4) (by decide) (by decide)
    have h2 := hfacetBase (2 : Fin 4) (by decide) (by decide)
    have h3 : C.ray.facetExponent (3 : Fin 4) = T.topFace.degree := by
      simp [HC4.Polynomial.ordinaryDegree4, h0, h1, h2] at hdeg
      exact hdeg
    apply Finsupp.ext
    intro k
    fin_cases k <;>
      simp [Finsupp.single_apply, h0, h1, h2, h3]

/-- **Binary lower-ray closure.**  An honest binary-plane residual with a
pure transverse top endpoint always yields an actual represented-source
rank-two chart. -/
theorem qs_ray_binarySupport_actualRankTwo
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (a : Fin 4)
    (ha0 : a ≠ (0 : Fin 4))
    (ha : 1 < C.ray.facetExponent a)
    (hfacetBase :
      ∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ a →
        C.ray.facetExponent k = 0)
    (hbinary :
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsTransverseBaseSupport
        a C.ray.face) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  let emb :=
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding
      a ha0
  rcases
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseSupport_exists_binaryPlanarisation
        (K := K) ha0 hbinary with
    ⟨Q, hQrename⟩

  have hsuppRename :
      (MvPolynomial.rename emb Q).support =
        Finset.image (Finsupp.mapDomain emb) Q.support := by
    exact MvPolynomial.support_rename_of_injective emb.injective

  have ambient_mem
      {d : Fin 2 →₀ ℕ}
      (hd : d ∈ Q.support) :
      d.mapDomain emb ∈ C.ray.face.support := by
    rw [← hQrename, hsuppRename]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

  have mapDomain_degree (d : Fin 2 →₀ ℕ) :
      (d.mapDomain emb).degree = d.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    simpa [Finsupp.sum_fintype] using
      (Finsupp.sum_mapDomain_index_addMonoidHom
        (f := (emb : Fin 2 → Fin 4)) (s := d)
        (fun _ : Fin 4 => AddMonoidHom.id ℕ))

  have degree_map (d : Fin 2 →₀ ℕ) :
      HC4.Polynomial.ordinaryDegree4 (d.mapDomain emb) = d.degree := by
    rw [← finsuppDegree_eq_ordinaryDegree4]
    exact mapDomain_degree d

  have map_zero_apply (d : Fin 2 →₀ ℕ) :
      (d.mapDomain emb) (0 : Fin 4) = d (0 : Fin 2) := by
    rw [← AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding_zero
      a ha0]
    exact Finsupp.mapDomain_apply emb.injective d (0 : Fin 2)

  let D := T.topFace.degree
  have hfacetEq :
      C.ray.facetExponent = Finsupp.single a D := by
    simpa [D] using
      C.qs_ray_facetExponent_eq_single_axis a ha0 hfacetBase
  have haD : C.ray.facetExponent a = D := by
    have happ :=
      congrArg (fun e : Fin 4 →₀ ℕ => e a) hfacetEq
    simpa using happ
  have hD : 2 ≤ D := by
    omega

  have hmax :
      ∀ d ∈ Q.support, d.degree ≤ D := by
    intro d hd
    let e := d.mapDomain emb
    have he : e ∈ C.ray.face.support := ambient_mem hd
    have hcontact := C.ray_contact_eq e he
    simp only [HC4.Polynomial.facetOmittedCoordinate] at hcontact
    unfold HC4.Newton.scaledContactExponentWeight at hcontact
    have hsZ : (0 : ℤ) < (C.scale : ℤ) := by exact_mod_cast C.scale_pos
    have hbZ : (0 : ℤ) < (C.bump : ℤ) := by exact_mod_cast C.bump_pos
    have he0Z : (0 : ℤ) ≤ (e (0 : Fin 4) : ℤ) := by omega
    have hdegLe :
        HC4.Polynomial.ordinaryDegree4 e ≤ T.topFace.degree := by
      by_contra hnot
      have hgt :
          T.topFace.degree < HC4.Polynomial.ordinaryDegree4 e := by omega
      have hgtZ :
          (T.topFace.degree : ℤ) <
            (HC4.Polynomial.ordinaryDegree4 e : ℤ) := by
        exact_mod_cast hgt
      push_cast at hcontact
      nlinarith
    dsimp [e] at hdegLe
    rw [degree_map d] at hdegLe
    simpa [D] using hdegLe

  have htopFacet :
      ∀ d ∈ Q.support, d.degree = D → d (0 : Fin 2) = 0 := by
    intro d hd hdD
    let e := d.mapDomain emb
    have he : e ∈ C.ray.face.support := ambient_mem hd
    have hcontact := C.ray_contact_eq e he
    simp only [HC4.Polynomial.facetOmittedCoordinate] at hcontact
    unfold HC4.Newton.scaledContactExponentWeight at hcontact
    have hdegE :
        HC4.Polynomial.ordinaryDegree4 e = T.topFace.degree := by
      dsimp [e]
      rw [degree_map d, hdD]
    have hbZ : (0 : ℤ) < (C.bump : ℤ) := by exact_mod_cast C.bump_pos
    have he0Z : (0 : ℤ) ≤ (e (0 : Fin 4) : ℤ) := by omega
    have he0 : e (0 : Fin 4) = 0 := by
      rw [hdegE] at hcontact
      push_cast at hcontact
      nlinarith
    dsimp [e] at he0
    rw [map_zero_apply d] at he0
    exact he0

  have hfacetEq :
      C.ray.facetExponent = Finsupp.single a D := by
    simpa [D] using
      C.qs_ray_facetExponent_eq_single_axis a ha0 hfacetBase

  have hmapTop :
      (Finsupp.single (1 : Fin 2) D).mapDomain emb =
        Finsupp.single a D := by
    simp [emb,
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding]

  have hfacetCoeff :
      MvPolynomial.coeff C.ray.facetExponent C.ray.face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face

  have htopCoeff :
      MvPolynomial.coeff (Finsupp.single (1 : Fin 2) D) Q ≠ 0 := by
    have hcoeff :=
      MvPolynomial.coeff_rename_mapDomain
        emb emb.injective Q (Finsupp.single (1 : Fin 2) D)
    rw [hQrename, hmapTop, ← hfacetEq] at hcoeff
    intro hz
    apply hfacetCoeff
    rw [hcoeff, hz]

  have hlinear :
      MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) Q = 0 := by
    by_contra hne
    have hmapLinear :
        (Finsupp.single (0 : Fin 2) 1).mapDomain emb =
          Finsupp.single (0 : Fin 4) 1 := by
      simp [emb,
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.transverseBaseEmbedding]
    have hcoeff :=
      MvPolynomial.coeff_rename_mapDomain
        emb emb.injective Q (Finsupp.single (0 : Fin 2) 1)
    rw [hQrename, hmapLinear] at hcoeff
    have hamb :
        MvPolynomial.coeff (Finsupp.single (0 : Fin 4) 1) C.ray.face ≠ 0 := by
      intro hz
      apply hne
      rw [← hcoeff, hz]
    have hdeg :=
      C.ray_support_degree_ge_three
        (Finsupp.single (0 : Fin 4) 1)
        (MvPolynomial.mem_support_iff.mpr hamb)
    simp [HC4.Polynomial.ordinaryDegree4, Finsupp.single_apply] at hdeg

  have houtAmbient :
      C.ray.outsideExponent ∈
        (MvPolynomial.rename emb Q).support := by
    rw [hQrename]
    exact C.ray.outside_mem_face
  rw [hsuppRename] at houtAmbient
  rcases Finset.mem_image.mp houtAmbient with ⟨dout, hdoutQ, hdoutMap⟩
  have hdout0 :
      0 < dout (0 : Fin 2) := by
    have happ :
        (dout.mapDomain emb) (0 : Fin 4) =
          C.ray.outsideExponent (0 : Fin 4) := by
      simpa using
        congrArg (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) hdoutMap
    rw [map_zero_apply dout] at happ
    rw [happ]
    exact C.ray.outside_coordinate_pos
  have houtQ :
      (binaryOutsideSupport (0 : Fin 2) Q).Nonempty :=
    ⟨dout, mem_binaryOutsideSupport.mpr ⟨hdoutQ, hdout0⟩⟩

  have hbinaryDet :
      HC4.Newton.binaryDirectionalHessianDet
          (0 : Fin 2) (1 : Fin 2) Q ≠ 0 := by
    intro hdet
    have hno :=
      binarySingularHessian_no_outsideSupport_of_pureTop
        Q D (1 : Fin 2) (0 : Fin 2) (by decide)
        hD hmax htopFacet htopCoeff hlinear hdet
    exact hno houtQ

  have hrenameDet :
      MvPolynomial.rename emb
          (HC4.Newton.binaryDirectionalHessianDet
            (0 : Fin 2) (1 : Fin 2) Q) ≠ 0 := by
    intro hz
    apply hbinaryDet
    apply MvPolynomial.rename_injective emb emb.injective
    simpa using hz

  have hrayDet :
      HC4.Newton.binaryDirectionalHessianDet
          (0 : Fin 4) a C.ray.face ≠ 0 := by
    rw [← hQrename]
    rw [AdaptiveAlignedSmithRankOneClosingSourceCarrier.binaryDirectionalHessianDet_rename_transverseBaseEmbedding]
    exact hrenameDet

  have hrayMinor :
      HC4.Polynomial.hessianPrincipalMinor
          C.ray.face (0 : Fin 4) a ≠ 0 := by
    rw [hessianPrincipalMinor_eq_binaryDirectionalHessianDet]
    exact hrayDet

  rcases C.ray_direct_initialForm_package with
    ⟨W, level, hexposed, hinitial⟩
  have hsourceBound :
      HC4.Polynomial.IsWeightLE W level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
    intro e he
    exact hexposed.weight_le (by simpa using he)
  have hsourceMinor :
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (0 : Fin 4) a ≠ 0 := by
    apply HC4.Valuation.hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      hsourceBound (0 : Fin 4) a
    rw [hinitial]
    exact hrayMinor

  exact ⟨actualRankTwoChart0a a ha0 hsourceMinor⟩

/-- **Pure-axis endpoint eliminated.**  The lower `.qs` facet endpoint now
always yields an actual represented-source rank-two chart; there is no
remaining reverse-Rees first-break layer branch. -/
theorem qs_ray_facetEndpoint_actualRankTwo
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases C.qs_ray_facetEndpoint_actualRankTwo_or_binarySupport with
    hactual | hbinary
  · exact hactual
  · rcases hbinary with ⟨a, ha0, ha, hfacetBase, hbase⟩
    exact C.qs_ray_binarySupport_actualRankTwo
      a ha0 ha hfacetBase hbase

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
