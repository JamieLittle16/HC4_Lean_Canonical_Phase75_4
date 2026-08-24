import HC4.Valuation.AdaptiveAlignedSmithCanonicalAllTransverseRationalKernelDispatcher
import HC4.Valuation.AdaptiveAlignedSmithMixedDegreePointedReflection
import Mathlib.Tactic

/-!
# Canonical stationary mixed-source dispatcher

After all positive saturated rational transverse kernel slopes have been
consumed, every surviving canonical blocker lies in a common source normal
form.  Independently, the pure-degree alternative for a canonical blocker is
already impossible, so the right-recentered raw special fibre carries an
explicit mixed-degree pair.

This file packages those two facts together and removes the artificial
five-way split from the *global* dispatcher.  The remaining Schur / rigid
geometry is retained as a local tag on one stationary blocker.  Thus the next
local theorem has a single source-facing input:

* exact canonical blocker provenance;
* zero integral kernel slope in the endpoint presentation;
* zero integral kernel slope in the honest right-recentered presentation;
* zero saturated rational slope in all three transverse directions;
* an explicit mixed-degree pair in the right-recentered raw special fibre.

No terminal classification or JC2 hypothesis is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The common stationary source normal form left after rational-kernel
normalisation.

The `mixed_eq` field is intentionally retained.  It prevents the final local
elimination theorem from losing the identity of the blocker while moving
between the source-normal-form and branch-specific views. -/
structure AdaptiveAlignedSmithCanonicalStationaryBlocker
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  blocker : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap
  mixed : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint (K := K) s.degreeCap
  mixed_eq : mixed.blocker = blocker
  endpointZero :
    AdaptiveKernelZeroSlopeObstruction
      (blocker.aligned.toAdaptiveState s)
      adaptiveCanonicalCommonKernel
  recenteredZero :
    AdaptiveRecenteredKernelZeroSlopeObstruction
      blocker adaptiveCanonicalCommonKernel
  allTransverseZero :
    AdaptiveRecenteredAllTransverseZeroRationalSlope blocker

namespace AdaptiveAlignedSmithCanonicalStationaryBlocker

/-- The stationary blocker is genuinely nonhomogeneous after longitudinal
right recentering.  This is the source-degree obstruction which survives all
rational-kernel normalisation. -/
theorem recentered_not_isHomogeneous
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s)
    (D : ℕ) :
    ¬ (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber).IsHomogeneous D := by
  have h := S.mixed.recentered_not_isHomogeneous D
  rw [S.mixed_eq] at h
  exact h

/-- The same mixedness certificate, stated directly on the honest
right-recentered family special fibre used by every surviving local branch. -/
theorem specialFiber_mixedDegree_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    ∃ d₀ d₁ : Fin 4 →₀ ℕ,
      d₀ ∈ (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      d₁ ∈ (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      HC4.Polynomial.ordinaryDegree4 d₀ ≠
        HC4.Polynomial.ordinaryDegree4 d₁ := by
  refine ⟨S.mixed.d₀, S.mixed.d₁, ?_, ?_, S.mixed.degree_ne⟩
  · rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    have h := S.mixed.d₀_mem
    rw [S.mixed_eq] at h
    exact h
  · rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    have h := S.mixed.d₁_mem
    rw [S.mixed_eq] at h
    exact h

/-- In particular the honest stationary special fibre is not homogeneous in
any ordinary degree. -/
theorem specialFiber_not_isHomogeneous
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s)
    (D : ℕ) :
    ¬ (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily).IsHomogeneous D := by
  rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
  exact S.recentered_not_isHomogeneous D

/-- Each transverse coordinate occurs in the honest right-recentered special
fibre of a stationary blocker. -/
theorem specialFiber_witnesses
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) :
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (1 : Fin 4)) ∧
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (2 : Fin 4)) ∧
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (3 : Fin 4)) :=
  S.allTransverseZero.specialFiber_witnesses

end AdaptiveAlignedSmithCanonicalStationaryBlocker

/-- The five branch-specific geometries retained on a *single* stationary
source normal form.  These are deliberately local tags: all global descent,
reentry, and zero-defect alternatives have already been discharged before
this type is constructed. -/
inductive AdaptiveAlignedSmithCanonicalStationaryGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s) : Prop

  | schurEarlyActualLayer
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)

  | schurCanonicalEarlierWall
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (hwall :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWall D)

  | zeroSchur
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
      (W : AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C)

  | planarRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Final global outcome after stationary-source consolidation.

There is now only one unresolved global constructor.  Its `geometry` field
remembers which local Schur / packet certificate led to the stationary
source, but all source-facing hypotheses are shared through `S`. -/
inductive AdaptiveAlignedSmithCanonicalStationaryOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  | stationary
      (S : AdaptiveAlignedSmithCanonicalStationaryBlocker s)
      (geometry : AdaptiveAlignedSmithCanonicalStationaryGeometry S)

/-- **Stationary mixed-source dispatcher.**

All five all-transverse-zero-rational blocker constructors are consolidated
onto one source normal form.  The degree-pure alternative is eliminated by
the already-proved canonical blocker rigidity theorem, so the retained
stationary source is explicitly mixed-degree. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryOutcome RR s complexity := by
  rcases
      s.alignedSmithCanonicalAllTransverseRationalKernelDispatcher
        RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt, Z, ZR, ZA⟩ |
    ⟨B, C, D, hwall, Z, ZR, ZA⟩ |
    ⟨B, C, O, W, Z, ZR, ZA⟩ |
    ⟨B, hall, P, hrigid, Z, ZR, ZA⟩ |
    ⟨B, hall, P, hrigid, Z, ZR, ZA⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let S : AdaptiveAlignedSmithCanonicalStationaryBlocker s :=
      {
        blocker := B
        mixed := M
        mixed_eq := hM
        endpointZero := Z
        recenteredZero := ZR
        allTransverseZero := ZA
      }
    exact .stationary S (.schurEarlyActualLayer C hlt)

  · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let S : AdaptiveAlignedSmithCanonicalStationaryBlocker s :=
      {
        blocker := B
        mixed := M
        mixed_eq := hM
        endpointZero := Z
        recenteredZero := ZR
        allTransverseZero := ZA
      }
    exact .stationary S (.schurCanonicalEarlierWall C D hwall)

  · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let S : AdaptiveAlignedSmithCanonicalStationaryBlocker s :=
      {
        blocker := B
        mixed := M
        mixed_eq := hM
        endpointZero := Z
        recenteredZero := ZR
        allTransverseZero := ZA
      }
    exact .stationary S (.zeroSchur C O W)

  · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let S : AdaptiveAlignedSmithCanonicalStationaryBlocker s :=
      {
        blocker := B
        mixed := M
        mixed_eq := hM
        endpointZero := Z
        recenteredZero := ZR
        allTransverseZero := ZA
      }
    exact .stationary S (.planarRigidPacket hall P hrigid)

  · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let S : AdaptiveAlignedSmithCanonicalStationaryBlocker s :=
      {
        blocker := B
        mixed := M
        mixed_eq := hM
        endpointZero := Z
        recenteredZero := ZR
        allTransverseZero := ZA
      }
    exact .stationary S (.wSquareRigidPacket hall P hrigid)

end

end HC4.Valuation
