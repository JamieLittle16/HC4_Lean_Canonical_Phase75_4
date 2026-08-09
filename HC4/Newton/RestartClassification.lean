import HC4.Newton.SmithRefinedFacePolynomial
import HC4.Newton.RankTwoRepairTerminal
import HC4.Newton.TerminalPositiveWeightEndpoint
import HC4.Newton.TerminalOneZeroEndpoint
import HC4.Newton.TerminalTwoZeroJC2Endpoint
import Mathlib.Tactic

/-!
# Local restart classification assembly

This module is the first genuine orchestration layer for the candidate
`JC₂ => HC₄` restart proof.

The local algebraic work is now expressed through one interface:

    terminal certificate OR a `RepairProgress` successor.

Three independently developed branches are converted to that shape:

* the canonical Smith first-wall restriction;
* a preterminal mixed departure;
* a rank-two Schur entry.

`FiniteRepairTermination` then supplies the well-founded iteration theorem:
if the geometric restart extraction produces one of these local classifiers
at every nonterminal state, a terminal state is reached after finitely many
repair steps.

The second half of the file unifies the already-green terminal endpoint
theorems.  A certified endpoint is one of:

* strictly-positive non-scalar terminal weights;
* the standard one-zero endpoint;
* the standard two-zero endpoint.

Under `PlanarJC2Injectivity`, every such endpoint has injective gradient,
hence cannot contain a distinct exact gradient collision.

Important scope boundary:
this file does NOT yet formalise the DVR/kernel-blow-up layer that extracts
a total local classifier from an arbitrary HC4 counterexample.  It closes
the finite local recursion once that extraction is supplied.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]
variable {σ : Type*} [DecidableEq σ]

/-! ## Uniform one-step repair interfaces -/

/-- The canonical Smith first wall is already in the common one-step
restart form: rigid rank-one packet, or a genuine rank-one to rank-two
repair successor. -/
theorem smithFirstWall_hasRepairOrTerminal
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent -> ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    HasRepairOrTerminal
      (HasRigidRankOnePacket x y z D G)
      (rankOneRepairState complexity) := by
  dsimp
  have hout :=
    homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_canonicalRepair
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain complexity
  rcases hout.2.2.2 with hterminal | hrepair
  · exact Or.inl hterminal
  · exact
      Or.inr
        ⟨rankTwoRepairState complexity, hrepair.2.1⟩

/-- A preterminal first departure is uniformly either the affine/separated
terminal channel or the canonical rank-one to rank-two repair successor. -/
theorem mixedDeparture_hasRepairOrTerminal
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    HasRepairOrTerminal
      (IsPreterminalAffineSeparatedChannel U V P)
      (rankOneRepairState complexity) := by
  rcases
      preterminal_departure_canonicalStrictRepair_or_affineSeparated
        b hb U V P complexity hsource with
    hrepair | hterminal
  · exact
      Or.inr
        ⟨rankTwoRepairState complexity, hrepair.2.1⟩
  · exact Or.inl hterminal

/-- A rank-two Schur entry is uniformly either a rigid rank-two terminal
packet or the canonical rank-two to rank-three repair successor. -/
theorem rankTwoSchurEntry_hasRepairOrTerminal
    [CharZero K]
    (q : BinarySchurBlock K)
    (hnz : q.Nonzero)
    {i j : σ}
    (hij : i ≠ j)
    (n mLeft mRight complexity : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmLeftPos : 0 < mLeft)
    (hmRightPos : 0 < mRight)
    (hexactLeft :
      HasExactTransverseDegree i j mLeft
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hexactRight :
      HasExactTransverseDegree i j mRight
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hleftKernel :
      q.LeftPivot -> HasLeftPivotHessianKernel q i j F)
    (hrightKernel :
      q.RightAxisPivot -> HasRightAxisHessianKernel i j F) :
    HasRepairOrTerminal
      (HasRigidRankTwoTerminal q i j n F)
      (rankTwoRepairState complexity) := by
  rcases
      rankTwoSchurEntry_terminal_or_strictRepair
        q hnz hij n mLeft mRight complexity F
        hexactF hmLeftPos hmRightPos
        hexactLeft hexactRight hleftKernel hrightKernel with
    hterminal | hrepair
  · exact Or.inl hterminal
  · exact
      Or.inr
        ⟨rankThreeRepairState complexity, hrepair.2.1⟩

/-! ## Generic local restart closure -/

/-- A convenient restart-facing alias for the finite well-founded theorem.

The only remaining input is a *total local classifier*: for each repair
state, either an endpoint certificate is available or the geometric
extraction supplies a strictly smaller repair state. -/
theorem localRestartClassification
    (Terminal : RepairState -> Prop)
    (hlocal : IsTotalRepairClassifier Terminal)
    (s : RepairState) :
    ∃ t : RepairState,
      RepairReachable s t ∧ Terminal t := by
  exact
    repairClassifier_reaches_terminal
      Terminal hlocal s

/-! ## Unified terminal endpoint certificate -/

section TerminalEndpoints

variable {F : MvPolynomial (Fin 4) K}

/-- The three terminal endpoint families currently closed in Lean.

The certificate stores exactly the hypotheses of the existing endpoint
theorems and nothing stronger. -/
inductive CertifiedTerminalEndpoint
    (F : MvPolynomial (Fin 4) K) : Prop
  | positive
      (lambda : Fin 4 -> ℤ)
      (d : ℤ)
      (hface :
        HasNonScalarTerminalConformalFace
          (0 : Fin 4) 1 2 3 lambda d F)
      (hpos :
        HasStrictlyPositiveTerminalWeights lambda) :
      CertifiedTerminalEndpoint F
  | oneZero
      (d a : ℤ)
      (ha : 0 < a)
      (had : a < d)
      (hhom :
        IsIntegralWeightedHomogeneous
          (standardOneZeroTerminalWeight d a) d F)
      (hMA :
        HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
      CertifiedTerminalEndpoint F
  | twoZero
      (d : ℤ)
      (hd : 0 < d)
      (hhom :
        IsIntegralWeightedHomogeneous
          (standardTwoZeroTerminalWeight d) d F)
      (hMA :
        HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
      CertifiedTerminalEndpoint F

/-- **Unified terminal injectivity theorem.**

Under JC2, every terminal family already certified in the current Lean tree
has injective four-dimensional gradient. -/
theorem certifiedTerminalEndpoint_gradient_injective_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {F : MvPolynomial (Fin 4) K}
    (hterminal : CertifiedTerminalEndpoint F) :
    Function.Injective (mvGradientMap F) := by
  cases hterminal with
  | positive lambda d hface hpos =>
      exact
        positiveTerminalFace_gradient_injective
          hface hpos
  | oneZero d a ha had hhom hMA =>
      exact
        standardOneZero_terminal_gradient_injective_of_JC2
          hJC2 ha had hhom hMA
  | twoZero d hd hhom hMA =>
      exact
        standardTwoZero_terminal_gradient_injective_of_JC2
          hJC2 hd hhom hMA

/-- **Unified terminal collision contradiction.**

A distinct exact collision cannot survive any certified terminal endpoint
under JC2.  This is the endpoint statement wanted by the eventual global
DVR restart theorem. -/
theorem certifiedTerminalEndpoint_collision_impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {F : MvPolynomial (Fin 4) K}
    (hterminal : CertifiedTerminalEndpoint F)
    {p q : Fin 4 -> K}
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    False := by
  exact
    exactGradientCollision_impossible_of_injective
      F p q hpq
      (certifiedTerminalEndpoint_gradient_injective_of_JC2
        hJC2 hterminal)
      hcoll

end TerminalEndpoints

end

end HC4.Newton
