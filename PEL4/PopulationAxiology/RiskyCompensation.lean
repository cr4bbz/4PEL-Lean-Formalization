import PEL4.PopulationAxiology.FourCellKernel
import PEL4.PopulationAxiology.ParaconsistentComparison

namespace PEL4.PopulationAxiology

/-!
# Reciprocal-risk compensation and finite transport

The rational contract below preserves the quantifier order of Risky General
Non-Extreme Priority: for every upper welfare level there are fixed `m`, `r`,
and `p = 1/r`; the same witnesses must work for every admissible `k`, every
barely-positive compensation level, every very-positive compensation level,
and every background population.

This is a typed formal statement of that one condition, with abstract
predicates for the two welfare bands and an abstract prospect comparison. It
does not assert the condition, identify a concrete welfare scale, or formalize
the remaining axioms of the Risky Sixth Impossibility Theorem.
-/

universe u

/-- Rational Risky General Non-Extreme Priority. `lower a` plays the role of
`a - 1`; the two predicates encode `0 < b <= 3` and `c >= beta`. -/
def RationalRiskyGeneralNonExtremePriority
    {Welfare : Type u}
    (lower : Welfare -> Welfare)
    (barelyPositive veryPositive : Welfare -> Prop)
    (noBetterThan :
      BinaryProspect (Population Welfare) ->
      BinaryProspect (Population Welfare) -> Prop) : Prop :=
  forall a : Welfare,
    exists m r : Nat, exists p : Rat,
      0 < r ∧ 0 < p ∧ p = 1 / (r : Rat) ∧
      forall k : Rat, 0 ≤ k -> k ≤ 1 - p ->
      forall b c : Welfare,
        barelyPositive b -> veryPositive c ->
        forall background : Population Welfare,
          noBetterThan
            (riskShiftProspect background a (lower a) m b k)
            (riskShiftProspect background a (lower a) m c (k + p))

/-!
## The transitivity engine

The paper's derivation applies the risky condition exactly `r` times. Each
application increases the bad-outcome probability by `p`; `r * p = 1` closes
the path at certainty. `ExactStepChain` records the number of applications,
while `ReciprocalRiskChain` records the arithmetic closure condition.
-/

/-- A finite chain indexed by its exact number of local steps. -/
inductive ExactStepChain {A : Type u} (step : A -> A -> Prop) :
    Nat -> A -> A -> Prop
  | zero (x : A) : ExactStepChain step 0 x x
  | succ {n : Nat} {x y z : A} :
      step x y ->
      ExactStepChain step n y z ->
      ExactStepChain step (n + 1) x z

namespace ExactStepChain

/-- Forgetting the exact length yields the earlier finite-path notion. -/
theorem toFiniteStepChain
    {A : Type u} {step : A -> A -> Prop} {n : Nat} {x y : A}
    (chain : ExactStepChain step n x y) :
    FiniteStepChain step x y := by
  induction chain with
  | zero x => exact .refl x
  | succ hStep _ ih => exact .cons hStep ih

/-- Reflexivity, transitivity, and local acceptance transport along an exact
finite step count. -/
theorem transport
    {A : Type u}
    {step comparison : A -> A -> Prop}
    (comparison_refl : forall x, comparison x x)
    (comparison_trans : forall {x y z},
      comparison x y -> comparison y z -> comparison x z)
    (local_transport : forall {x y}, step x y -> comparison x y)
    {n : Nat} {x y : A}
    (chain : ExactStepChain step n x y) :
    comparison x y := by
  induction chain with
  | zero x => exact comparison_refl x
  | succ hStep _ ih =>
      exact comparison_trans (local_transport hStep) ih

end ExactStepChain

/-- A path of exactly `r` identical risk increments `p`, with `r * p = 1`. -/
structure ReciprocalRiskChain
    {A : Type u}
    (riskStep : Rat -> A -> A -> Prop)
    (source target : A) where
  rounds : Nat
  increment : Rat
  rounds_positive : 0 < rounds
  increment_positive : 0 < increment
  closes_total_risk : (rounds : Rat) * increment = 1
  steps : ExactStepChain (riskStep increment) rounds source target

/-- The exact structural content of the risky iteration: local comparison at
each reciprocal-risk step plus transitivity yields the endpoint comparison. -/
theorem reciprocalRiskTransport
    {A : Type u}
    {riskStep : Rat -> A -> A -> Prop}
    {comparison : A -> A -> Prop}
    (comparison_refl : forall x, comparison x x)
    (comparison_trans : forall {x y z},
      comparison x y -> comparison y z -> comparison x z)
    (local_transport : forall {p x y}, riskStep p x y -> comparison x y)
    {source target : A}
    (chain : ReciprocalRiskChain riskStep source target) :
    comparison source target :=
  chain.steps.transport comparison_refl comparison_trans
    (fun h => local_transport h)

/-- If an independent adequacy route rejects the endpoint comparison, the
risky transitivity engine produces `B`, not logical explosion. -/
theorem reciprocalRisk_axiological_glut
    {A : Type u}
    {riskStep : Rat -> A -> A -> Prop}
    {supports rejects : A -> A -> Prop}
    [DecidableRel supports] [DecidableRel rejects]
    (supports_refl : forall x, supports x x)
    (supports_trans : forall {x y z},
      supports x y -> supports y z -> supports x z)
    (local_transport : forall {p x y}, riskStep p x y -> supports x y)
    {source target : A}
    (chain : ReciprocalRiskChain riskStep source target)
    (hReject : rejects source target) :
    comparisonValue supports rejects source target = FDEValue.B := by
  apply comparisonValue_eq_B supports rejects
  · exact reciprocalRiskTransport supports_refl supports_trans
      local_transport chain
  · exact hReject

/-! ## One finite model of the bridge -/

inductive RiskStage
  | start
  | finish
  | unrelated
  deriving DecidableEq, Repr

def toyRiskStep (_ : Rat) : RiskStage -> RiskStage -> Prop
  | .start, .finish => True
  | _, _ => False

def toySupports : RiskStage -> RiskStage -> Prop
  | .start, .finish => True
  | x, y => x = y

def toyRejects : RiskStage -> RiskStage -> Prop
  | .start, .finish => True
  | _, _ => False

theorem toySupports_refl : forall x, toySupports x x := by
  intro x
  cases x <;> decide

theorem toySupports_trans : forall {x y z},
    toySupports x y -> toySupports y z -> toySupports x z := by
  intro x y z
  cases x <;> cases y <;> cases z <;> decide

theorem toyRiskStep_supports : forall {p x y},
    toyRiskStep p x y -> toySupports x y := by
  intro p x y
  cases x <;> cases y <;> decide

def toyReciprocalRiskChain :
    ReciprocalRiskChain toyRiskStep RiskStage.start RiskStage.finish :=
  { rounds := 1
    increment := 1
    rounds_positive := by decide
    increment_positive := by decide
    closes_total_risk := by decide
    steps := ExactStepChain.succ (by trivial) (ExactStepChain.zero _) }

/-- The finite risky chain and the independent rejection yield a glut. -/
theorem toy_risky_comparison_is_glut :
    comparisonValue toySupports toyRejects
      RiskStage.start RiskStage.finish = FDEValue.B := by
  apply reciprocalRisk_axiological_glut
    toySupports_refl toySupports_trans toyRiskStep_supports
    toyReciprocalRiskChain
  trivial

/-- The same finite interpretation is non-trivial: an unrelated comparison
remains a gap rather than becoming supported. -/
theorem toy_unrelated_comparison_is_gap :
    comparisonValue toySupports toyRejects
      RiskStage.unrelated RiskStage.start = FDEValue.N := by
  decide

end PEL4.PopulationAxiology
