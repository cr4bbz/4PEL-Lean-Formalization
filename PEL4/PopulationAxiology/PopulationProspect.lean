import PEL4.ConvexProbabilitySimplex

namespace PEL4.PopulationAxiology

/-!
# Finite population prospects

This module separates three types that must not be conflated in the risky
population-axiology programme:

* a `Population Welfare` is a finite list of welfare levels;
* a `FiniteProspect Outcome` is a normalized rational distribution on a
  duplicate-free finite support of outcomes;
* a `PopulationProspect Welfare` is a finite prospect whose outcomes are
  populations.

The list representation is intentionally minimal. It does not yet quotient
populations by permutation, so anonymity remains a future semantic condition.
-/

universe u

/-- A finite population represented by the welfare level of each life. -/
abbrev Population (Welfare : Type u) := List Welfare

/-- A normalized finite rational prospect. -/
structure FiniteProspect (Outcome : Type u) [DecidableEq Outcome] where
  support : FiniteSet Outcome
  weight : Outcome -> Rat
  distribution : FiniteWeightDistribution support weight

/-- A prospect whose possible outcomes are finite populations. -/
abbrev PopulationProspect (Welfare : Type u) [DecidableEq Welfare] :=
  FiniteProspect (Population Welfare)

/-- A two-outcome prospect, convenient for stating the risky adequacy
conditions before quotienting or canonicalizing its support. -/
structure BinaryProspect (Outcome : Type u) where
  higherOutcome : Outcome
  lowerOutcome : Outcome
  lowerProbability : Rat

namespace BinaryProspect

/-- The elementary probability-integrity condition for a binary prospect. -/
def Valid {Outcome : Type u} (prospect : BinaryProspect Outcome) : Prop :=
  0 ≤ prospect.lowerProbability ∧ prospect.lowerProbability ≤ 1

/-- The probability of the higher outcome. -/
def higherProbability {Outcome : Type u}
    (prospect : BinaryProspect Outcome) : Rat :=
  1 - prospect.lowerProbability

end BinaryProspect

/-- Add `count` lives at one welfare level to a background population. -/
def addWelfareBlock {Welfare : Type u}
    (background : Population Welfare) (count : Nat) (level : Welfare) :
    Population Welfare :=
  background ++ List.replicate count level

/-- A binary population prospect in which one distinguished life is at
`upper` with probability `1-k` and at `lower` with probability `k`, while a
deterministic compensation block is added to the background population. -/
def riskShiftProspect {Welfare : Type u}
    (background : Population Welfare)
    (upper lower : Welfare)
    (compensationCount : Nat)
    (compensationLevel : Welfare)
    (k : Rat) : BinaryProspect (Population Welfare) :=
  { higherOutcome :=
      addWelfareBlock (background ++ [upper])
        compensationCount compensationLevel
    lowerOutcome :=
      addWelfareBlock (background ++ [lower])
        compensationCount compensationLevel
    lowerProbability := k }

/-- The probability coordinate of a risk-shift prospect is exactly the
specified risk of the lower outcome. -/
@[simp] theorem riskShiftProspect_lowerProbability
    {Welfare : Type u}
    (background : Population Welfare)
    (upper lower : Welfare)
    (compensationCount : Nat)
    (compensationLevel : Welfare)
    (k : Rat) :
    (riskShiftProspect background upper lower compensationCount
      compensationLevel k).lowerProbability = k :=
  rfl

end PEL4.PopulationAxiology
