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

/-- A finite population represented by the welfare level of each life. -/
abbrev Population (Welfare : Type) := List Welfare

/-- A normalized finite rational prospect. -/
structure FiniteProspect (Outcome : Type) [DecidableEq Outcome] where
  support : FiniteSet Outcome
  weight : Outcome -> Rat
  distribution : FiniteWeightDistribution support weight

/-- A prospect whose possible outcomes are finite populations. -/
abbrev PopulationProspect (Welfare : Type) [DecidableEq Welfare] :=
  FiniteProspect (Population Welfare)

/-- A two-outcome prospect, convenient for stating the risky adequacy
conditions before quotienting or canonicalizing its support. -/
structure BinaryProspect (Outcome : Type) where
  higherOutcome : Outcome
  lowerOutcome : Outcome
  lowerProbability : Rat

namespace BinaryProspect

/-- The elementary probability-integrity condition for a binary prospect. -/
def Valid {Outcome : Type} (prospect : BinaryProspect Outcome) : Prop :=
  0 ≤ prospect.lowerProbability ∧ prospect.lowerProbability ≤ 1

/-- The probability of the higher outcome. -/
def higherProbability {Outcome : Type}
    (prospect : BinaryProspect Outcome) : Rat :=
  1 - prospect.lowerProbability

end BinaryProspect

/-- Equality of binary population prospects up to permutation of lives in
each outcome, while preserving the probability coordinate. This is the
minimal anonymity relation needed before populations are represented by a
quotient or multiset. -/
def BinaryPopulationProspectEquivalent
    {Welfare : Type}
    (left right : BinaryProspect (Population Welfare)) : Prop :=
  List.Perm left.higherOutcome right.higherOutcome ∧
    List.Perm left.lowerOutcome right.lowerOutcome ∧
    left.lowerProbability = right.lowerProbability

theorem binaryPopulationProspectEquivalent_refl
    {Welfare : Type}
    (prospect : BinaryProspect (Population Welfare)) :
    BinaryPopulationProspectEquivalent prospect prospect :=
  ⟨List.Perm.refl _, List.Perm.refl _, rfl⟩

/-- Add `count` lives at one welfare level to a background population. -/
def addWelfareBlock {Welfare : Type}
    (background : Population Welfare) (count : Nat) (level : Welfare) :
    Population Welfare :=
  background ++ List.replicate count level

/-- A binary population prospect in which one distinguished life is at
`upper` with probability `1-k` and at `lower` with probability `k`, while a
deterministic compensation block is added to the background population. -/
def riskShiftProspect {Welfare : Type}
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
    {Welfare : Type}
    (background : Population Welfare)
    (upper lower : Welfare)
    (compensationCount : Nat)
    (compensationLevel : Welfare)
    (k : Rat) :
    (riskShiftProspect background upper lower compensationCount
      compensationLevel k).lowerProbability = k :=
  rfl

/-- A risk-shift prospect is valid whenever its lower-outcome probability is
in the rational unit interval. -/
theorem riskShiftProspect_valid
    {Welfare : Type}
    (background : Population Welfare)
    (upper lower : Welfare)
    (compensationCount : Nat)
    (compensationLevel : Welfare)
    (k : Rat)
    (hk0 : 0 ≤ k)
    (hk1 : k ≤ 1) :
    BinaryProspect.Valid
      (riskShiftProspect background upper lower compensationCount
        compensationLevel k) :=
  ⟨hk0, hk1⟩

/-- If `k` lies in `[0, 1-p]` and `p` is nonnegative, both the original
prospect and the prospect after one risk increment are probability-valid. -/
theorem riskShiftProspect_pair_valid
    {Welfare : Type}
    (background : Population Welfare)
    (upper lower : Welfare)
    (compensationCount : Nat)
    (leftCompensation rightCompensation : Welfare)
    (k p : Rat)
    (hk0 : 0 ≤ k)
    (hkp : k ≤ 1 - p)
    (hp0 : 0 ≤ p) :
    BinaryProspect.Valid
        (riskShiftProspect background upper lower compensationCount
          leftCompensation k) ∧
      BinaryProspect.Valid
        (riskShiftProspect background upper lower compensationCount
          rightCompensation (k + p)) := by
  have hk_le_kp : k ≤ k + p := by
    have h := (Rat.add_le_add_left (a := 0) (b := p) (c := k)).2 hp0
    simpa only [Rat.add_zero] using h
  have hkp1 : k + p ≤ 1 := by
    have h := (Rat.add_le_add_right
      (a := k) (b := 1 - p) (c := p)).2 hkp
    simpa only [Rat.sub_add_cancel] using h
  constructor
  · exact riskShiftProspect_valid background upper lower compensationCount
      leftCompensation k hk0 (Rat.le_trans hk_le_kp hkp1)
  · exact riskShiftProspect_valid background upper lower compensationCount
      rightCompensation (k + p) (Rat.add_nonneg hk0 hp0) hkp1

end PEL4.PopulationAxiology
