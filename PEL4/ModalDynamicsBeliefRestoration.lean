import PEL4.ModalDynamicsBeliefInstability

namespace PEL4

/-!
# Belief-mediated dynamic stability restoration

The preceding dynamic witness showed that admissible conditionalization can
fracture a homogeneous belief profile and thereby turn outer knowledge from
`T` to `F`.  This module tests the converse direction.

The accessibility relation and valuation again remain fixed.  Before update,
local probability measures make `B p` take the profile `T/N/T` across three
mutually accessible worlds.  Conditioning on positive evidence concentrated on
the two `p`-worlds makes the posterior belief profile homogeneous `T/T/T`.
If the finite calculations compile, conditionalization can therefore restore
full-value stability and move outer evidence-stable knowledge from `F` to `T`.
-/

/-- Prior at worlds `a` and `c`: weights `(4/10,2/10,4/10)`.  Thus `p` has
probability `4/5`, above the `2/3` threshold. -/
def dynamicRestorationMuAC
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  let pa := if S.contains DynamicInstabilityWorld.a then (4 : Rat) / 10 else 0
  let pb := if S.contains DynamicInstabilityWorld.b then (2 : Rat) / 10 else 0
  let pc := if S.contains DynamicInstabilityWorld.c then (4 : Rat) / 10 else 0
  pa + pb + pc

/-- Prior at world `b`: weights `(3/10,4/10,3/10)`.  Here `p` has probability
`3/5` and `not p` probability `2/5`, so threshold belief in `p` is `N`. -/
def dynamicRestorationMuB
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  let pa := if S.contains DynamicInstabilityWorld.a then (3 : Rat) / 10 else 0
  let pb := if S.contains DynamicInstabilityWorld.b then (4 : Rat) / 10 else 0
  let pc := if S.contains DynamicInstabilityWorld.c then (3 : Rat) / 10 else 0
  pa + pb + pc

def dynamicRestorationMu
    (w : DynamicInstabilityWorld)
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  match w with
  | DynamicInstabilityWorld.a => dynamicRestorationMuAC S
  | DynamicInstabilityWorld.b => dynamicRestorationMuB S
  | DynamicInstabilityWorld.c => dynamicRestorationMuAC S

/-- Same worlds, accessibility, valuation, and threshold as the fracture
witness; only the source-indexed prior probabilities differ. -/
def DynamicRestorationModel :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  { worlds := [DynamicInstabilityWorld.a,
      DynamicInstabilityWorld.b,
      DynamicInstabilityWorld.c]
  , R := fun _ _ => [DynamicInstabilityWorld.a,
      DynamicInstabilityWorld.b,
      DynamicInstabilityWorld.c]
  , mu := fun _ w => dynamicRestorationMu w
  , val := dynamicInstabilityVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro ag w
      cases ag
      cases w <;> native_decide
  , mu_empty := by
      intro ag w
      cases ag
      cases w <;> native_decide
  , c_gt_half := by
      intro ag
      cases ag
      native_decide
  , c_le_one := by
      intro ag
      cases ag
      native_decide
  }

/-- Evidence `e` selects worlds `a,c`.  Its prior mass is `4/5` at `a,c` and
`3/5` at `b`, so conditioning is admissible everywhere. -/
theorem dynamic_restoration_evidence_admissible :
    ConditionalizationAdmissible
      DynamicRestorationModel dynamicInstabilityEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> native_decide
  · intro ag w
    cases ag
    cases w <;> native_decide
  · intro ag w
    cases ag
    cases w <;> native_decide

/-- Posterior model after learning `e`. -/
def DynamicRestorationUpdated :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize DynamicRestorationModel dynamicInstabilityEvidence
    dynamic_restoration_evidence_admissible

/-- Before update the belief profile is heterogeneous `T/N/T`. -/
theorem dynamic_restoration_belief_profile_before :
    evalModal DynamicRestorationModel DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicRestorationModel DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.N ∧
    evalModal DynamicRestorationModel DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  native_decide

/-- Hence `B p` is unstable before the update. -/
theorem dynamic_restoration_unstable_before :
    modalAccessibleValueStable
        (DynamicRestorationModel.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicRestorationModel u dynamicInstabilityBelP) =
      false := by
  native_decide

/-- Conditioning on `e` removes the local threshold difference: `B p` becomes
`T` at all three worlds. -/
theorem dynamic_restoration_belief_profile_after :
    evalModal DynamicRestorationUpdated DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicRestorationUpdated DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicRestorationUpdated DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  native_decide

/-- The posterior belief profile is therefore full-value stable. -/
theorem dynamic_restoration_stable_after :
    modalAccessibleValueStable
        (DynamicRestorationUpdated.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicRestorationUpdated u dynamicInstabilityBelP) =
      true := by
  native_decide

/-- Outer knowledge rejects the heterogeneous prior belief profile. -/
theorem dynamic_restoration_outer_knowledge_false_before :
    evalModal DynamicRestorationModel DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.F := by
  native_decide

/-- Once conditionalization restores a homogeneous `T/T/T` belief profile,
outer knowledge recovers strict `T`. -/
theorem dynamic_restoration_outer_knowledge_true_after :
    evalModal DynamicRestorationUpdated DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.T := by
  native_decide

/-- Complete dynamic restoration: admissible conditionalization changes
`T/N/T` into `T/T/T`, flips stability from false to true, and moves outer
knowledge from strict `F` to strict `T`. -/
theorem conditionalization_can_restore_belief_mediated_stability :
    modalAccessibleValueStable
        (DynamicRestorationModel.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicRestorationModel u dynamicInstabilityBelP) =
      false ∧
    modalAccessibleValueStable
        (DynamicRestorationUpdated.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicRestorationUpdated u dynamicInstabilityBelP) =
      true ∧
    evalModal DynamicRestorationModel DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.F ∧
    evalModal DynamicRestorationUpdated DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.T := by
  native_decide

/-!
## Interpretation

Together with the fracture witness, this candidate would show that probabilistic
conditionalization can move epistemic stability in both directions:

```text
fracture:    T/T/T -> T/N/T -> K(B p): T -> F
restoration: T/N/T -> T/T/T -> K(B p): F -> T
```

The update does not alter `R` or atomic valuation.  The phase change is mediated
entirely by source-dependent posterior threshold belief and then amplified by
the qualitative stability gate of `K`.

Working diagnosis: **Belief-Mediated Stability Restoration**.  If both gates are
verified, conditionalization behaves as a genuine epistemic stability-phase
operator rather than as a monotone knowledge gain or loss operation.
-/

end PEL4
