import PEL4.ModalDynamicsPhaseClassification

namespace PEL4

/-!
# Complete dynamic reachability of four-valued knowledge

The preceding dynamic modules establish that admissible conditionalization can
fracture and restore the stability gate of evidence-stable knowledge. This
module asks a stronger reachability question:

  which complete FDE values of K(B p) can be transformed into which others
  while accessibility and atomic valuation remain fixed across the update?

A six-world construction realizes every ordered pair of FDE values.

For arbitrary source and target values:

* one distinguished `focus` world carries `p = target` and is the only world
  positively satisfying the update evidence `e`;
* four anchor worlds carry `p = source`;
* one spare world carries `p = N`;
* the prior is uniform and the threshold is 2/3.

Before update the four source anchors force B(p) to have exactly the source
status, independently of the target at `focus`. After conditioning on `e`, all
posterior probability is concentrated on `focus`, so B(p) has exactly the
target status. The local measure is source-world independent, hence the B(p)
profile is homogeneous across the common accessibility range both before and
after update. Outer evidence-stable K therefore transmits the same transition.

Thus all 4 x 4 = 16 transitions are reachable by probability change alone.
-/

inductive DynamicReachabilityWorld where
  | focus | a1 | a2 | a3 | a4 | spare
deriving DecidableEq, Repr

inductive DynamicReachabilityAgent where
  | i
deriving DecidableEq, Repr

inductive DynamicReachabilityAtom where
  | p | e
deriving DecidableEq, Repr

/-- Four source anchors, one neutral spare world, and one target/evidence world. -/
def dynamicReachabilityVal (source target : FDEValue) :
    DynamicReachabilityWorld → DynamicReachabilityAtom → FDEValue
  | DynamicReachabilityWorld.focus, DynamicReachabilityAtom.p => target
  | DynamicReachabilityWorld.a1, DynamicReachabilityAtom.p => source
  | DynamicReachabilityWorld.a2, DynamicReachabilityAtom.p => source
  | DynamicReachabilityWorld.a3, DynamicReachabilityAtom.p => source
  | DynamicReachabilityWorld.a4, DynamicReachabilityAtom.p => source
  | DynamicReachabilityWorld.spare, DynamicReachabilityAtom.p => FDEValue.N
  | DynamicReachabilityWorld.focus, DynamicReachabilityAtom.e => FDEValue.T
  | _, DynamicReachabilityAtom.e => FDEValue.F

/-- Uniform prior over six worlds. -/
def dynamicReachabilityMu
    (S : FiniteSet DynamicReachabilityWorld) : Rat :=
  let q : Rat := 1 / 6
  let pf := if S.contains DynamicReachabilityWorld.focus then q else 0
  let p1 := if S.contains DynamicReachabilityWorld.a1 then q else 0
  let p2 := if S.contains DynamicReachabilityWorld.a2 then q else 0
  let p3 := if S.contains DynamicReachabilityWorld.a3 then q else 0
  let p4 := if S.contains DynamicReachabilityWorld.a4 then q else 0
  let ps := if S.contains DynamicReachabilityWorld.spare then q else 0
  pf + p1 + p2 + p3 + p4 + ps

/-- Six-world family parameterized only by desired source and target FDE values. -/
def DynamicReachabilityModel (source target : FDEValue) :
    Model DynamicReachabilityWorld DynamicReachabilityAgent
      DynamicReachabilityAtom :=
  { worlds := [DynamicReachabilityWorld.focus,
      DynamicReachabilityWorld.a1,
      DynamicReachabilityWorld.a2,
      DynamicReachabilityWorld.a3,
      DynamicReachabilityWorld.a4,
      DynamicReachabilityWorld.spare]
  , R := fun _ _ => [DynamicReachabilityWorld.focus,
      DynamicReachabilityWorld.a1,
      DynamicReachabilityWorld.a2,
      DynamicReachabilityWorld.a3,
      DynamicReachabilityWorld.a4,
      DynamicReachabilityWorld.spare]
  , mu := fun _ _ => dynamicReachabilityMu
  , val := dynamicReachabilityVal source target
  , c := fun _ => 2 / 3
  , mu_total := by
      intro ag w
      cases ag
      native_decide
  , mu_empty := by
      intro ag w
      cases ag
      native_decide
  , c_gt_half := by
      intro ag
      cases ag
      native_decide
  , c_le_one := by
      intro ag
      cases ag
      native_decide
  }

/-- Update evidence selects exactly the target-bearing focus world. -/
def dynamicReachabilityEvidence :
    Formula DynamicReachabilityAtom DynamicReachabilityAgent :=
  Formula.prop DynamicReachabilityAtom.e

/-- The evidence event has prior mass 1/6 everywhere, so conditionalization is
admissible for every source/target pair. -/
theorem dynamic_reachability_evidence_admissible
    (source target : FDEValue) :
    ConditionalizationAdmissible
      (DynamicReachabilityModel source target)
      dynamicReachabilityEvidence := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;>
    constructor <;>
      intro ag w <;>
      cases ag <;>
      cases w <;>
      native_decide

/-- Posterior model: only the probability measure changes. -/
def DynamicReachabilityUpdated (source target : FDEValue) :
    Model DynamicReachabilityWorld DynamicReachabilityAgent
      DynamicReachabilityAtom :=
  conditionalize
    (DynamicReachabilityModel source target)
    dynamicReachabilityEvidence
    (dynamic_reachability_evidence_admissible source target)

/-- Atomic target and its probability-sensitive belief layer. -/
def dynamicReachabilityP :
    ModalFormula DynamicReachabilityAtom DynamicReachabilityAgent :=
  ModalFormula.prop DynamicReachabilityAtom.p

def dynamicReachabilityBelP :
    ModalFormula DynamicReachabilityAtom DynamicReachabilityAgent :=
  ModalFormula.bel DynamicReachabilityAgent.i dynamicReachabilityP

/-- Outer evidence-stable knowledge of the probabilistic belief state. -/
def dynamicReachabilityKBelP :
    ModalFormula DynamicReachabilityAtom DynamicReachabilityAgent :=
  ModalFormula.know DynamicReachabilityAgent.i dynamicReachabilityBelP

/-- The update keeps accessibility literally unchanged. -/
theorem dynamic_reachability_accessibility_fixed
    (source target : FDEValue)
    (w : DynamicReachabilityWorld) :
    (DynamicReachabilityUpdated source target).R
        DynamicReachabilityAgent.i w =
      (DynamicReachabilityModel source target).R
        DynamicReachabilityAgent.i w := by
  rfl

/-- The update also keeps the complete atomic valuation literally unchanged. -/
theorem dynamic_reachability_valuation_fixed
    (source target : FDEValue)
    (w : DynamicReachabilityWorld)
    (atom : DynamicReachabilityAtom) :
    (DynamicReachabilityUpdated source target).val w atom =
      (DynamicReachabilityModel source target).val w atom := by
  rfl

/-- Before update, probabilistic belief in `p` equals the chosen source value at
every world. Four source anchors dominate the 2/3 threshold, while the single
target world cannot change either threshold bit. -/
theorem dynamic_reachability_belief_before
    (source target : FDEValue)
    (w : DynamicReachabilityWorld) :
    evalModal (DynamicReachabilityModel source target) w
        dynamicReachabilityBelP = source := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;>
    cases w <;> native_decide

/-- After conditioning, all mass lies on `focus`, whose complete value is the
chosen target. Threshold belief therefore reproduces the target exactly. -/
theorem dynamic_reachability_belief_after
    (source target : FDEValue)
    (w : DynamicReachabilityWorld) :
    evalModal (DynamicReachabilityUpdated source target) w
        dynamicReachabilityBelP = target := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;>
    cases w <;> native_decide

/-- The belief profile is homogeneous before update. -/
theorem dynamic_reachability_stable_before
    (source target : FDEValue) :
    ModalStableAt (DynamicReachabilityModel source target)
        DynamicReachabilityAgent.i DynamicReachabilityWorld.focus
        dynamicReachabilityBelP = true := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;> native_decide

/-- The belief profile is homogeneous after update as well. -/
theorem dynamic_reachability_stable_after
    (source target : FDEValue) :
    ModalStableAt (DynamicReachabilityUpdated source target)
        DynamicReachabilityAgent.i DynamicReachabilityWorld.focus
        dynamicReachabilityBelP = true := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;> native_decide

/-- Outer knowledge therefore equals the arbitrary chosen source before update. -/
theorem dynamic_reachability_knowledge_before
    (source target : FDEValue) :
    evalModal (DynamicReachabilityModel source target)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = source := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;> native_decide

/-- And it equals the arbitrary chosen target after update. -/
theorem dynamic_reachability_knowledge_after
    (source target : FDEValue) :
    evalModal (DynamicReachabilityUpdated source target)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = target := by
  rcases source with ⟨sp, sn⟩
  rcases target with ⟨tp, tn⟩
  cases sp <;> cases sn <;> cases tp <;> cases tn <;> native_decide

/-- Complete four-valued dynamic reachability.

For every ordered pair of FDE values, there is a member of this fixed six-world
model family in which admissible conditionalization changes only probability
and sends `K(B p)` from the first value to the second. Since an FDE value has
two Boolean coordinates, this single theorem covers all 16 transitions. -/
theorem conditionalization_realizes_every_knowledge_value_transition
    (source target : FDEValue) :
    evalModal (DynamicReachabilityModel source target)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = source ∧
    evalModal (DynamicReachabilityUpdated source target)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = target := by
  exact ⟨dynamic_reachability_knowledge_before source target,
    dynamic_reachability_knowledge_after source target⟩

/-- In particular, conditionalization can create glutty knowledge. -/
theorem conditionalization_can_create_knowledge_glut :
    evalModal (DynamicReachabilityModel FDEValue.T FDEValue.B)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.T ∧
    evalModal (DynamicReachabilityUpdated FDEValue.T FDEValue.B)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.B := by
  exact conditionalization_realizes_every_knowledge_value_transition
    FDEValue.T FDEValue.B

/-- It can remove a glut and create a gap. -/
theorem conditionalization_can_turn_knowledge_glut_into_gap :
    evalModal (DynamicReachabilityModel FDEValue.B FDEValue.N)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.B ∧
    evalModal (DynamicReachabilityUpdated FDEValue.B FDEValue.N)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.N := by
  exact conditionalization_realizes_every_knowledge_value_transition
    FDEValue.B FDEValue.N

/-- And it can restore strict truth from a gap. -/
theorem conditionalization_can_turn_knowledge_gap_into_truth :
    evalModal (DynamicReachabilityModel FDEValue.N FDEValue.T)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.N ∧
    evalModal (DynamicReachabilityUpdated FDEValue.N FDEValue.T)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP = FDEValue.T := by
  exact conditionalization_realizes_every_knowledge_value_transition
    FDEValue.N FDEValue.T

/-!
## Interpretation

The dynamic K/B picture is maximally permissive at the level of complete FDE
status once a probability-sensitive belief layer is available:

```text
        T   F   B   N
      +---------------
T     | x   x   x   x
F     | x   x   x   x
B     | x   x   x   x
N     | x   x   x   x
```

Every arrow is realized by safe conditionalization while `R`, atomic valuation,
and threshold remain fixed across the update. The probability distribution is
the only model field that changes.

This answers two open dynamic questions at once:

* the reachability graph of K(B p) over T/F/B/N is complete;
* conditionalization can both create and remove knowledge-level gluts and gaps.

The result does not say that every fixed concrete model admits every transition.
It says that no ordered pair of four-valued knowledge statuses is forbidden by
the semantics of admissible probabilistic conditionalization itself.

Working name: **Complete Dynamic Epistemic Reachability**.
-/

end PEL4
