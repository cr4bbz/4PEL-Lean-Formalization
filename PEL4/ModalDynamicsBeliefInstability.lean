import PEL4.ModalDynamicsStability

namespace PEL4

/-!
# Belief-mediated dynamic instability

The preceding dynamic-stability theorem showed that admissible probabilistic
conditionalization preserves every modal formula that contains no `bel`
subformula.  This module supplies the complementary finite witness.

The update changes only local probability measures, but those measures may be
world-dependent.  A probabilistic belief formula can therefore remain `T` at
one accessible world while dropping to `N` at another.  Once this happens, the
complete accessible profile of that belief formula becomes heterogeneous and
outer evidence-stable knowledge collapses to strict `F`.

This is the first explicit dynamic witness that conditionalization can create
knowledge-relevant instability through an embedded belief operator while the
belief-free modal fragment remains invariant.
-/

inductive DynamicInstabilityWorld where
  | a | b | c
deriving DecidableEq, Repr

inductive DynamicInstabilityAgent where
  | i
deriving DecidableEq, Repr

inductive DynamicInstabilityAtom where
  | p | e
deriving DecidableEq, Repr

/-- `p` is true at `a,c` and false at `b`; update evidence `e` is true at
`a,b` and false at `c`. -/
def dynamicInstabilityVal :
    DynamicInstabilityWorld → DynamicInstabilityAtom → FDEValue
  | DynamicInstabilityWorld.a, DynamicInstabilityAtom.p => FDEValue.T
  | DynamicInstabilityWorld.b, DynamicInstabilityAtom.p => FDEValue.F
  | DynamicInstabilityWorld.c, DynamicInstabilityAtom.p => FDEValue.T
  | DynamicInstabilityWorld.a, DynamicInstabilityAtom.e => FDEValue.T
  | DynamicInstabilityWorld.b, DynamicInstabilityAtom.e => FDEValue.T
  | DynamicInstabilityWorld.c, DynamicInstabilityAtom.e => FDEValue.F

/-- Local prior at worlds `a` and `c`: weights `(7/10,1/10,2/10)`. -/
def dynamicInstabilityMuAC
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  let pa := if S.contains DynamicInstabilityWorld.a then (7 : Rat) / 10 else 0
  let pb := if S.contains DynamicInstabilityWorld.b then (1 : Rat) / 10 else 0
  let pc := if S.contains DynamicInstabilityWorld.c then (2 : Rat) / 10 else 0
  pa + pb + pc

/-- Local prior at world `b`: weights `(2/10,2/10,6/10)`. -/
def dynamicInstabilityMuB
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  let pa := if S.contains DynamicInstabilityWorld.a then (2 : Rat) / 10 else 0
  let pb := if S.contains DynamicInstabilityWorld.b then (2 : Rat) / 10 else 0
  let pc := if S.contains DynamicInstabilityWorld.c then (6 : Rat) / 10 else 0
  pa + pb + pc

/-- Source-world dependent local probability measure. -/
def dynamicInstabilityMu
    (w : DynamicInstabilityWorld)
    (S : FiniteSet DynamicInstabilityWorld) : Rat :=
  match w with
  | DynamicInstabilityWorld.a => dynamicInstabilityMuAC S
  | DynamicInstabilityWorld.b => dynamicInstabilityMuB S
  | DynamicInstabilityWorld.c => dynamicInstabilityMuAC S

/-- All three worlds are mutually epistemically accessible. -/
def DynamicInstabilityModel :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  { worlds := [DynamicInstabilityWorld.a,
      DynamicInstabilityWorld.b,
      DynamicInstabilityWorld.c]
  , R := fun _ _ => [DynamicInstabilityWorld.a,
      DynamicInstabilityWorld.b,
      DynamicInstabilityWorld.c]
  , mu := fun _ w => dynamicInstabilityMu w
  , val := dynamicInstabilityVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro i w
      cases i
      cases w <;> native_decide
  , mu_empty := by
      intro i w
      cases i
      cases w <;> native_decide
  , c_gt_half := by
      intro i
      cases i
      native_decide
  , c_le_one := by
      intro i
      cases i
      native_decide
  }

/-- Legacy evidence used for conditionalization. -/
def dynamicInstabilityEvidence :
    Formula DynamicInstabilityAtom DynamicInstabilityAgent :=
  Formula.prop DynamicInstabilityAtom.e

/-- The evidence event has mass `4/5` at `a,c` and `2/5` at `b`, so the update
is admissible at every local state. -/
theorem dynamic_instability_evidence_admissible :
    ConditionalizationAdmissible
      DynamicInstabilityModel dynamicInstabilityEvidence := by
  constructor
  · intro i w
    cases i
    cases w <;> native_decide
  · intro i w
    cases i
    cases w <;> native_decide
  · intro i w
    cases i
    cases w <;> native_decide

/-- Updated model after learning `e`. -/
def DynamicInstabilityUpdated :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize DynamicInstabilityModel dynamicInstabilityEvidence
    dynamic_instability_evidence_admissible

def dynamicInstabilityP :
    ModalFormula DynamicInstabilityAtom DynamicInstabilityAgent :=
  ModalFormula.prop DynamicInstabilityAtom.p

/-- The probability-sensitive target formula. -/
def dynamicInstabilityBelP :
    ModalFormula DynamicInstabilityAtom DynamicInstabilityAgent :=
  ModalFormula.bel DynamicInstabilityAgent.i dynamicInstabilityP

/-- The witness genuinely lies outside the probability-free fragment. -/
theorem dynamic_instability_belP_not_probabilityFree :
    ¬ ModalProbabilityFree dynamicInstabilityBelP := by
  intro h
  cases h

/-- Before update, `B p = T` at every accessible world. -/
theorem dynamic_instability_belief_profile_before :
    evalModal DynamicInstabilityModel DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicInstabilityModel DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicInstabilityModel DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  native_decide

/-- Hence the accessible profile of `B p` is stable before update. -/
theorem dynamic_instability_stable_before :
    modalAccessibleValueStable
        (DynamicInstabilityModel.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicInstabilityModel u dynamicInstabilityBelP) =
      true := by
  native_decide

/-- After conditioning on `e`, the local posterior belief values split:
`T` at `a,c`, but `N` at `b`. -/
theorem dynamic_instability_belief_profile_after :
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.N ∧
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  native_decide

/-- The update therefore creates complete-value instability in `B p`. -/
theorem dynamic_instability_unstable_after :
    modalAccessibleValueStable
        (DynamicInstabilityUpdated.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicInstabilityUpdated u dynamicInstabilityBelP) =
      false := by
  native_decide

/-- Before update, outer knowledge of the homogeneous belief profile is strict
`T`. -/
theorem dynamic_instability_outer_knowledge_true_before :
    evalModal DynamicInstabilityModel DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.T := by
  native_decide

/-- After update, the newly heterogeneous belief profile forces outer knowledge
to strict `F`. -/
theorem dynamic_instability_outer_knowledge_false_after :
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.F := by
  native_decide

/-- Complete dynamic fracture: admissible conditionalization turns a stable
`T/T/T` belief profile into `T/N/T`, and outer knowledge flips from `T` to `F`. -/
theorem conditionalization_can_create_belief_mediated_instability :
    modalAccessibleValueStable
        (DynamicInstabilityModel.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicInstabilityModel u dynamicInstabilityBelP) =
      true ∧
    modalAccessibleValueStable
        (DynamicInstabilityUpdated.R DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a)
        (fun u => evalModal DynamicInstabilityUpdated u dynamicInstabilityBelP) =
      false ∧
    evalModal DynamicInstabilityModel DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.T ∧
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityBelP) =
      FDEValue.F := by
  native_decide

/-- Contrast: atomic `p`, which is probability-free, has invariant outer
knowledge under the same update. -/
theorem dynamic_instability_atomic_knowledge_is_invariant :
    evalModal DynamicInstabilityUpdated DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityP) =
      evalModal DynamicInstabilityModel DynamicInstabilityWorld.a
        (ModalFormula.know DynamicInstabilityAgent.i dynamicInstabilityP) := by
  exact modal_knowledge_conditionalize_of_probabilityFree
    DynamicInstabilityModel dynamicInstabilityEvidence
    dynamic_instability_evidence_admissible
    DynamicInstabilityAgent.i DynamicInstabilityWorld.a
    (ModalProbabilityFree.prop DynamicInstabilityAtom.p)

/-!
## Interpretation

The dynamic boundary is now two-sided.

For the probability-free modal fragment:

```text
conditionalization preserves complete value and stability.
```

But once a `bel` subformula is present, source-dependent posterior measures can
make the same belief formula take different complete FDE values at different
accessible worlds.  In this witness:

```text
before:  B p = T, T, T   -> stable  -> K(B p) = T
after:   B p = T, N, T   -> unstable -> K(B p) = F
```

So probabilistic update does not alter evidence-stable knowledge directly.
Instead it can inject heterogeneity through the belief layer, after which the
qualitative stability filter of `K` converts that heterogeneity into strict
failure.

Working diagnosis: **Belief-Mediated Stability Fracture** or
**Probabilistic Instability Injection**.
-/

end PEL4
