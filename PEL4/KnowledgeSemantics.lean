import PEL4.Syntax

namespace PEL4

/-!
# Knowledge semantics comparison gate

This module still does not extend the object language with a primitive
four-valued knowledge operator `K`. Instead it develops and tests an
*evidence-stable* four-valued knowledge semantics on the existing finite 4-PEL
model structure.

The positive component follows the non-standard Belnap-Dunn knowledge idea:

  * `phi` has positive support at every accessible world, and
  * `phi` has the same complete FDE value throughout the accessible range.

The negative component records either

  * accessible negative support for `phi`, or
  * instability of the complete FDE value across accessible worlds.

Thus epistemic heterogeneity itself counts against knowledge. This reproduces
the qualitative behaviour motivating the non-standard knowledge modality in
the Belnap-Dunn literature while keeping the present 4-PEL object language
unchanged until the semantic gate is understood.
-/

/-- Standard positive `Box` condition: positive support at every accessible
world. -/
def standardBoxPositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (m.R i w).all (fun w' => (eval m w' phi).pos)

/-- Standard negative support condition used by the knowledge candidate:
negative support occurs at at least one accessible world. -/
def standardBoxNegative {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (m.R i w).any (fun w' => (eval m w' phi).neg)

/-- The complete FDE value of `phi` is stable over the accessible range.
The empty and singleton ranges are vacuously stable. -/
def accessibleFDEValueStable {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  match m.R i w with
  | [] => true
  | first :: rest =>
      rest.all (fun w' => decide (eval m w' phi = eval m first phi))

/-- Positive component of evidence-stable knowledge: universal positive support
plus stability of the full Belnapian value. -/
def evidenceStableKnowledgePositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  standardBoxPositive m i w phi && accessibleFDEValueStable m i w phi

/-- Negative component of evidence-stable knowledge: either some accessible
world negatively supports `phi`, or the full FDE status is not stable across
the accessible range.

The second disjunct is essential. A `T/N` variation, for example, contains no
negative support at either world but still represents failure of stable
knowledge. -/
def evidenceStableKnowledgeNegative {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (!accessibleFDEValueStable m i w phi) || standardBoxNegative m i w phi

/-- Full four-valued semantic value of the evidence-stable knowledge
candidate. -/
def evidenceStableKnowledgeValue {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : FDEValue :=
  { pos := evidenceStableKnowledgePositive m i w phi
  , neg := evidenceStableKnowledgeNegative m i w phi
  }

/-- Evidence-stable positive knowledge is at least as strong as the ordinary
positive modal-box condition. -/
theorem evidence_stable_knowledge_implies_standard_box
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (h : evidenceStableKnowledgePositive m i w phi = true) :
    standardBoxPositive m i w phi = true := by
  cases hbox : standardBoxPositive m i w phi <;>
    simp_all [evidenceStableKnowledgePositive]

/-- Instability of the complete accessible FDE status forces the knowledge
candidate to the strict false value `F`: positive knowledge fails and negative
knowledge support is present. -/
theorem knowledge_instability_forces_false
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (h : accessibleFDEValueStable m i w phi = false) :
    evidenceStableKnowledgeValue m i w phi = FDEValue.F := by
  simp [evidenceStableKnowledgeValue, evidenceStableKnowledgePositive,
    evidenceStableKnowledgeNegative, h]

/-!
## A finite contrast model

At both accessible worlds, `p` has positive support, so the standard FDE-style
box condition accepts it. But the complete values differ (`T` versus `B`), so
the evidence-stable knowledge condition rejects it. The full knowledge value is
therefore `F` by the instability theorem above.
-/

inductive KnowledgeGateAtom where
  | p
deriving DecidableEq, Repr

inductive KnowledgeGateAgent where
  | a
deriving DecidableEq, Repr

inductive KnowledgeGateWorld where
  | root | left | right
deriving DecidableEq, Repr

/-- Accessible evidence sources carry `T` and `B` respectively. -/
def knowledgeGateVal : KnowledgeGateWorld → KnowledgeGateAtom → FDEValue
| KnowledgeGateWorld.root, _ => FDEValue.T
| KnowledgeGateWorld.left, _ => FDEValue.T
| KnowledgeGateWorld.right, _ => FDEValue.B

/-- Uniform probability over the two accessible evidence worlds. Probability
is irrelevant to the knowledge predicates but is supplied so the example is an
ordinary 4-PEL `Model`. -/
def knowledgeGateMu : FiniteSet KnowledgeGateWorld → Rat
| S =>
  let pl := if S.contains KnowledgeGateWorld.left then (1 : Rat) / 2 else 0
  let pr := if S.contains KnowledgeGateWorld.right then (1 : Rat) / 2 else 0
  pl + pr

/-- Contrast model used to separate ordinary positive `Box` from
Belnapian-value-stable knowledge. -/
def KnowledgeGateModel :
    Model KnowledgeGateWorld KnowledgeGateAgent KnowledgeGateAtom :=
  { worlds := [KnowledgeGateWorld.root,
      KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , R := fun _ _ => [KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , mu := fun _ _ => knowledgeGateMu
  , val := knowledgeGateVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro _ _
      native_decide
  , mu_empty := by
      intro _ _
      native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }

/-- Test proposition for the contrast model. -/
def knowledgeGateP : Formula KnowledgeGateAtom KnowledgeGateAgent :=
  Formula.prop KnowledgeGateAtom.p

#eval! standardBoxPositive KnowledgeGateModel KnowledgeGateAgent.a
  KnowledgeGateWorld.root knowledgeGateP
#eval! accessibleFDEValueStable KnowledgeGateModel KnowledgeGateAgent.a
  KnowledgeGateWorld.root knowledgeGateP
#eval! evidenceStableKnowledgeValue KnowledgeGateModel KnowledgeGateAgent.a
  KnowledgeGateWorld.root knowledgeGateP

/-- The standard positive box condition accepts `p` because both accessible
worlds positively support it. -/
theorem knowledge_gate_standard_box_accepts :
    standardBoxPositive KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = true := by
  native_decide

/-- The full FDE value is not stable: the accessible values are `T` and `B`. -/
theorem knowledge_gate_value_not_stable :
    accessibleFDEValueStable KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = false := by
  native_decide

/-- Consequently, the evidence-stable knowledge candidate is strictly false in
the same model in which ordinary positive `Box` succeeds. -/
theorem standard_box_can_hold_while_stable_knowledge_is_false :
    standardBoxPositive KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = true ∧
    evidenceStableKnowledgeValue KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = FDEValue.F := by
  native_decide

/-!
## Homogeneous recovery model

A second family of models assigns the same arbitrary FDE value `v` to both
accessible evidence worlds. The evidence-stable knowledge candidate should then
recover that complete value exactly. This tests all four homogeneous epistemic
regimes with one parameterized theorem.
-/

/-- Two accessible worlds with the same supplied FDE value. -/
def HomogeneousKnowledgeModel (v : FDEValue) :
    Model KnowledgeGateWorld KnowledgeGateAgent KnowledgeGateAtom :=
  { worlds := [KnowledgeGateWorld.root,
      KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , R := fun _ _ => [KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , mu := fun _ _ => knowledgeGateMu
  , val := fun _ _ => v
  , c := fun _ => 2 / 3
  , mu_total := by
      intro _ _
      native_decide
  , mu_empty := by
      intro _ _
      native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }

/-- Knowledge Stability Principle for the finite homogeneous gate: when every
accessible world gives `phi` the same FDE value, evidence-stable knowledge
recovers that value exactly. -/
theorem homogeneous_knowledge_recovers_fde_value (v : FDEValue) :
    evidenceStableKnowledgeValue (HomogeneousKnowledgeModel v)
      KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = v := by
  rcases v with ⟨pos, neg⟩
  cases pos <;> cases neg <;> native_decide

/-- Explicit four-value sanity check. -/
theorem homogeneous_knowledge_four_values :
    evidenceStableKnowledgeValue (HomogeneousKnowledgeModel FDEValue.T)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.T ∧
    evidenceStableKnowledgeValue (HomogeneousKnowledgeModel FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.F ∧
    evidenceStableKnowledgeValue (HomogeneousKnowledgeModel FDEValue.B)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.B ∧
    evidenceStableKnowledgeValue (HomogeneousKnowledgeModel FDEValue.N)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.N := by
  native_decide

/-!
## Interpretation

The candidate has a simple finite behaviour:

* homogeneous accessible status `T` gives knowledge value `T`;
* homogeneous accessible status `F` gives knowledge value `F`;
* homogeneous accessible status `B` gives knowledge value `B`;
* homogeneous accessible status `N` gives knowledge value `N`;
* heterogeneous accessible FDE status gives knowledge value `F`.

This should not yet be read as the final object-language `K`. It is a semantic
gate testing whether a literature-motivated four-valued knowledge operator fits
4-PEL's existing model structure. The next gates are reflexive factivity,
conjunction behaviour, internal negation versus absence of knowledge, and only
then a Fitch formalization.
-/

end PEL4
