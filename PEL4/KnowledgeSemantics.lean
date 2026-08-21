import PEL4.Syntax

namespace PEL4

/-!
# Knowledge semantics comparison gate

This module does not yet extend the object language with a full four-valued
knowledge operator `K`. Instead it compares two candidate *positive* epistemic
conditions on the existing finite 4-PEL model structure.

The first is the standard positive condition for an FDE-style modal box:

  phi has positive support at every accessible world.

The second adds Belnapian value stability:

  phi has positive support at every accessible world,
  and phi has the same complete FDE value throughout the accessible range.

This separation is motivated by the literature on knowledge and ignorance in
Belnap-Dunn logic. The negative component of a future four-valued knowledge
operator is deliberately left open at this stage.
-/

/-- Standard positive `Box` condition: positive support at every accessible
world. -/
def standardBoxPositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (m.R i w).all (fun w' => (eval m w' phi).pos)

/-- The complete FDE value of `phi` is stable over the accessible range.
The empty and singleton ranges are vacuously stable. -/
def accessibleFDEValueStable {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  match m.R i w with
  | [] => true
  | first :: rest =>
      rest.all (fun w' => decide (eval m w' phi = eval m first phi))

/-- Preferred positive knowledge candidate for the current design gate:
standard universal positive support plus stability of the full Belnapian value. -/
def evidenceStableKnowledgePositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  standardBoxPositive m i w phi && accessibleFDEValueStable m i w phi

/-- Evidence-stable positive knowledge is at least as strong as the ordinary
positive modal-box condition. -/
theorem evidence_stable_knowledge_implies_standard_box
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (h : evidenceStableKnowledgePositive m i w phi = true) :
    standardBoxPositive m i w phi = true := by
  simpa [evidenceStableKnowledgePositive] using And.left
    (Bool.and_eq_true.mp h)

/-!
## A finite contrast model

At both accessible worlds, `p` has positive support, so the standard FDE-style
box condition accepts it. But the complete values differ (`T` versus `B`), so
the evidence-stable knowledge condition rejects it.

This is the exact structural phenomenon for which the ordinary FDE box has
been criticized as an epistemic knowledge operator.
-/

inductive KnowledgeGateAtom where
  | p
deriving DecidableEq, Repr

inductive KnowledgeGateAgent where
  | a
deriving DecidableEq, Repr

inductive KnowledgeGateWorld where
  | root | tWorld | bWorld
deriving DecidableEq, Repr

/-- Accessible evidence sources carry `T` and `B` respectively. -/
def knowledgeGateVal : KnowledgeGateWorld → KnowledgeGateAtom → FDEValue
| KnowledgeGateWorld.root, _ => FDEValue.T
| KnowledgeGateWorld.tWorld, _ => FDEValue.T
| KnowledgeGateWorld.bWorld, _ => FDEValue.B

/-- Uniform probability over the two accessible evidence worlds. Probability
is irrelevant to the candidate knowledge predicates but is supplied so the
example is an ordinary 4-PEL `Model`. -/
def knowledgeGateMu : FiniteSet KnowledgeGateWorld → Rat
| S =>
  let pt := if S.contains KnowledgeGateWorld.tWorld then (1 : Rat) / 2 else 0
  let pb := if S.contains KnowledgeGateWorld.bWorld then (1 : Rat) / 2 else 0
  pt + pb

/-- Contrast model used only to separate ordinary positive `Box` from
Belnapian-value-stable positive knowledge. -/
def KnowledgeGateModel :
    Model KnowledgeGateWorld KnowledgeGateAgent KnowledgeGateAtom :=
  { worlds := [KnowledgeGateWorld.root,
      KnowledgeGateWorld.tWorld, KnowledgeGateWorld.bWorld]
  , R := fun _ _ => [KnowledgeGateWorld.tWorld, KnowledgeGateWorld.bWorld]
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
#eval! evidenceStableKnowledgePositive KnowledgeGateModel KnowledgeGateAgent.a
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

/-- Consequently, the evidence-stable positive knowledge candidate rejects the
same proposition accepted by the standard positive box condition. -/
theorem standard_box_can_hold_without_evidence_stable_knowledge :
    standardBoxPositive KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = true ∧
    evidenceStableKnowledgePositive KnowledgeGateModel KnowledgeGateAgent.a
      KnowledgeGateWorld.root knowledgeGateP = false := by
  native_decide

/-!
## Interpretation

The theorem above does not claim that the evidence-stable candidate is already
the final 4-PEL knowledge operator. It proves a design-relevant separation:
ordinary universal positive support does not guarantee stability of the
four-valued information state.

A future object-language `K` can therefore be compared against both notions
rather than silently inheriting one of them.
-/

end PEL4
