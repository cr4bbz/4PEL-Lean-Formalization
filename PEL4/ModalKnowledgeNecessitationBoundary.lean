import PEL4.ModalKnowledgeBeliefFactorization

namespace PEL4

/-!
# Necessitation boundary for evidence-stable knowledge

Classical modal presentations usually treat necessitation as a theorem-level
rule: if `phi` is valid, then `K phi` is valid.  In the present finite 4-PEL
model structure two independent boundaries have to be kept visible.

First, `modalStrictValidIn` quantifies only over worlds explicitly listed in
`m.worlds`, while the `Model` structure does not require accessibility to stay
inside that list.  Strict validity can therefore miss an epistemically
accessible counterexample.

Second, even when the listed world set is closed under accessibility, merely
positive/designated validity permits different complete FDE values such as `T`
and `B`.  Evidence-stable knowledge rejects that heterogeneity.

So strict and positive necessitation split for different structural reasons.
-/

/-- The explicitly listed world set is closed under one agent's accessibility
relation. -/
def ModalAccessibilityClosedForAgent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ w, w ∈ m.worlds → ∀ u, u ∈ m.R i w → u ∈ m.worlds

/-- Model-local strict necessitation schema for one agent. -/
def ModalStrictKnowledgeNecessitationIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ phi : ModalFormula Atom Ag,
    modalStrictValidIn m phi →
    modalStrictValidIn m (ModalFormula.know i phi)

/-- Model-local positive/designated necessitation schema for one agent. -/
def ModalPositiveKnowledgeNecessitationIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ phi : ModalFormula Atom Ag,
    modalPositiveValidIn m phi →
    modalPositiveValidIn m (ModalFormula.know i phi)

/-- Accessibility closure restores strict necessitation.  Strict validity makes
every accessible value exactly `T`; probability-induced seriality then lets the
primitive knowledge operator recover that constant profile as `T`. -/
theorem modal_strict_necessitation_of_accessibility_closed
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hClosed : ModalAccessibilityClosedForAgent m i) :
    ModalStrictKnowledgeNecessitationIn m i := by
  intro phi hValid
  unfold modalStrictValidIn at hValid ⊢
  intro w hw
  unfold modalStrictTrueAt at hValid ⊢
  have hNonempty : m.R i w ≠ [] := model_accessibility_nonempty m i w
  have hConst : ∀ u, u ∈ m.R i w → evalModal m u phi = FDEValue.T := by
    intro u hu
    exact hValid u (hClosed w hw u hu)
  exact modal_knowledge_recovers_nonempty_constant_profile
    m i w phi FDEValue.T hNonempty hConst

/-!
## Strict-validity escape witness

The next model lists only `root` as a model world, but `root` accesses `hidden`.
The atom `p` is strict `T` at `root` and strict `F` at `hidden`.  Hence `p` is
strictly valid according to `modalStrictValidIn`, but `K p` is false at the only
listed world.
-/

inductive NecessitationEscapeWorld where
  | root | hidden
deriving DecidableEq, Repr

inductive NecessitationEscapeAgent where
  | a
deriving DecidableEq, Repr

inductive NecessitationEscapeAtom where
  | p
deriving DecidableEq, Repr

def necessitationEscapeVal :
    NecessitationEscapeWorld → NecessitationEscapeAtom → FDEValue
  | NecessitationEscapeWorld.root, _ => FDEValue.T
  | NecessitationEscapeWorld.hidden, _ => FDEValue.F

def necessitationEscapeMu
    (S : FiniteSet NecessitationEscapeWorld) : Rat :=
  if S.contains NecessitationEscapeWorld.hidden then 1 else 0

def NecessitationEscapeModel :
    Model NecessitationEscapeWorld NecessitationEscapeAgent
      NecessitationEscapeAtom :=
  { worlds := [NecessitationEscapeWorld.root]
  , R := fun _ _ => [NecessitationEscapeWorld.hidden]
  , mu := fun _ _ => necessitationEscapeMu
  , val := necessitationEscapeVal
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

def modalNecessitationEscapeP :
    ModalFormula NecessitationEscapeAtom NecessitationEscapeAgent :=
  ModalFormula.prop NecessitationEscapeAtom.p

/-- The escape model violates closure of the listed world set under `R`. -/
theorem necessitation_escape_worlds_not_accessibility_closed :
    ¬ ModalAccessibilityClosedForAgent
      NecessitationEscapeModel NecessitationEscapeAgent.a := by
  intro hClosed
  have hRoot : NecessitationEscapeWorld.root ∈
      NecessitationEscapeModel.worlds := by
    native_decide
  have hAccessible : NecessitationEscapeWorld.hidden ∈
      NecessitationEscapeModel.R NecessitationEscapeAgent.a
        NecessitationEscapeWorld.root := by
    native_decide
  have hHidden := hClosed NecessitationEscapeWorld.root hRoot
    NecessitationEscapeWorld.hidden hAccessible
  have hNotHidden : ¬ NecessitationEscapeWorld.hidden ∈
      NecessitationEscapeModel.worlds := by
    native_decide
  exact hNotHidden hHidden

/-- `p` is strict-valid on the explicitly listed world set. -/
theorem necessitation_escape_p_strict_valid :
    modalStrictValidIn NecessitationEscapeModel modalNecessitationEscapeP := by
  unfold modalStrictValidIn
  intro w hw
  unfold modalStrictTrueAt
  cases w with
  | root =>
      native_decide
  | hidden =>
      have hImpossible : False := by
        simpa [NecessitationEscapeModel] using hw
      exact hImpossible.elim

/-- Yet the hidden accessible counterexample makes `K p` strict `F` at root. -/
theorem necessitation_escape_knowledge_false_at_root :
    evalModal NecessitationEscapeModel NecessitationEscapeWorld.root
      (ModalFormula.know NecessitationEscapeAgent.a modalNecessitationEscapeP) =
      FDEValue.F := by
  native_decide

/-- Therefore strict model-validity does not imply strict validity of knowledge
without accessibility closure of the listed world set. -/
theorem necessitation_escape_breaks_strict_necessitation :
    modalStrictValidIn NecessitationEscapeModel modalNecessitationEscapeP ∧
    ¬ modalStrictValidIn NecessitationEscapeModel
      (ModalFormula.know NecessitationEscapeAgent.a modalNecessitationEscapeP) := by
  refine ⟨necessitation_escape_p_strict_valid, ?_⟩
  intro hValidK
  have hRoot := hValidK NecessitationEscapeWorld.root (by native_decide)
  unfold modalStrictTrueAt at hRoot
  rw [necessitation_escape_knowledge_false_at_root] at hRoot
  exact (by native_decide : FDEValue.F ≠ FDEValue.T) hRoot

/-- The escape model refutes the unrestricted strict necessitation schema. -/
theorem necessitation_escape_refutes_strict_schema :
    ¬ ModalStrictKnowledgeNecessitationIn
      NecessitationEscapeModel NecessitationEscapeAgent.a := by
  intro hNec
  have hKValid := hNec modalNecessitationEscapeP
    necessitation_escape_p_strict_valid
  exact necessitation_escape_breaks_strict_necessitation.2 hKValid

/-!
## Positive-validity instability witness

The existing `KnowledgeGateModel` is accessibility-closed: every world accesses
`left` and `right`, both explicitly listed.  The atom `p` is positively true at
all listed worlds, with values `T`, `T`, and `B`.  Positive validity therefore
holds, but the accessible `T/B` profile is unstable and `K p = F`.

Thus accessibility closure alone repairs strict necessitation but not positive
necessitation.
-/

/-- The existing heterogeneous knowledge gate is closed under accessibility. -/
theorem knowledge_gate_worlds_accessibility_closed :
    ModalAccessibilityClosedForAgent
      KnowledgeGateModel KnowledgeGateAgent.a := by
  intro _w _hw u _hu
  cases u <;> native_decide

/-- The gate proposition is positively valid at every explicitly listed world. -/
theorem knowledge_gate_p_positive_valid :
    modalPositiveValidIn KnowledgeGateModel modalGateP := by
  unfold modalPositiveValidIn
  intro w _hw
  unfold modalPositiveAt
  cases w <;> native_decide

/-- Positive knowledge of that positively valid proposition is not positively
valid, because the common accessible `T/B` profile is unstable. -/
theorem knowledge_gate_kp_not_positive_valid :
    ¬ modalPositiveValidIn KnowledgeGateModel
      (ModalFormula.know KnowledgeGateAgent.a modalGateP) := by
  intro hValidK
  have hRoot := hValidK KnowledgeGateWorld.root (by native_decide)
  unfold modalPositiveAt at hRoot
  rw [modal_knowledge_gate_is_false] at hRoot
  exact (by native_decide : FDEValue.F.pos ≠ true) hRoot

/-- Positive necessitation fails even when the listed world set is perfectly
closed under accessibility. -/
theorem positive_necessitation_fails_even_with_accessibility_closure :
    ModalAccessibilityClosedForAgent
        KnowledgeGateModel KnowledgeGateAgent.a ∧
    modalPositiveValidIn KnowledgeGateModel modalGateP ∧
    ¬ modalPositiveValidIn KnowledgeGateModel
      (ModalFormula.know KnowledgeGateAgent.a modalGateP) := by
  exact ⟨knowledge_gate_worlds_accessibility_closed,
    knowledge_gate_p_positive_valid,
    knowledge_gate_kp_not_positive_valid⟩

/-- Consequently the unrestricted positive necessitation schema fails in an
accessibility-closed model. -/
theorem knowledge_gate_refutes_positive_necessitation_schema :
    ¬ ModalPositiveKnowledgeNecessitationIn
      KnowledgeGateModel KnowledgeGateAgent.a := by
  intro hNec
  have hKValid := hNec modalGateP knowledge_gate_p_positive_valid
  exact knowledge_gate_kp_not_positive_valid hKValid

/-!
## Interpretation

Necessitation splits into two independent transport requirements.

For strict `T` validity:

```text
strict validity + accessibility closure -> strict K-validity.
```

Without closure, validity can simply fail to cover worlds that the epistemic
operator still inspects.

For merely positive/designated validity, closure is not enough:

```text
positive validity + accessibility closure does not imply positive K-validity.
```

The obstruction is specifically four-valued.  A globally positive profile may
still vary between `T` and `B`; the primitive knowledge operator treats that
full-value heterogeneity as epistemic instability and returns strict `F`.

So the classical necessitation slogan decomposes in 4-PEL into a domain-closure
condition and, for the positive fragment, an additional information-stability
condition.
-/

end PEL4
