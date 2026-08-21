import PEL4.ModalKnowledgeBeliefBoundary

namespace PEL4

/-!
# From probabilistic belief to evidence-stable knowledge

The preceding gate proved the exact equality boundary

  K(phi) = B(phi)
  iff
  Stable(phi) OR B(phi) = F.

This module isolates the positive/designated consequence.  Positive knowledge
already contains full-value stability by definition, so it must agree with
probabilistic belief.  In the reverse direction, positive probabilistic belief
upgrades to positive knowledge exactly when the underlying accessible FDE
profile is stable.
-/

/-- Positive probabilistic belief at a point. -/
def modalPositiveBelievedAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.bel i phi)).pos = true

/-- Positive knowledge always agrees with probabilistic belief on the complete
four-valued output. -/
theorem modal_positive_knowledge_has_same_value_as_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hK : modalPositiveKnownAt m i w phi) :
    evalModal m w (ModalFormula.know i phi) =
      evalModal m w (ModalFormula.bel i phi) := by
  unfold modalPositiveKnownAt at hK
  have hStable := (modal_positive_knowledge_components m i w phi hK).2
  exact modal_knowledge_equals_belief_of_stable m i w phi hStable

/-- Positive evidence-stable knowledge entails positive probabilistic belief. -/
theorem modal_positive_knowledge_implies_positive_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hK : modalPositiveKnownAt m i w phi) :
    modalPositiveBelievedAt m i w phi := by
  have hEq := modal_positive_knowledge_has_same_value_as_belief
    m i w phi hK
  unfold modalPositiveBelievedAt
  unfold modalPositiveKnownAt at hK
  rw [← hEq]
  exact hK

/-- Under positive probabilistic belief, stability is exactly the missing
condition for positive knowledge. -/
theorem modal_positive_belief_upgrades_to_knowledge_iff_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hB : modalPositiveBelievedAt m i w phi) :
    modalPositiveKnownAt m i w phi ↔
      modalAccessibleValueStable (m.R i w)
        (fun x => evalModal m x phi) = true := by
  constructor
  · intro hK
    unfold modalPositiveKnownAt at hK
    exact (modal_positive_knowledge_components m i w phi hK).2
  · intro hStable
    have hEq := modal_knowledge_equals_belief_of_stable
      m i w phi hStable
    unfold modalPositiveKnownAt
    unfold modalPositiveBelievedAt at hB
    rw [hEq]
    exact hB

/-- The heterogeneous `T/B` gate witnesses that positive belief alone is not
positive knowledge. -/
theorem modal_positive_belief_does_not_imply_positive_knowledge :
    modalPositiveBelievedAt KnowledgeGateModel KnowledgeGateAgent.a
        KnowledgeGateWorld.root modalGateP ∧
    ¬ modalPositiveKnownAt KnowledgeGateModel KnowledgeGateAgent.a
        KnowledgeGateWorld.root modalGateP := by
  constructor
  · unfold modalPositiveBelievedAt
    native_decide
  · unfold modalPositiveKnownAt
    native_decide

/-- The same witness pinpoints instability as the failed upgrade condition. -/
theorem modal_positive_belief_upgrade_failure_is_instability :
    modalPositiveBelievedAt KnowledgeGateModel KnowledgeGateAgent.a
        KnowledgeGateWorld.root modalGateP ∧
    modalAccessibleValueStable
        (KnowledgeGateModel.R KnowledgeGateAgent.a KnowledgeGateWorld.root)
        (fun x => evalModal KnowledgeGateModel x modalGateP) = false ∧
    (evalModal KnowledgeGateModel KnowledgeGateWorld.root
        (ModalFormula.know KnowledgeGateAgent.a modalGateP)).pos = false := by
  constructor
  · unfold modalPositiveBelievedAt
    native_decide
  constructor <;> native_decide

/-!
## Interpretation

The positive relation between `K` and `B` is now asymmetric but exact:

  K+(phi) -> B+(phi)

while, under the premise `B+(phi)`,

  K+(phi) iff Stable(phi).

So evidence-stable knowledge is not produced by increasing the Lockean
threshold alone.  The decisive extra condition is qualitative invariance of the
complete four-valued evidence profile.

This gives a useful 4-PEL decomposition:

  positive knowledge
  = positive threshold belief + full-value stability

at the level of positive/designated support.
-/

end PEL4
