import PEL4.ModalFormulaClassicalRecovery
import PEL4.ProbabilityIntegrityFormulaRecovery

namespace PEL4

/-!
# Gate 10: compositional classical recovery

Gate 6 and Gate 7 recover classical values for the legacy `Formula` language.
This module starts Gate 10 by extending the recovery contract to the full
`ModalFormula` language, including primitive knowledge and raw possibility.

The contract is semantic and compositional. Propositional constructors recurse
locally. Modal constructors require recovery throughout the accessible profile.
Belief additionally requires local threshold completeness; probability integrity
supplies threshold consistency.
-/

/-- Local compositional recovery contract for the full modal language. -/
def ModalFormula.CompositionalRecoveryAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W → ModalFormula Atom Ag → Prop
  | w, ModalFormula.prop p => IsClassicalValue (m.val w p)
  | w, ModalFormula.not phi =>
      ModalFormula.CompositionalRecoveryAt m w phi
  | w, ModalFormula.and phi psi =>
      ModalFormula.CompositionalRecoveryAt m w phi ∧
      ModalFormula.CompositionalRecoveryAt m w psi
  | w, ModalFormula.bel i phi =>
      (∀ u, u ∈ m.R i w →
        ModalFormula.CompositionalRecoveryAt m u phi) ∧
      BeliefThresholdComplete m i w (fun u => evalModal m u phi)
  | w, ModalFormula.know i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.CompositionalRecoveryAt m u phi
  | w, ModalFormula.poss i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.CompositionalRecoveryAt m u phi

/-- The full modal recovery contract is sufficient for classical evaluation on
an integrity-certified model. -/
theorem evalModal_isClassical_of_compositionalRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag) :
    ∀ w,
      ModalFormula.CompositionalRecoveryAt m w phi →
      IsClassicalValue (evalModal m w phi) := by
  induction phi with
  | prop p =>
      intro w h
      exact h
  | not phi ih =>
      intro w h
      exact classicalValue_not _ (ih w h)
  | and phi psi ihPhi ihPsi =>
      intro w h
      exact classicalValue_and _ _ (ihPhi w h.1) (ihPsi w h.2)
  | bel i phi ih =>
      intro w h
      have hClassical :
          ∀ u, u ∈ m.R i w → IsClassicalValue (evalModal m u phi) := by
        intro u hu
        exact ih u (h.1 u hu)
      exact
        (probabilityIntegrity_classicalProfile_beliefClassical_iff_complete
          m hIntegrity i w (fun u => evalModal m u phi) hClassical).2 h.2
  | know i phi ih =>
      intro w h
      apply modalKnowledgeValue_classical_of_profile
        m i w (fun u => evalModal m u phi)
      intro u hu
      exact ih u (h u hu)
  | poss i phi ih =>
      intro w h
      apply modalRawPossibilityValue_classical_of_profile
        m i w (fun u => evalModal m u phi)
      intro u hu
      exact ih u (h u hu)

/-- Global compositional recovery contract. -/
def ModalFormula.CompositionalRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, ModalFormula.CompositionalRecoveryAt m w phi

/-- Globally recovered modal formulas evaluate classically at every world. -/
theorem evalModal_isClassical_of_global_compositionalRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag)
    (hRecovery : ModalFormula.CompositionalRecovery m phi) :
    ∀ w, IsClassicalValue (evalModal m w phi) := by
  intro w
  exact evalModal_isClassical_of_compositionalRecovery
    m hIntegrity phi w (hRecovery w)

/-! ## Constructor closure -/

/-- Globally classical atoms enter the recovery fragment. -/
theorem ModalFormula.CompositionalRecovery.prop
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hAtoms : AtomicClassicalModel m)
    (p : Atom) :
    ModalFormula.CompositionalRecovery m (ModalFormula.prop p) := by
  intro w
  exact hAtoms w p

/-- Recovery is closed under FDE negation. -/
theorem ModalFormula.CompositionalRecovery.not
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    {phi : ModalFormula Atom Ag}
    (hPhi : ModalFormula.CompositionalRecovery m phi) :
    ModalFormula.CompositionalRecovery m (ModalFormula.not phi) := by
  intro w
  exact hPhi w

/-- Recovery is closed under FDE conjunction. -/
theorem ModalFormula.CompositionalRecovery.and
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    {phi psi : ModalFormula Atom Ag}
    (hPhi : ModalFormula.CompositionalRecovery m phi)
    (hPsi : ModalFormula.CompositionalRecovery m psi) :
    ModalFormula.CompositionalRecovery m (ModalFormula.and phi psi) := by
  intro w
  exact ⟨hPhi w, hPsi w⟩

/-- Global recovery of the operand is sufficient for primitive knowledge. -/
theorem ModalFormula.CompositionalRecovery.know
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag)
    {phi : ModalFormula Atom Ag}
    (hPhi : ModalFormula.CompositionalRecovery m phi) :
    ModalFormula.CompositionalRecovery m (ModalFormula.know i phi) := by
  intro w u _
  exact hPhi u

/-- Global recovery of the operand is sufficient for raw possibility. -/
theorem ModalFormula.CompositionalRecovery.poss
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag)
    {phi : ModalFormula Atom Ag}
    (hPhi : ModalFormula.CompositionalRecovery m phi) :
    ModalFormula.CompositionalRecovery m (ModalFormula.poss i phi) := by
  intro w u _
  exact hPhi u

/-- Threshold completeness required to close the fragment under one belief
constructor. -/
def ModalFormula.BeliefCompleteEverywhere
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag)
    (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, BeliefThresholdComplete m i w (fun u => evalModal m u phi)

/-- Belief enters the recovered fragment exactly with its additional global
threshold-completeness obligation. -/
theorem ModalFormula.CompositionalRecovery.bel
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag)
    {phi : ModalFormula Atom Ag}
    (hPhi : ModalFormula.CompositionalRecovery m phi)
    (hComplete : ModalFormula.BeliefCompleteEverywhere m i phi) :
    ModalFormula.CompositionalRecovery m (ModalFormula.bel i phi) := by
  intro w
  exact ⟨fun u _ => hPhi u, hComplete w⟩

/-! ## Fragment-relative consequence -/

/-- LP consequence for modal formulas inside one fixed model. -/
def ModalLP_SemanticEntailsIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi psi : ModalFormula Atom Ag) : Prop :=
  ∀ w, (evalModal m w phi).pos = true →
    (evalModal m w psi).pos = true

/-- ST consequence for modal formulas inside one fixed model. -/
def ModalST_SemanticEntailsIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi psi : ModalFormula Atom Ag) : Prop :=
  ∀ w, evalModal m w phi = FDEValue.T →
    (evalModal m w psi).pos = true

/-- Modal LP consequence always implies modal ST consequence. -/
theorem ModalLP_SemanticEntailsIn_implies_ST
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi psi : ModalFormula Atom Ag)
    (h : ModalLP_SemanticEntailsIn m phi psi) :
    ModalST_SemanticEntailsIn m phi psi := by
  intro w hT
  apply h w
  rw [hT]
  rfl

/-- Gate-10 consequence lift: a compositionally recovered modal antecedent makes
ST and LP coincide throughout an integrity-certified model. -/
theorem modalST_iff_LP_of_compositionalRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi psi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionalRecovery m phi) :
    ModalST_SemanticEntailsIn m phi psi ↔
      ModalLP_SemanticEntailsIn m phi psi := by
  have hClassical :=
    evalModal_isClassical_of_global_compositionalRecovery
      m hIntegrity phi hPhi
  constructor
  · intro hST w hPos
    apply hST w
    rcases hClassical w with hT | hF
    · exact hT
    · rw [hF] at hPos
      contradiction
  · exact ModalLP_SemanticEntailsIn_implies_ST m phi psi

/-! ## Belief boundary -/

/-- Modal form of the Gate-6 threshold-gap witness. -/
def gate10BeliefBoundaryFormula : ModalFormula Unit Unit :=
  ModalFormula.bel () (ModalFormula.prop ())

/-- Classical atoms do not place a belief formula in the recovered fragment when
its threshold decisions are incomplete. -/
theorem gate10_atomicClassical_but_belief_not_recovered :
    AtomicClassicalModel gate6BeliefBoundaryModel ∧
      ¬ ModalFormula.CompositionalRecovery
        gate6BeliefBoundaryModel gate10BeliefBoundaryFormula := by
  constructor
  · exact gate6BeliefBoundary_atomicClassical
  · intro hRecovery
    have hAt := hRecovery false
    exact gate6BeliefBoundary_not_thresholdComplete hAt.2

end PEL4
