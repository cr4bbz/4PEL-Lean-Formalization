import PEL4.KnowledgePossibilityBoundary

namespace PEL4

/-!
# Conservative modal object language

The existing `Formula` language is kept unchanged so the verified 4-PEL core
and all existing paradox developments remain stable.  This module adds a
conservative modal language on top of it with primitive evidence-stable
knowledge and primitive raw accessibility possibility.

The new constructors are deliberately distinct:

* `know i phi` evaluates by the evidence-stable four-valued knowledge semantics;
* `poss i phi` evaluates by raw accessibility possibility;
* `not (know i (not phi))` remains an ordinary internal dual expression and is
  not identified definitionally with `poss i phi`.

This is the object language intended for the Fitch gate.
-/

/-- Modal extension of the 4-PEL formula language. -/
inductive ModalFormula (Atom Ag : Type) where
  | prop : Atom → ModalFormula Atom Ag
  | not  : ModalFormula Atom Ag → ModalFormula Atom Ag
  | and  : ModalFormula Atom Ag → ModalFormula Atom Ag → ModalFormula Atom Ag
  | bel  : Ag → ModalFormula Atom Ag → ModalFormula Atom Ag
  | know : Ag → ModalFormula Atom Ag → ModalFormula Atom Ag
  | poss : Ag → ModalFormula Atom Ag → ModalFormula Atom Ag

/-- Embed every legacy 4-PEL formula into the modal language. -/
def ModalFormula.ofFormula {Atom Ag : Type} :
    Formula Atom Ag → ModalFormula Atom Ag
  | Formula.prop p => ModalFormula.prop p
  | Formula.not phi => ModalFormula.not (ModalFormula.ofFormula phi)
  | Formula.and phi psi =>
      ModalFormula.and (ModalFormula.ofFormula phi) (ModalFormula.ofFormula psi)
  | Formula.bel i phi => ModalFormula.bel i (ModalFormula.ofFormula phi)

/-- Internal knowledge dual written inside the new object language.  It is kept
separate from primitive raw possibility. -/
def ModalFormula.knowledgeDual {Atom Ag : Type}
    (i : Ag) (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.not (ModalFormula.know i (ModalFormula.not phi))

/-- Stability of an arbitrary FDE-valued interpretation over a finite
accessible range. -/
def modalAccessibleValueStable {W : Type} [DecidableEq W]
    (worlds : FiniteSet W) (value : W → FDEValue) : Bool :=
  match worlds with
  | [] => true
  | first :: rest =>
      rest.all (fun w' => decide (value w' = value first))

/-- Evidence-stable four-valued knowledge applied to an arbitrary semantic
interpretation. -/
def modalKnowledgeValue {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) : FDEValue :=
  let stable := modalAccessibleValueStable (m.R i w) value
  { pos := (m.R i w).all (fun w' => (value w').pos) && stable
  , neg := (!stable) || (m.R i w).any (fun w' => (value w').neg)
  }

/-- Raw four-valued accessibility possibility applied to an arbitrary semantic
interpretation. -/
def modalRawPossibilityValue {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) : FDEValue :=
  { pos := (m.R i w).any (fun w' => (value w').pos)
  , neg := (m.R i w).all (fun w' => (value w').neg)
  }

/-- Recursive evaluation of the modal object language. -/
def evalModal {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W → ModalFormula Atom Ag → FDEValue
  | w, ModalFormula.prop p => m.val w p
  | w, ModalFormula.not phi => FDEValue.not (evalModal m w phi)
  | w, ModalFormula.and phi psi =>
      FDEValue.and (evalModal m w phi) (evalModal m w psi)
  | w, ModalFormula.bel i phi =>
      belief m i w (fun w' => evalModal m w' phi)
  | w, ModalFormula.know i phi =>
      modalKnowledgeValue m i w (fun w' => evalModal m w' phi)
  | w, ModalFormula.poss i phi =>
      modalRawPossibilityValue m i w (fun w' => evalModal m w' phi)

/-- The modal language is a conservative extension of the existing object
language: embedding does not change semantic value. -/
theorem evalModal_ofFormula
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    evalModal m w (ModalFormula.ofFormula phi) = eval m w phi := by
  induction phi generalizing w with
  | prop p =>
      rfl
  | not phi ih =>
      change FDEValue.not (evalModal m w (ModalFormula.ofFormula phi)) =
        FDEValue.not (eval m w phi)
      rw [ih]
  | and phi psi ihPhi ihPsi =>
      change FDEValue.and
          (evalModal m w (ModalFormula.ofFormula phi))
          (evalModal m w (ModalFormula.ofFormula psi)) =
        FDEValue.and (eval m w phi) (eval m w psi)
      rw [ihPhi, ihPsi]
  | bel i phi ih =>
      change belief m i w
          (fun w' => evalModal m w' (ModalFormula.ofFormula phi)) =
        belief m i w (fun w' => eval m w' phi)
      apply congrArg (belief m i w)
      funext w'
      exact ih (w := w')

/-- Generic stability in the modal evaluator agrees with the already verified
legacy stability predicate on embedded formulas. -/
theorem modal_stability_ofFormula
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' (ModalFormula.ofFormula phi)) =
      accessibleFDEValueStable m i w phi := by
  cases hR : m.R i w with
  | nil =>
      simp [modalAccessibleValueStable, accessibleFDEValueStable, hR]
  | cons first rest =>
      simp [modalAccessibleValueStable, accessibleFDEValueStable, hR,
        evalModal_ofFormula]

/-- Primitive object-language knowledge reproduces the verified semantic
knowledge candidate on every embedded legacy formula. -/
theorem modal_knowledge_ofFormula
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    evalModal m w (ModalFormula.know i (ModalFormula.ofFormula phi)) =
      evidenceStableKnowledgeValue m i w phi := by
  unfold evalModal modalKnowledgeValue
  unfold evidenceStableKnowledgeValue evidenceStableKnowledgePositive
    evidenceStableKnowledgeNegative standardBoxPositive standardBoxNegative
  rw [modal_stability_ofFormula m i w phi]
  simp [evalModal_ofFormula]

/-- Primitive object-language raw possibility reproduces the verified raw
accessibility semantics on every embedded legacy formula. -/
theorem modal_possibility_ofFormula
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    evalModal m w (ModalFormula.poss i (ModalFormula.ofFormula phi)) =
      rawPossibilityValue m i w phi := by
  unfold evalModal modalRawPossibilityValue
  unfold rawPossibilityValue rawPossibilityPositive rawPossibilityNegative
  simp [evalModal_ofFormula]

/-!
## Object-language sanity witnesses
-/

def modalGateP : ModalFormula KnowledgeGateAtom KnowledgeGateAgent :=
  ModalFormula.prop KnowledgeGateAtom.p

/-- The previously verified heterogeneous `T/B` model is now expressible with
primitive object-language `K`. -/
theorem modal_knowledge_gate_is_false :
    evalModal KnowledgeGateModel KnowledgeGateWorld.root
      (ModalFormula.know KnowledgeGateAgent.a modalGateP) = FDEValue.F := by
  native_decide

/-- The `B/F` possibility witness is now internal to the object language:
primitive raw possibility remains `B`, while the internal knowledge dual is
strict `T`. -/
theorem modal_raw_possibility_and_knowledge_dual_diverge :
    evalModal (PossibilityPairModel FDEValue.B FDEValue.F)
        KnowledgeGateWorld.root
        (ModalFormula.poss KnowledgeGateAgent.a modalGateP) = FDEValue.B ∧
    evalModal (PossibilityPairModel FDEValue.B FDEValue.F)
        KnowledgeGateWorld.root
        (ModalFormula.knowledgeDual KnowledgeGateAgent.a modalGateP) =
      FDEValue.T := by
  native_decide

/-!
## Interpretation

The modal language is conservative over the existing 4-PEL syntax and adds two
primitive modal transports whose semantics have already been analyzed
independently.  This prevents the Fitch development from smuggling in either of
the two classical identifications that the preceding gates showed to be unsafe:

* `K(phi and psi)` does not automatically decompose into `K(phi)` and `K(psi)`;
* primitive raw possibility is not definitionally `not K(not phi)`.

The next module can therefore encode Fitch with the relevant proof steps visible
as explicit semantic assumptions or theorems rather than hidden abbreviations.
-/

end PEL4
