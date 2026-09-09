import PEL4.FormulaClassicalRecovery

namespace PEL4

/-!
# Gate 6: exact recovery boundary for Lockean belief

Propositional connectives, evidence-stable knowledge, and raw possibility preserve the
recovered classical sector under classical inputs. Lockean belief is different: its
two threshold decisions can jointly be false (a gap) or, under the weak legacy model
interface, can in principle jointly be true.

This file exposes those two threshold bits and states the exact local regularity
condition required for a belief output to lie in `{T,F}`. It then lifts that condition
recursively through the full legacy `Formula` syntax.
-/

/-- Positive threshold decision made by the Lockean belief operator. -/
def beliefPositiveThresholdBit
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) : Bool :=
  let posWorlds := filterWorlds (m.R i w) (fun u => (value u).pos)
  m.mu i w posWorlds ≥ m.c i

/-- Negative threshold decision made by the Lockean belief operator. -/
def beliefNegativeThresholdBit
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) : Bool :=
  let negWorlds := filterWorlds (m.R i w) (fun u => (value u).neg)
  m.mu i w negWorlds ≥ m.c i

/-- The existing belief implementation is exactly the pair of exposed threshold bits. -/
theorem belief_eq_thresholdBits
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) :
    belief m i w value =
      { pos := beliefPositiveThresholdBit m i w value
      , neg := beliefNegativeThresholdBit m i w value } := by
  rfl

/-- At least one side of the Lockean threshold decision fires. -/
def BeliefThresholdComplete
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) : Prop :=
  beliefPositiveThresholdBit m i w value = true ∨
  beliefNegativeThresholdBit m i w value = true

/-- The two Lockean threshold decisions do not both fire. -/
def BeliefThresholdConsistent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) : Prop :=
  ¬ (beliefPositiveThresholdBit m i w value = true ∧
     beliefNegativeThresholdBit m i w value = true)

/-- Exact local threshold regularity for a classical belief output. -/
def BeliefThresholdRegular
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) : Prop :=
  BeliefThresholdComplete m i w value ∧
  BeliefThresholdConsistent m i w value

/-- Exact belief-recovery theorem: a Lockean belief value is classical iff exactly
one of its positive/negative threshold decisions fires. -/
theorem belief_isClassical_iff_thresholdRegular
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) :
    IsClassicalValue (belief m i w value) ↔
      BeliefThresholdRegular m i w value := by
  rw [belief_eq_thresholdBits]
  cases hp : beliefPositiveThresholdBit m i w value <;>
    cases hn : beliefNegativeThresholdBit m i w value <;>
    simp [BeliefThresholdRegular, BeliefThresholdComplete,
      BeliefThresholdConsistent, IsClassicalValue,
      FDEValue.T, FDEValue.F, hp, hn]

/-- The Gate-6 1/2--1/2 witness fails belief completeness at threshold 3/5. -/
theorem gate6BeliefBoundary_not_thresholdComplete :
    ¬ BeliefThresholdComplete gate6BeliefBoundaryModel () false
      (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) := by
  have hBits := belief_eq_thresholdBits gate6BeliefBoundaryModel () false
    (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ()))
  have hStruct :
      { pos := beliefPositiveThresholdBit gate6BeliefBoundaryModel () false
          (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ()))
      , neg := beliefNegativeThresholdBit gate6BeliefBoundaryModel () false
          (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) } =
        FDEValue.N :=
    hBits.symm.trans gate6BeliefBoundary_belief_is_N
  have hpFalse :
      beliefPositiveThresholdBit gate6BeliefBoundaryModel () false
        (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) = false := by
    simpa [FDEValue.N] using congrArg FDEValue.pos hStruct
  have hnFalse :
      beliefNegativeThresholdBit gate6BeliefBoundaryModel () false
        (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) = false := by
    simpa [FDEValue.N] using congrArg FDEValue.neg hStruct
  unfold BeliefThresholdComplete
  simp [hpFalse, hnFalse]

/-- The same witness is not a contradiction problem: its threshold decisions are
consistent, but incomplete. -/
theorem gate6BeliefBoundary_thresholdConsistent :
    BeliefThresholdConsistent gate6BeliefBoundaryModel () false
      (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) := by
  have hBits := belief_eq_thresholdBits gate6BeliefBoundaryModel () false
    (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ()))
  have hStruct :
      { pos := beliefPositiveThresholdBit gate6BeliefBoundaryModel () false
          (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ()))
      , neg := beliefNegativeThresholdBit gate6BeliefBoundaryModel () false
          (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) } =
        FDEValue.N :=
    hBits.symm.trans gate6BeliefBoundary_belief_is_N
  have hpFalse :
      beliefPositiveThresholdBit gate6BeliefBoundaryModel () false
        (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) = false := by
    simpa [FDEValue.N] using congrArg FDEValue.pos hStruct
  have hnFalse :
      beliefNegativeThresholdBit gate6BeliefBoundaryModel () false
        (fun u => eval gate6BeliefBoundaryModel u (Formula.prop ())) = false := by
    simpa [FDEValue.N] using congrArg FDEValue.neg hStruct
  unfold BeliefThresholdConsistent
  simp [hpFalse, hnFalse]

/-- Semantic admissibility for formula-level classical recovery. Propositional
constructors recurse locally. A belief node requires the subformula to remain
admissible throughout its accessible range and requires the local pair of threshold
decisions to be regular. -/
def Formula.ClassicalRecoveryAdmissibleAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W → Formula Atom Ag → Prop
  | w, Formula.prop p => IsClassicalValue (m.val w p)
  | w, Formula.not phi => Formula.ClassicalRecoveryAdmissibleAt m w phi
  | w, Formula.and phi psi =>
      Formula.ClassicalRecoveryAdmissibleAt m w phi ∧
      Formula.ClassicalRecoveryAdmissibleAt m w psi
  | w, Formula.bel i phi =>
      (∀ u, u ∈ m.R i w → Formula.ClassicalRecoveryAdmissibleAt m u phi) ∧
      BeliefThresholdRegular m i w (fun u => eval m u phi)

/-- Full legacy-formula recovery theorem. Every constructor is classical whenever its
corresponding recovery obligation is satisfied; belief contributes the only new local
threshold-regularity obligation. -/
theorem eval_isClassical_of_recoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : Formula Atom Ag) :
    ∀ w,
      Formula.ClassicalRecoveryAdmissibleAt m w phi →
      IsClassicalValue (eval m w phi) := by
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
      exact (belief_isClassical_iff_thresholdRegular
        m i w (fun u => eval m u phi)).2 h.2

/-- Every propositionally generated formula is recovery-admissible whenever its atoms
are classical at the evaluation world. -/
theorem propositional_recoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    {phi : Formula Atom Ag}
    (hAtoms : AtomicClassicalAt m w)
    (hphi : Formula.IsPropositional phi) :
    Formula.ClassicalRecoveryAdmissibleAt m w phi := by
  induction hphi with
  | prop p =>
      exact hAtoms p
  | not h ih =>
      exact ih
  | and hphi hpsi ihPhi ihPsi =>
      exact ⟨ihPhi, ihPsi⟩

/-- A global form convenient for nested formula reasoning. -/
def Formula.ClassicalRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.ClassicalRecoveryAdmissibleAt m w phi

/-- Globally admissible formulas evaluate classically at every world. -/
theorem eval_isClassical_of_global_recoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : Formula Atom Ag)
    (h : Formula.ClassicalRecoveryAdmissible m phi) :
    ∀ w, IsClassicalValue (eval m w phi) := by
  intro w
  exact eval_isClassical_of_recoveryAdmissible m phi w (h w)

end PEL4
