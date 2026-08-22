import PEL4.ModalDynamicsReachability

namespace PEL4

/-!
# Threshold robustness under probabilistic conditionalization

The previous dynamic modules establish two extremes:

* probability-free modal formulas are invariant under admissible
  conditionalization;
* once probabilistic belief is available, every ordered transition between
  T, F, B, and N is reachable at the level of K(B p).

This module isolates the semantic boundary between those extremes.

For a belief formula, conditionalization changes its complete FDE value exactly
when at least one of its two threshold bits changes.  The relevant quantities
are the positive and negative support masses of the embedded modal formula.

This yields a compositional robustness predicate that permits `bel`
subformulas.  A belief node is robust when neither threshold bit changes at any
world.  Negation, conjunction, knowledge, and raw possibility preserve
robustness compositionally.
-/

/-- Positive support mass used by a modal belief formula at one local state. -/
def modalPositiveBeliefMass
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Rat :=
  let Rw := m.R i w
  let posWorlds := filterWorlds Rw (fun u => (evalModal m u phi).pos)
  m.mu i w posWorlds

/-- Negative support mass used by a modal belief formula at one local state. -/
def modalNegativeBeliefMass
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Rat :=
  let Rw := m.R i w
  let negWorlds := filterWorlds Rw (fun u => (evalModal m u phi).neg)
  m.mu i w negWorlds

/-- Modal belief is exactly the pair of threshold decisions on its positive and
negative support masses. -/
theorem evalModal_bel_eq_threshold_pair
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.bel i phi) =
      { pos := decide (modalPositiveBeliefMass m i w phi ≥ m.c i)
      , neg := decide (modalNegativeBeliefMass m i w phi ≥ m.c i) } := by
  rfl

/-- Exact pointwise robustness boundary for a probabilistic belief formula.

The belief value is unchanged between two models iff neither its positive nor
its negative threshold bit changes.  No syntactic restriction on the embedded
formula is required. -/
theorem modal_belief_value_eq_iff_threshold_bits_eq
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal after w (ModalFormula.bel i phi) =
        evalModal before w (ModalFormula.bel i phi) ↔
      decide (modalPositiveBeliefMass after i w phi ≥ after.c i) =
          decide (modalPositiveBeliefMass before i w phi ≥ before.c i) ∧
      decide (modalNegativeBeliefMass after i w phi ≥ after.c i) =
          decide (modalNegativeBeliefMass before i w phi ≥ before.c i) := by
  rw [evalModal_bel_eq_threshold_pair, evalModal_bel_eq_threshold_pair]
  constructor
  · intro h
    exact ⟨congrArg FDEValue.pos h, congrArg FDEValue.neg h⟩
  · rintro ⟨hPos, hNeg⟩
    apply FDEValue.ext
    · exact hPos
    · exact hNeg

/-- A formula is robust for one specific admissible conditionalization when its
complete value is protected compositionally.

The important clause is `bel`: the embedded formula need not itself be robust.
It is enough that the update leave both threshold decisions of the resulting
belief unchanged at every world.  This allows semantic robustness to absorb
subformula changes that never cross a Lockean boundary. -/
inductive ModalConditionalizationRobust
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E) :
    ModalFormula Atom Ag → Prop where
  | prop (p : Atom) :
      ModalConditionalizationRobust m E hAdm (ModalFormula.prop p)
  | neg {phi : ModalFormula Atom Ag} :
      ModalConditionalizationRobust m E hAdm phi →
      ModalConditionalizationRobust m E hAdm (ModalFormula.not phi)
  | conj {phi psi : ModalFormula Atom Ag} :
      ModalConditionalizationRobust m E hAdm phi →
      ModalConditionalizationRobust m E hAdm psi →
      ModalConditionalizationRobust m E hAdm (ModalFormula.and phi psi)
  | know (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalConditionalizationRobust m E hAdm phi →
      ModalConditionalizationRobust m E hAdm (ModalFormula.know i phi)
  | poss (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalConditionalizationRobust m E hAdm phi →
      ModalConditionalizationRobust m E hAdm (ModalFormula.poss i phi)
  | bel (i : Ag) (phi : ModalFormula Atom Ag)
      (hPos : ∀ w,
        decide (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi ≥
            (conditionalize m E hAdm).c i) =
          decide (modalPositiveBeliefMass m i w phi ≥ m.c i))
      (hNeg : ∀ w,
        decide (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi ≥
            (conditionalize m E hAdm).c i) =
          decide (modalNegativeBeliefMass m i w phi ≥ m.c i)) :
      ModalConditionalizationRobust m E hAdm (ModalFormula.bel i phi)

/-- Every robust formula preserves its complete FDE value under the designated
conditionalization. -/
theorem evalModal_conditionalize_of_robust
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    {phi : ModalFormula Atom Ag}
    (hRobust : ModalConditionalizationRobust m E hAdm phi) :
    ∀ w,
      evalModal (conditionalize m E hAdm) w phi = evalModal m w phi := by
  induction hRobust with
  | prop p =>
      intro w
      rfl
  | neg hPhi ih =>
      intro w
      change FDEValue.not (evalModal (conditionalize m E hAdm) w _) =
        FDEValue.not (evalModal m w _)
      rw [ih w]
  | conj hPhi hPsi ihPhi ihPsi =>
      intro w
      change FDEValue.and
          (evalModal (conditionalize m E hAdm) w _)
          (evalModal (conditionalize m E hAdm) w _) =
        FDEValue.and (evalModal m w _) (evalModal m w _)
      rw [ihPhi w, ihPsi w]
  | @know i phi hPhi ih =>
      intro w
      change modalKnowledgeValue (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
        modalKnowledgeValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalKnowledgeValue_congr
        m (conditionalize m E hAdm) i w
        (fun u => evalModal m u phi)
        (fun u => evalModal (conditionalize m E hAdm) u phi)
        (conditionalize_accessibility_eq m E hAdm i w) hValues
  | @poss i phi hPhi ih =>
      intro w
      change modalRawPossibilityValue (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
        modalRawPossibilityValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalRawPossibilityValue_congr
        m (conditionalize m E hAdm) i w
        (fun u => evalModal m u phi)
        (fun u => evalModal (conditionalize m E hAdm) u phi)
        (conditionalize_accessibility_eq m E hAdm i w) hValues
  | bel i phi hPos hNeg =>
      intro w
      apply (modal_belief_value_eq_iff_threshold_bits_eq
        m (conditionalize m E hAdm) i w phi).2
      exact ⟨hPos w, hNeg w⟩

/-- The older probability-free fragment is contained in the new robustness
notion.  Hence threshold robustness is a genuine extension of the existing
syntactic invariance theorem. -/
theorem probabilityFree_implies_conditionalizationRobust
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    ModalConditionalizationRobust m E hAdm phi := by
  induction hFree with
  | prop p =>
      exact ModalConditionalizationRobust.prop p
  | neg hPhi ih =>
      exact ModalConditionalizationRobust.neg ih
  | conj hPhi hPsi ihPhi ihPsi =>
      exact ModalConditionalizationRobust.conj ihPhi ihPsi
  | @know i phi hPhi ih =>
      exact ModalConditionalizationRobust.know i ih
  | @poss i phi hPhi ih =>
      exact ModalConditionalizationRobust.poss i ih

/-- A concrete non-probability-free robust family.

On the diagonal reachability model (`source = target`), conditioning radically
changes the probability distribution but leaves `B p` on the same threshold
side at every world.  Thus a formula containing `bel` can be robust. -/
theorem diagonal_reachability_belief_is_robust
    (v : FDEValue) :
    ModalConditionalizationRobust
      (DynamicReachabilityModel v v)
      dynamicReachabilityEvidence
      (dynamic_reachability_evidence_admissible v v)
      dynamicReachabilityBelP := by
  apply ModalConditionalizationRobust.bel
  · intro w
    rcases v with ⟨vp, vn⟩
    cases vp <;> cases vn <;> cases w <;> native_decide
  · intro w
    rcases v with ⟨vp, vn⟩
    cases vp <;> cases vn <;> cases w <;> native_decide

/-- The diagonal witness really lies outside the probability-free fragment. -/
theorem diagonal_reachability_belief_not_probabilityFree :
    ¬ ModalProbabilityFree dynamicReachabilityBelP := by
  intro h
  cases h

/-- Consequently, outer knowledge of the robust belief formula is also
invariant under the nontrivial probability update. -/
theorem diagonal_reachability_knowledge_is_robust
    (v : FDEValue) :
    evalModal (DynamicReachabilityUpdated v v)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP =
      evalModal (DynamicReachabilityModel v v)
        DynamicReachabilityWorld.focus dynamicReachabilityKBelP := by
  have hBel := diagonal_reachability_belief_is_robust v
  have hK : ModalConditionalizationRobust
      (DynamicReachabilityModel v v)
      dynamicReachabilityEvidence
      (dynamic_reachability_evidence_admissible v v)
      dynamicReachabilityKBelP :=
    ModalConditionalizationRobust.know DynamicReachabilityAgent.i hBel
  exact evalModal_conditionalize_of_robust
    (DynamicReachabilityModel v v)
    dynamicReachabilityEvidence
    (dynamic_reachability_evidence_admissible v v)
    hK DynamicReachabilityWorld.focus

/-!
## Interpretation

`ModalProbabilityFree` identified a syntactic safe zone: if no probabilistic
belief occurs, probability-only updates cannot matter.

Threshold robustness is strictly more permissive.  A formula may contain
probabilistic belief and even have probability-sensitive substructure.  What
matters for the categorical FDE result is whether the update changes either of
the two Lockean threshold decisions.

Thus the dynamic architecture has two complementary facts:

```text
complete reachability: threshold crossings can realize every T/F/B/N transition;
threshold robustness:  without a threshold-bit change, the belief value is fixed.
```

The relevant invariant is therefore not raw probability itself but the pair of
threshold sides occupied by positive and negative support.

Working name: **Threshold-Side Robustness**.
-/

end PEL4
