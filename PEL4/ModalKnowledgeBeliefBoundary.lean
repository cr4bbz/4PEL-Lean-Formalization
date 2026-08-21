import PEL4.ModalKnowledgeIgnoranceBoundary

namespace PEL4

/-!
# Knowledge versus probabilistic belief

The modal layer now has mature separate semantics for evidence-stable knowledge
`K` and probabilistic threshold belief `B`.  This gate asks when their complete
four-valued outputs coincide.

The key observation is that a stable, nonempty accessible profile is constant.
For a constant FDE value, each positive/negative component is either present on
all accessible worlds or on none.  The corresponding belief evidence set is
therefore either the full accessibility list, with probability `1`, or the empty
list, with probability `0`.

Because every 4-PEL threshold satisfies

  0 < c <= 1,

probabilistic belief recovers the same complete FDE value as evidence-stable
knowledge on stable profiles.
-/

/-- Filtering a finite world list by a Boolean component of a constant FDE
profile returns either the entire list or the empty list. -/
theorem filterWorlds_constant_component
    {W : Type}
    (worlds : FiniteSet W)
    (value : W → FDEValue)
    (v : FDEValue)
    (component : FDEValue → Bool)
    (hConst : ∀ x, x ∈ worlds → value x = v) :
    filterWorlds worlds (fun x => component (value x)) =
      if component v then worlds else [] := by
  induction worlds with
  | nil =>
      simp [filterWorlds]
  | cons first rest ih =>
      have hFirst : value first = v := hConst first (by simp)
      have hRest : ∀ x, x ∈ rest → value x = v := by
        intro x hx
        exact hConst x (by simp [hx])
      specialize ih hRest
      cases hComponent : component v <;>
        simp [filterWorlds, hFirst, hComponent, ih]

/-- Threshold belief recovers an arbitrary constant FDE profile exactly. -/
theorem modal_belief_recovers_constant_profile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) (v : FDEValue)
    (hConst : ∀ x, x ∈ m.R i w → value x = v) :
    belief m i w value = v := by
  have hPosFilter := filterWorlds_constant_component
    (m.R i w) value v (fun z => z.pos) hConst
  have hNegFilter := filterWorlds_constant_component
    (m.R i w) value v (fun z => z.neg) hConst
  have hZeroLt : (0 : Rat) < m.c i :=
    lt_trans (by native_decide : (0 : Rat) < 1 / 2) (m.c_gt_half i)
  have hZeroNotGe : ¬ (0 : Rat) ≥ m.c i := by
    exact not_le_of_gt hZeroLt
  have hOneGe : (1 : Rat) ≥ m.c i := m.c_le_one i
  rcases v with ⟨vp, vn⟩
  cases vp <;> cases vn <;>
    simp [belief, hPosFilter, hNegFilter, hZeroNotGe, hOneGe,
      m.mu_total, m.mu_empty]

/-- On every stable accessible profile, primitive evidence-stable knowledge and
probabilistic threshold belief have exactly the same four-valued output. -/
theorem modal_knowledge_equals_belief_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hStable : modalAccessibleValueStable (m.R i w)
      (fun x => evalModal m x phi) = true) :
    evalModal m w (ModalFormula.know i phi) =
      evalModal m w (ModalFormula.bel i phi) := by
  have hNonempty : m.R i w ≠ [] := model_accessibility_nonempty m i w
  rcases modal_constant_profile_of_stable_nonempty
      (m.R i w) (fun x => evalModal m x phi) hNonempty hStable with
    ⟨v, hConst⟩
  have hK : evalModal m w (ModalFormula.know i phi) = v :=
    modal_knowledge_recovers_nonempty_constant_profile
      m i w phi v hNonempty hConst
  have hB : evalModal m w (ModalFormula.bel i phi) = v := by
    change belief m i w (fun x => evalModal m x phi) = v
    exact modal_belief_recovers_constant_profile
      m i w (fun x => evalModal m x phi) v hConst
  rw [hK, hB]

/-- Exact equality boundary.  On unstable profiles knowledge is forced to `F`,
so equality with belief survives precisely when belief independently also has
value `F`. -/
theorem modal_knowledge_equals_belief_iff_stable_or_belief_false
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) =
        evalModal m w (ModalFormula.bel i phi) ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true ∨
      evalModal m w (ModalFormula.bel i phi) = FDEValue.F := by
  constructor
  · intro hEq
    cases hStable : modalAccessibleValueStable (m.R i w)
        (fun x => evalModal m x phi) with
    | true =>
        exact Or.inl hStable
    | false =>
        right
        have hKFalse := modal_knowledge_false_of_instability
          m i w phi hStable
        calc
          evalModal m w (ModalFormula.bel i phi) =
              evalModal m w (ModalFormula.know i phi) := hEq.symm
          _ = FDEValue.F := hKFalse
  · intro h
    rcases h with hStable | hBeliefFalse
    · exact modal_knowledge_equals_belief_of_stable m i w phi hStable
    · cases hStable : modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) with
      | true =>
          exact modal_knowledge_equals_belief_of_stable m i w phi hStable
      | false =>
          have hKFalse := modal_knowledge_false_of_instability
            m i w phi hStable
          rw [hKFalse, hBeliefFalse]

/-!
## Instability witness

The existing `KnowledgeGateModel` has accessible values `T` and `B`.
The profile is therefore unstable, so knowledge is strict `F`.

Threshold belief behaves differently: both accessible worlds positively support
`p`, giving positive probability `1`, while only the `B` world contributes
negative support, with probability `1/2 < 2/3`.  Hence belief is strict `T`.

So instability can separate knowledge and belief maximally:

  K p = F,
  B p = T.
-/

/-- In the heterogeneous `T/B` gate model, modal knowledge is strict `F`. -/
theorem modal_knowledge_belief_gate_knowledge_false :
    evalModal KnowledgeGateModel KnowledgeGateWorld.root
      (ModalFormula.know KnowledgeGateAgent.a modalGateP) = FDEValue.F := by
  native_decide

/-- In the same model, threshold belief is strict `T`. -/
theorem modal_knowledge_belief_gate_belief_true :
    evalModal KnowledgeGateModel KnowledgeGateWorld.root
      (ModalFormula.bel KnowledgeGateAgent.a modalGateP) = FDEValue.T := by
  native_decide

/-- Therefore knowledge and belief need not coincide on unstable profiles. -/
theorem modal_knowledge_belief_can_diverge_under_instability :
    modalAccessibleValueStable
        (KnowledgeGateModel.R KnowledgeGateAgent.a KnowledgeGateWorld.root)
        (fun x => evalModal KnowledgeGateModel x modalGateP) = false ∧
    evalModal KnowledgeGateModel KnowledgeGateWorld.root
        (ModalFormula.know KnowledgeGateAgent.a modalGateP) = FDEValue.F ∧
    evalModal KnowledgeGateModel KnowledgeGateWorld.root
        (ModalFormula.bel KnowledgeGateAgent.a modalGateP) = FDEValue.T := by
  constructor
  · native_decide
  constructor <;> native_decide

/-!
## Interpretation

The relation between `K` and `B` is not a simple strength ordering.

On stable profiles they coincide exactly because both operators see a complete
all-or-none evidence pattern.  Under instability, however, `K` records the
heterogeneity itself as negative epistemic information and collapses to strict
`F`, while probabilistic belief continues aggregating the positive and negative
masses separately.

The exact boundary is:

  K(phi) = B(phi)
  iff
  Stable(phi) OR B(phi) = F.

The second disjunct is accidental agreement: instability already forces
`K(phi) = F`, so equality survives only when threshold belief independently
lands on the same value.

This gives another instance of the project's transport pattern.  Stable
full-value evidence makes the qualitative knowledge projection and the
probabilistic threshold projection commute; heterogeneous evidence can make
them diverge.
-/

end PEL4
