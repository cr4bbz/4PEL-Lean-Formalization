import PEL4.ModalDynamicsBeliefRestoration

namespace PEL4

/-!
# Dynamic knowledge phase classification

The verified K/B factorization is pointwise:

  K(phi) = if Stable(phi) then B(phi) else F.

This module lifts that equation to a two-state dynamic comparison.  For any two
models on the same language, the stability status of `phi` before and after the
change determines which channel can move knowledge.

The resulting 2x2 table is independent of the particular update mechanism:

```text
Stable before | Stable after | knowledge phase
--------------+--------------+--------------------------------
true          | true         | K = B on both sides
true          | false        | after-value of K is forced to F
false         | true         | before K = F; after K = after B
false         | false        | K = F on both sides
```

The already verified conditionalization witnesses then realize both
off-diagonal phases: fracture (`true -> false`) and restoration
(`false -> true`).
-/

/-- Stability of `phi` at one agent/world pair. -/
def ModalStableAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Bool :=
  modalAccessibleValueStable (m.R i w) (fun x => evalModal m x phi)

/-- If a formula is stable in both states, knowledge tracks belief in both
states. -/
theorem modal_knowledge_phase_stable_stable
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = true)
    (hAfter : ModalStableAt after i w phi = true) :
    evalModal before w (ModalFormula.know i phi) =
        evalModal before w (ModalFormula.bel i phi) ∧
    evalModal after w (ModalFormula.know i phi) =
        evalModal after w (ModalFormula.bel i phi) := by
  constructor
  · exact modal_knowledge_factorization_stable before i w phi hBefore
  · exact modal_knowledge_factorization_stable after i w phi hAfter

/-- If stability fractures, the posterior knowledge value is absorbed into
strict `F`, while the prior stable state still tracks belief. -/
theorem modal_knowledge_phase_stable_unstable
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = true)
    (hAfter : ModalStableAt after i w phi = false) :
    evalModal before w (ModalFormula.know i phi) =
        evalModal before w (ModalFormula.bel i phi) ∧
    evalModal after w (ModalFormula.know i phi) = FDEValue.F := by
  constructor
  · exact modal_knowledge_factorization_stable before i w phi hBefore
  · exact modal_knowledge_factorization_unstable after i w phi hAfter

/-- If stability is restored, the prior knowledge value is strict `F` and the
posterior knowledge value becomes exactly the posterior belief value. -/
theorem modal_knowledge_phase_unstable_stable
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = false)
    (hAfter : ModalStableAt after i w phi = true) :
    evalModal before w (ModalFormula.know i phi) = FDEValue.F ∧
    evalModal after w (ModalFormula.know i phi) =
        evalModal after w (ModalFormula.bel i phi) := by
  constructor
  · exact modal_knowledge_factorization_unstable before i w phi hBefore
  · exact modal_knowledge_factorization_stable after i w phi hAfter

/-- If both states are unstable, knowledge is dynamically pinned to strict `F`
even if probabilistic belief itself changes. -/
theorem modal_knowledge_phase_unstable_unstable
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = false)
    (hAfter : ModalStableAt after i w phi = false) :
    evalModal before w (ModalFormula.know i phi) = FDEValue.F ∧
    evalModal after w (ModalFormula.know i phi) = FDEValue.F := by
  constructor
  · exact modal_knowledge_factorization_unstable before i w phi hBefore
  · exact modal_knowledge_factorization_unstable after i w phi hAfter

/-- Within the stable/stable phase, equality of knowledge across states is
exactly equality of probabilistic belief across states. -/
theorem modal_knowledge_change_iff_belief_change_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = true)
    (hAfter : ModalStableAt after i w phi = true) :
    evalModal before w (ModalFormula.know i phi) =
        evalModal after w (ModalFormula.know i phi) ↔
      evalModal before w (ModalFormula.bel i phi) =
        evalModal after w (ModalFormula.bel i phi) := by
  rw [modal_knowledge_factorization_stable before i w phi hBefore,
      modal_knowledge_factorization_stable after i w phi hAfter]

/-- Within the unstable/unstable phase, knowledge is invariant at strict `F`. -/
theorem modal_knowledge_invariant_of_persistent_instability
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalStableAt before i w phi = false)
    (hAfter : ModalStableAt after i w phi = false) :
    evalModal before w (ModalFormula.know i phi) =
      evalModal after w (ModalFormula.know i phi) := by
  rw [modal_knowledge_factorization_unstable before i w phi hBefore,
      modal_knowledge_factorization_unstable after i w phi hAfter]

/-- The fracture witness realizes the `stable -> unstable` off-diagonal phase. -/
theorem conditionalization_realizes_stability_fracture_phase :
    ModalStableAt DynamicInstabilityModel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityBelP = true ∧
    ModalStableAt DynamicInstabilityUpdated DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityBelP = false := by
  exact ⟨dynamic_instability_stable_before,
    dynamic_instability_unstable_after⟩

/-- The restoration witness realizes the `unstable -> stable` off-diagonal
phase. -/
theorem conditionalization_realizes_stability_restoration_phase :
    ModalStableAt DynamicRestorationModel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityBelP = false ∧
    ModalStableAt DynamicRestorationUpdated DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityBelP = true := by
  exact ⟨dynamic_restoration_unstable_before,
    dynamic_restoration_stable_after⟩

/-- Admissible conditionalization therefore realizes both directions of
stability phase change in finite models. -/
theorem conditionalization_realizes_both_stability_phase_directions :
    (ModalStableAt DynamicInstabilityModel DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a dynamicInstabilityBelP = true ∧
      ModalStableAt DynamicInstabilityUpdated DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a dynamicInstabilityBelP = false) ∧
    (ModalStableAt DynamicRestorationModel DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a dynamicInstabilityBelP = false ∧
      ModalStableAt DynamicRestorationUpdated DynamicInstabilityAgent.i
          DynamicInstabilityWorld.a dynamicInstabilityBelP = true) := by
  exact ⟨conditionalization_realizes_stability_fracture_phase,
    conditionalization_realizes_stability_restoration_phase⟩

/-!
## Interpretation

The dynamic K/B architecture has two independent channels:

```text
belief channel:    the threshold value B(phi) may change
stability channel: the accessible full-value profile may change phase
```

The stability gate determines whether the belief channel is visible at the
knowledge level.  Stable/stable updates transmit belief changes to `K` exactly;
unstable/unstable updates hide all such changes behind `K = F`; and crossing the
stability boundary switches the filter itself on or off.

The finite conditionalization models show that both off-diagonal transitions
are reachable.  Thus probabilistic conditionalization is neither monotone
knowledge gain nor monotone knowledge loss in this semantics.  It is capable of
moving formulas between epistemic stability phases.
-/

end PEL4
