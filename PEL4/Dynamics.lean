import PEL4.Syntax
import PEL4.Belief

namespace PEL4

/-- Helper to filter a finite set based on another set (intersection). -/
def intersectWorlds {W : Type} [DecidableEq W]
    (A B : FiniteSet W) : FiniteSet W :=
  A.filter (fun w => B.contains w)

/-- Positive evidence mass used by conditionalization at one agent/world pair. -/
def conditionalizationEvidenceMass
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (E : Formula Atom Ag) : Rat :=
  let R_w := m.R i w
  let E_pos := filterWorlds R_w (fun w' => (eval m w' E).pos)
  m.mu i w E_pos

/--
Dynamically conditionalize the local probability measure of agent `i` at world
`w` on the positive extension of evidence formula `E`.

As a raw numerical function this remains total: zero evidence mass returns `0`.
Constructing an updated `Model`, however, now requires an explicit admissibility
proof below.  This keeps impossible-evidence updates from being smuggled into a
normalized model by an unconditional axiom.
-/
def conditionalize_mu {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (E : Formula Atom Ag)
    (S : FiniteSet W) : Rat :=
  let R_w := m.R i w
  let E_pos := filterWorlds R_w (fun w' => (eval m w' E).pos)
  let E_mass := m.mu i w E_pos
  if E_mass == 0 then 0
  else (m.mu i w (intersectWorlds S E_pos)) / E_mass

/--
Evidence `E` is admissible for model-level conditionalization when every local
conditioning event has nonzero probability mass and the resulting raw
conditionalized measure satisfies the two normalization fields required by
`Model`.

The normalization clauses are proof obligations rather than axioms.  In finite
concrete models they can often be discharged by computation; future stronger
measure structure can derive them generically from the positive-mass clause.
-/
structure ConditionalizationAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) : Prop where
  positive_mass :
    ∀ (i : Ag) (w : W), conditionalizationEvidenceMass m i w E ≠ 0
  mu_total :
    ∀ (i : Ag) (w : W),
      conditionalize_mu m i w E (m.R i w) = 1
  mu_empty :
    ∀ (i : Ag) (w : W),
      conditionalize_mu m i w E [] = 0

/--
Return a new model after conditioning on evidence `E`.

Unlike the previous prototype definition, this constructor is logically safe:
normalization is supplied by an explicit `ConditionalizationAdmissible` proof
rather than postulated for arbitrary evidence, including zero-mass evidence.
Only the probability measure is changed.
-/
def conditionalize {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (h : ConditionalizationAdmissible m E) : Model W Ag Atom :=
  { m with
    mu := fun i w => conditionalize_mu m i w E
    mu_total := h.mu_total
    mu_empty := h.mu_empty
  }

end PEL4
