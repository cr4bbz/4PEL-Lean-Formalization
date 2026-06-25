import PEL4.Model
import PEL4.Syntax

namespace PEL4

/-- Epistemic Action Model representing information flow and updates. -/
structure ActionModel (Act Ag Atom : Type) [DecidableEq Act] where
  /-- The set of all possible action events. -/
  events : FiniteSet Act
  /-- The indistinguishability relation for each agent over actions. -/
  sim : Ag → Act → FiniteSet Act
  /-- The precondition for each action (a 4-PEL formula). -/
  pre : Act → Formula Atom Ag
  /-- The prior probability / plausibility of each action for a given agent. -/
  plausibility : Ag → Act → Rat
  
end PEL4
