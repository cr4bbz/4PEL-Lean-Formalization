import PEL4.Syntax
import PEL4.Belief

namespace PEL4

/-- The set of worlds where the formula explicitly evaluates to the Glut state (B). -/
def ontological_glut_set {W Ag Atom : Type} [DecidableEq W] 
  (m : Model W Ag Atom) (phi : Formula Atom Ag) : FiniteSet W :=
  m.worlds.filter (fun w => eval m w phi == FDEValue.B)

/-- The set of worlds where the agent `i` believes both the formula and its negation (Epistemic Glut). -/
def epistemic_glut_set {W Ag Atom : Type} [DecidableEq W] 
  (m : Model W Ag Atom) (i : Ag) (phi : Formula Atom Ag) : FiniteSet W :=
  m.worlds.filter (fun w => eval m w (Formula.bel i phi) == FDEValue.B)

/-- 
  The Local Glut Conservation Hypothesis (H5).
  It states that for any agent `i` at any world `w`, the probability mass of the 
  epistemic gluts within their accessible worlds is strictly bounded by the 
  probability mass of the ontological gluts within those worlds.
  
  Since P_B >= 2c - 1 is the boundary for a *single* epistemic glut, the global measure 
  of epistemic gluts might be bounded proportionally.
  As a starting point, we define the property that Epistemic Gluts cannot exceed 
  Ontological Gluts (Strong Conservation).
-/
def satisfies_strong_conservation {W Ag Atom : Type} [DecidableEq W] 
  (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Prop :=
  let O_G := ontological_glut_set m phi
  let E_G := epistemic_glut_set m i phi
  -- The agent's subjective probability of experiencing an epistemic glut
  -- is less than or equal to the subjective probability of the objective glut.
  m.mu i w E_G ≤ m.mu i w O_G

end PEL4
