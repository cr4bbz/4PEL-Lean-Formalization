import PEL4.Syntax
import PEL4.Evidence

namespace PEL4

/-!
Probabilistic evidence masses.

These helpers expose the geometry behind the threshold belief operator.  They
measure the accessible probability mass on which a formula has positive
evidence, negative evidence, glutty evidence, or no evidence.
-/

def massWhere {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : Formula Atom Ag) (p : FDEValue -> Bool) : Rat :=
  m.mu i w ((m.R i w).filter (fun w' => p (eval m w' phi)))

def P_pos {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Rat :=
  massWhere m i w phi hasPositiveEvidence

def P_neg {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Rat :=
  massWhere m i w phi hasNegativeEvidence

def P_glut {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Rat :=
  massWhere m i w phi isGlut

def P_gap {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Rat :=
  massWhere m i w phi isGap

def P_classical {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Rat :=
  massWhere m i w phi isClassical

end PEL4
