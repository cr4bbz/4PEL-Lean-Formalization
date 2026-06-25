import FourNPEL

/-!
# Fallstudie 1: Das Lügner-Paradoxon (The Liar Paradox)

"Dieser Satz ist falsch." (p)

Klassisch: $B(p) \implies B(\sim p)$ führt zu einer Explosion.
In 4-NPEL: Wenn $p$ als ontologischer Glut ($B$) modelliert wird,
beweisen wir, dass $B(p) \implies B(\sim p)$ unter Strict-to-Tolerant (ST)
Validität ein gültiger Schluss ist, ohne das System inkonsistent zu machen.
-/

namespace Fallstudien.LiarParadox

open FourNPEL

/-- Wir definieren ein Modell für den Lügner, das eine extrem hohe Wahrscheinlichkeit für einen Glut (B) hat. -/
def M_liar : Model := {
  PT := 0.1
  PB := 0.8
  PN := 0.1
  PF := 0.0
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

def c_thresh : ℚ := 4/5 -- 0.8

/-- Der Liar-Satz `p` -/
def p := p_var

/-- Prämisse: Der Agent glaubt den Liar-Satz -/
def premise := Belief M_liar c_thresh p

/-- Konklusion: Der Agent glaubt die Negation des Liar-Satzes -/
def conclusion := Belief M_liar c_thresh (∼p)

/- 
Evaluation: Die Inferenz $B(p) \implies B(\sim p)$ ist im Liar-Modell unter ST-Validität *gültig*.
Dies zeigt, dass 4-NPEL den Paradox-Schluss toleriert, ohne ihn als "Strict False" (F) abzuweisen.
-/
#eval isGloballyValid_ST premise conclusion

end Fallstudien.LiarParadox
