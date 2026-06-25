import FourNPEL

/-!
# Fallstudie 4: Epistemische Explosion (Ex Falso Quodlibet)

Führt ein widersprüchlicher Glaube B(p ∧ ¬p) dazu, dass man alles glaubt, B(q)?
Wir modellieren eine Welt, in der p ein ontologischer Glut ist (P_B = 1), 
sodass B(p ∧ ¬p) ein epistemischer Glut (b) wird. 
Gleichzeitig ist q strikt falsch (F).

Wir überprüfen, welcher Validitätsstandard die epistemische Explosion verhindert.
-/

namespace Fallstudien.ExFalso

open FourNPEL

/-- Modell: p ist Glut, q ist strikt Falsch. 
Wir können das abbilden, indem wir eine Region haben, in der p den Wert B hat und q den Wert F. -/
def M_exfalso : Model := {
  PT := 0
  PB := 1
  PN := 0
  PF := 0
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

def c_thresh : ℚ := 4/5 -- 0.8

/-- p ist in Region B ein Glut. -/
def p : PropVal := ⟨Val4.T, Val4.B, Val4.N, Val4.F⟩

/-- q ist überall strikt Falsch. -/
def q : PropVal := ⟨Val4.F, Val4.F, Val4.F, Val4.F⟩

def premise := Belief M_exfalso c_thresh (p ⊓ (∼p))
def conclusion := Belief M_exfalso c_thresh q

#eval premise.vB     -- Ergibt B (Glut)
#eval conclusion.vB  -- Ergibt F (False)

-- Validitätstests
#eval isGloballyValid_ST premise conclusion -- True (vacuous truth, da Prämisse nicht Strikt True ist)
#eval isGloballyValid_LP premise conclusion -- False (Prämisse toleriert, Konklusion nicht! Explosion VERHINDERT!)

end Fallstudien.ExFalso
