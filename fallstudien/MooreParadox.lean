import FourNPEL

/-!
# Fallstudie 3: Mooresches Paradoxon (Moore's Paradox)

"Es regnet, aber ich glaube nicht, dass es regnet" -> p ∧ ¬B(p)

Ein Agent kann diesen Satz klassisch nicht rational glauben: B(p ∧ ¬B(p)) ist inkonsistent.
Wir untersuchen, wie 4-NPEL das verarbeitet.
In einer rein bivalenten Welt (P(T)=1) ergibt sich Strikt False (F).
In einer Welt, in der p ein ontologischer Glut ist (P(B)=1), wird auch der Glaube
an Moores Satz zu einem epistemischen Glut.
-/

namespace Fallstudien.MooreParadox

open FourNPEL

/-- Modell 1: Klassische bivalente Welt -/
def M_classic : Model := {
  PT := 1
  PB := 0
  PN := 0
  PF := 0
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

/-- Modell 2: Paradoxe Glut-Welt -/
def M_glut : Model := {
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
def p := p_var

-- Moores Satz in Modell 1
def moore_classic := p ⊓ (∼(Belief M_classic c_thresh p))
def belief_moore_classic := Belief M_classic c_thresh moore_classic

-- Moores Satz in Modell 2
def moore_glut := p ⊓ (∼(Belief M_glut c_thresh p))
def belief_moore_glut := Belief M_glut c_thresh moore_glut

#eval belief_moore_classic.vT -- Ergibt F (False)
#eval belief_moore_glut.vB    -- Ergibt B (Glut)

end Fallstudien.MooreParadox
