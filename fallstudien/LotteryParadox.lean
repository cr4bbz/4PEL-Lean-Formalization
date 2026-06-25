import FourNPEL

/-!
# Fallstudie 2: Das Lotterie-Paradoxon (Lottery Paradox)

In einer Lotterie glaubt man für jedes einzelne Los, dass es verliert (B(p1) und B(p2)).
Die klassische deduktive Abgeschlossenheit verlangt dann B(p1 ∧ p2),
was bedeutet, man glaubt, dass überhaupt kein Los gewinnt. 
In 4-NPEL sinkt die Aggregation unter den Schwellenwert c.
Wir zeigen, dass die Inferenz B(p1) ∧ B(p2) => B(p1 ∧ p2)
in allen nicht-trivialen Validitäts-Standards FALSCH (INVALID) ist, 
wenn die Wahrscheinlichkeiten gleichverteilt sind.
-/

namespace Fallstudien.LotteryParadox

open FourNPEL

/-- 3 Welten Modell. Jede Welt repräsentiert das Gewinnen eines Loses (1, 2, 3). -/
def M_lottery : Model := {
  PT := 1/3
  PB := 1/3
  PN := 1/3
  PF := 0.0
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

def c_thresh : ℚ := 6/10 -- 0.6

/-- p1: Los 1 verliert. Es ist falsch in Welt 1 (Region T), wahr in Region B und N. -/
def p1 : PropVal := ⟨Val4.F, Val4.T, Val4.T, Val4.F⟩

/-- p2: Los 2 verliert. Es ist wahr in Region T, falsch in Region B, wahr in Region N. -/
def p2 : PropVal := ⟨Val4.T, Val4.F, Val4.T, Val4.F⟩

def premise := (Belief M_lottery c_thresh p1) ⊓ (Belief M_lottery c_thresh p2)
def conclusion := Belief M_lottery c_thresh (p1 ⊓ p2)

#eval premise.vT
#eval conclusion.vT

#eval isGloballyValid_ST premise conclusion
#eval isGloballyValid_LP premise conclusion
#eval isGloballyValid_SS premise conclusion

end Fallstudien.LotteryParadox
