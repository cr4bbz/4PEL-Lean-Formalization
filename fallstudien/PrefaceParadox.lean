import FourNPEL

/-!
# Fallstudie 5: Das Preface-Paradoxon (Vorwort-Paradoxon)

In einem Buch mit n Aussagen glaubt der Autor an jede einzelne Aussage (hohe Wahrscheinlichkeit), 
aber er glaubt nicht an die Konjunktion aller Aussagen (da ein Fehler wahrscheinlich ist).
Wir modellieren 3 Aussagen s1, s2, s3. Die Wahrscheinlichkeit, dass das ganze Buch fehlerfrei ist,
beträgt P(F) = 0.7. Die Wahrscheinlichkeit für einen individuellen Fehler ist jeweils 0.1 in T, B, N.
Der Lockesche Schwellenwert ist c = 0.85.
-/

namespace Fallstudien.PrefaceParadox

open FourNPEL

/-- 4 Regionen als 4 exklusive Zustände des Buches. 
Region F: Buch komplett fehlerfrei (0.7).
Region T, B, N: Jeweils ein Fehler in s1, s2, s3 (je 0.1). -/
def M_preface : Model := {
  PT := 1/10
  PB := 1/10
  PN := 1/10
  PF := 7/10
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

def c_thresh : ℚ := 85/100

/-- s1 ist korrekt in B, N, F. Fehler in T. -/
def s1 : PropVal := ⟨Val4.F, Val4.T, Val4.T, Val4.T⟩

/-- s2 ist korrekt in T, N, F. Fehler in B. -/
def s2 : PropVal := ⟨Val4.T, Val4.F, Val4.T, Val4.T⟩

/-- s3 ist korrekt in T, B, F. Fehler in N. -/
def s3 : PropVal := ⟨Val4.T, Val4.T, Val4.F, Val4.T⟩

def b_s1 := Belief M_preface c_thresh s1
def b_s2 := Belief M_preface c_thresh s2
def b_s3 := Belief M_preface c_thresh s3

def premise := PropVal.and b_s1 (PropVal.and b_s2 b_s3)
def conclusion := Belief M_preface c_thresh (PropVal.and s1 (PropVal.and s2 s3))

#eval premise.vT    -- Ergibt T (Strict True)
#eval conclusion.vT -- Ergibt N (Epistemic Gap), da pos=0.7 < 0.85 und neg=0.3 < 0.85

-- Validitätstests
#eval isGloballyValid_ST premise conclusion -- True (T -> N ist unter ST erlaubt)
#eval isGloballyValid_LP premise conclusion -- False (Toleriert -> Nicht toleriert)
#eval isGloballyValid_SS premise conclusion -- False (Strikt -> Nicht strikt)

end Fallstudien.PrefaceParadox
