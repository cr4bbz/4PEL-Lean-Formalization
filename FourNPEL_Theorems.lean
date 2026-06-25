import Mathlib.Tactic.Linarith
import FourNPEL

/-!
# Allgemeine formale Theoreme der 4-NPEL Validitäten

Dieses Modul beweist universelle Eigenschaften der non-bivalenten Validitätsstandards 
ST (Strict-to-Tolerant) und LP (Tolerant-to-Tolerant), unabhängig von konkreten numerischen Modellen.
-/

namespace FourNPEL.Theorems

open FourNPEL

/-- 
  **Theorem: LP verhindert Epistemische Explosion (Ex Falso Quodlibet)**
  Wenn die Prämisse ein Epistemischer Glut (oder Strikt Wahr) ist, also toleriert wird (`pos = true`), 
  und die Konklusion strikt falsch (oder ein Gap) ist, also nicht toleriert wird (`pos = false`),
  dann ist der Schluss unter LP-Validität immer ungültig.
  Dies blockiert Ex Falso Quodlibet für paradoxe Agenten.
-/
theorem lp_blocks_epistemic_explosion (prem conc : Val4) 
  (h_prem_pos : prem.pos = true) 
  (h_conc_pos : conc.pos = false) : 
  isValid_LP prem conc = false := by
  unfold isValid_LP
  simp [h_prem_pos, h_conc_pos]

/--
  **Theorem: ST erhält klassische Wahrheit**
  Wenn die Prämisse strikt wahr ist (`Val4.T`) und die Konklusion ebenfalls strikt wahr ist (`Val4.T`),
  dann ist der Schluss unter ST-Validität immer gültig.
  Dies garantiert, dass klassische (bivalente) Schlüsse in paradoxiefreien Welten erhalten bleiben.
-/
theorem st_preserves_classical_truth : 
  isValid_ST Val4.T Val4.T = true := by
  unfold isValid_ST
  rfl

/--
  **Theorem: ST toleriert den Übergang von Wahrheit zu Gaps**
  Wie im Preface-Paradoxon beobachtet, verbietet ST *nur* den Übergang von T nach F.
  Der Übergang von Strikt Wahr (T) zu einem Epistemischen Gap (N) ist unter ST gültig!
-/
theorem st_allows_gaps_from_truth :
  isValid_ST Val4.T Val4.N = true := by
  unfold isValid_ST
  rfl

/--
  **Globale Erweiterung: LP blockiert globale Explosion**
  Wenn in irgendeiner Region die Prämisse positiven Support hat, 
  die Konklusion aber nicht, schlägt die globale LP-Validität fehl.
-/
theorem global_lp_blocks_explosion (prem conc : PropVal)
  (h_prem_pos : prem.vT.pos = true)
  (h_conc_pos : conc.vT.pos = false) :
  isGloballyValid_LP prem conc = false := by
  unfold isGloballyValid_LP
  have h_local : isValid_LP prem.vT conc.vT = false := lp_blocks_epistemic_explosion prem.vT conc.vT h_prem_pos h_conc_pos
  simp [h_local]

end FourNPEL.Theorems
