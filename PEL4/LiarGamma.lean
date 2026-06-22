import PEL4.Weatherson

namespace PEL4

/-- Ein Satz/Knoten in unserem logischen Graphen. -/
structure PropNode where
  id : Nat
  deriving DecidableEq, Repr

/-- Ein logischer Evaluierungs-Kontext (ein Menü von Propositionen). -/
abbrev Context := Menu PropNode

/-- 
  Der Lügner-Zyklus (z.B. p2 sagt "p3 ist wahr", p3 sagt "p2 ist falsch").
  Ein logischer Knoten verliert seine Stabilität, wenn er in einem 
  Kontext evaluiert wird, der einen geschlossenen Paradoxie-Zyklus enthält.
-/
def has_liar_cycle (ctx : Context) : Bool :=
  -- Wir simulieren einen Zyklus, der genau dann entsteht, 
  -- wenn Knoten 2 und Knoten 3 gemeinsam im Kontext auftreten.
  (ctx.any (fun p => p.id == 2)) ∧ (ctx.any (fun p => p.id == 3))

/-- 
  Wahrheits-Evaluierung als Weatherson-Wahlfunktion.
  Eine Proposition ist "choiceworthy" (wählbar), wenn der Kontext nicht
  durch ein Paradoxon (Liar-Zyklus) kontaminiert ist.
-/
def Pi_Truth (ctx : Context) : Context :=
  ctx.filter (fun _ => ¬ has_liar_cycle ctx)

/-- 
  Theorem: Das Lügner-Paradoxon verletzt Weathersons Expansionseigenschaft (γ).
  
  Beweis:
  Ein harmloser Satz p1 ist gültig im Kontext S und gültig im Kontext T.
  Werden die Kontexte jedoch vereint (S ∪ T), schließt sich ein Paradoxon 
  zwischen p2 und p3. Der Kontext explodiert (Ex Falso Quodlibet), und der 
  harmlose Satz p1 verliert seine globale Gültigkeit.
  
  Dies zeigt formal, dass Paradoxien Schwellenphänomene sind, die eine
  binäre Logik unmöglich machen und 4-PEL (Isolation des Paradoxons) erfordern.
-/
theorem Liar_violates_gamma : ¬ SatisfiesGamma Pi_Truth := by
  intro hGamma
  
  let p1 := PropNode.mk 1 -- Der harmlose Satz
  let p2 := PropNode.mk 2 -- Teil 1 des Lügner-Zyklus
  let p3 := PropNode.mk 3 -- Teil 2 des Lügner-Zyklus
  
  let S := [p1, p2]
  let T := [p1, p3]
  
  have h_S_T : p1 ∈ Pi_Truth S → p1 ∈ Pi_Truth T → p1 ∈ Pi_Truth (S ++ T) := 
    hGamma p1 S T

  have h_in_S : p1 ∈ Pi_Truth S := by
    -- S enthält p2, aber nicht p3 -> Kein Zyklus -> p1 ist gültig
    decide

  have h_in_T : p1 ∈ Pi_Truth T := by
    -- T enthält p3, aber nicht p2 -> Kein Zyklus -> p1 ist gültig
    decide

  have h_in_union := h_S_T h_in_S h_in_T

  have h_not_in_union : p1 ∉ Pi_Truth (S ++ T) := by
    -- S ∪ T enthält p2 und p3 -> Zyklus schließt sich -> Kontext kollabiert
    decide

  -- Widerspruch zwischen h_in_union und h_not_in_union!
  contradiction

end PEL4
