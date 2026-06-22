namespace PEL4

/-- Weatherson's Menu-dependent Choice Theory.
    A Menu is represented as a List (a finite collection of options). -/
abbrev Menu (α : Type) := List α

/-- A choice function takes a menu and returns the subset of choiceworthy options. -/
def ChoiceFn (α : Type) := Menu α → Menu α

/-- Weatherson's Expansion property (γ):
    If x is choiceworthy in S and x is choiceworthy in T, 
    it must be choiceworthy in S ∪ T. -/
def SatisfiesGamma {α : Type} (C : ChoiceFn α) : Prop :=
  ∀ (x : α) (S T : Menu α), x ∈ C S → x ∈ C T → x ∈ C (S ++ T)

end PEL4
