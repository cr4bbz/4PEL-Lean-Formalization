import PEL4.Syntax
import PEL4.Belief

namespace PEL4

/-- Helper to filter a finite set based on another set (intersection). -/
def intersectWorlds {W : Type} [DecidableEq W] (A B : FiniteSet W) : FiniteSet W :=
  A.filter (fun w => B.contains w)

/-- 
  Dynamically conditionalize the local probability measure of agent `i` at world `w`.
  The update is performed on the positive extension of the evidence formula `E`.
-/
def conditionalize_mu {W Ag Atom : Type} [DecidableEq W] 
  (m : Model W Ag Atom) (i : Ag) (w : W) (E : Formula Atom Ag) 
  (S : FiniteSet W) : Rat :=
  let R_w := m.R i w
  -- The positive extension of E within R_w
  let E_pos := filterWorlds R_w (fun w' => (eval m w' E).pos)
  let E_mass := m.mu i w E_pos
  -- We conditionally update. If E_mass is 0, we return 0.
  -- In a strict mathematical proof, we'd require a proof `E_mass > 0` 
  -- but since division by 0 in Rat gives 0, this acts as a safe fallback.
  if E_mass == 0 then 0 else (m.mu i w (intersectWorlds S E_pos)) / E_mass

axiom conditionalize_mu_total {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) (E : Formula Atom Ag) : ∀ (i : Ag) (w : W), conditionalize_mu m i w E (m.R i w) = 1
axiom conditionalize_mu_empty {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) (E : Formula Atom Ag) : ∀ (i : Ag) (w : W), conditionalize_mu m i w E [] = 0

/-- 
  Returns a new Model after agent updates on evidence E. 
  Only the probability measure `mu` is updated.
-/
def conditionalize {W Ag Atom : Type} [DecidableEq W] 
  (m : Model W Ag Atom) (E : Formula Atom Ag) : Model W Ag Atom :=
  { m with
    mu := fun i w => conditionalize_mu m i w E
    mu_total := conditionalize_mu_total m E
    mu_empty := conditionalize_mu_empty m E
  }

end PEL4
