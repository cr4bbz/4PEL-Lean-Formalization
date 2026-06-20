import PEL4.Model
import PEL4.Belief
import PEL4.Syntax

namespace PEL4.Paradoxes

inductive C_Atom where
  | p
deriving DecidableEq, Repr

inductive C_Agent where
  | a -- Paranoid agent (low threshold)
  | b -- Strict agent (high threshold)
deriving DecidableEq, Repr

inductive C_World where
  | w1 | w2
deriving DecidableEq, Repr

-- w1 is an ontological glut (B)
-- w2 is a gap (N)
def cart_val : C_World → C_Atom → FDEValue
| C_World.w1, C_Atom.p => FDEValue.B
| C_World.w2, C_Atom.p => FDEValue.N

-- P(w1) = 0.7, P(w2) = 0.3
def cart_mu : FiniteSet C_World → Rat
| S => 
  let p1 := if S.contains C_World.w1 then (7:Rat)/10 else 0
  let p2 := if S.contains C_World.w2 then (3:Rat)/10 else 0
  p1 + p2

axiom cart_mu_total : ∀ (_ : C_Agent) (_ : C_World), cart_mu [C_World.w1, C_World.w2] = 1
axiom cart_mu_empty : ∀ (_ : C_Agent) (_ : C_World), cart_mu [] = 0

-- Agent a has threshold 0.6
-- Agent b has threshold 0.9
def cart_c : C_Agent → Rat
| C_Agent.a => (6:Rat)/10
| C_Agent.b => (9:Rat)/10

axiom cart_c_gt_half : ∀ i, cart_c i > 1/2
axiom cart_c_le_one : ∀ i, cart_c i ≤ 1

def CartographyModel : Model C_World C_Agent C_Atom :=
  { worlds := [C_World.w1, C_World.w2]
  , R := fun _ _ => [C_World.w1, C_World.w2]
  , mu := fun _ _ => cart_mu
  , val := cart_val
  , c := cart_c
  , mu_total := cart_mu_total
  , mu_empty := cart_mu_empty
  , c_gt_half := cart_c_gt_half
  , c_le_one := cart_c_le_one
  }

def cart_p := Formula.prop C_Atom.p (Ag := C_Agent)

-- 1. Topological Boundary for Agent A (Paranoid)
-- Positive mass = 0.7 >= 0.6. Negative mass = 0.7 >= 0.6.
-- Agent a crosses the phase transition! B_a(p) = B.
def B_a_p := Formula.bel C_Agent.a cart_p
#eval! eval CartographyModel C_World.w1 B_a_p

-- 2. Topological Boundary for Agent B (Strict)
-- Positive mass = 0.7 < 0.9. Negative mass = 0.7 < 0.9.
-- Agent b remains below the boundary! B_b(p) = N.
def B_b_p := Formula.bel C_Agent.b cart_p
#eval! eval CartographyModel C_World.w1 B_b_p

-- 3. The Collapse of the Meta-Glut Hierarchy
-- Since Agent a's belief B_a(p) is B at ALL worlds, its probability mass is 1.
-- So B_a(B_a(p)) also evaluates to B.
-- This proves the singularity S_1 = S_infinity for isolated agents.
def B_a_B_a_p := Formula.bel C_Agent.a B_a_p
#eval! eval CartographyModel C_World.w1 B_a_B_a_p

end PEL4.Paradoxes
