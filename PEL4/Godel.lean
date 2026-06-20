import PEL4.Model
import PEL4.Belief
import PEL4.Syntax

namespace PEL4.Godel

inductive G_Atom where
  | G
deriving DecidableEq, Repr

inductive G_Agent where
  | a
deriving DecidableEq, Repr

inductive G_World where
  | w
deriving DecidableEq, Repr

-- To satisfy the Diagonal Lemma structurally without complex arithmetic,
-- we construct a model where G acts as its own fixpoint.
-- We assign the Glut state (B) to G and test if it is a stable fixpoint
-- for the Gödel sentence equivalence: G ↔ ¬B_a(G).
def godel_val : G_World → G_Atom → FDEValue
| _, _ => FDEValue.B

-- Strict certainty model: the agent considers w the only possible world.
def godel_mu : FiniteSet G_World → Rat
| S => if S.contains G_World.w then 1 else 0

axiom godel_mu_total : ∀ (_ : G_Agent) (_ : G_World), godel_mu [G_World.w] = 1
axiom godel_mu_empty : ∀ (_ : G_Agent) (_ : G_World), godel_mu [] = 0
-- We use c = 1 to represent strict "Beweisbarkeit" (Provability).
axiom godel_c_gt_half : ∀ (_ : G_Agent), (1:Rat) > 1/2
axiom godel_c_le_one : ∀ (_ : G_Agent), (1:Rat) ≤ 1

def GodelModel : Model G_World G_Agent G_Atom :=
  { worlds := [G_World.w]
  , R := fun _ _ => [G_World.w]
  , mu := fun _ _ => godel_mu
  , val := godel_val
  , c := fun _ => 1 
  , mu_total := godel_mu_total
  , mu_empty := godel_mu_empty
  , c_gt_half := godel_c_gt_half
  , c_le_one := godel_c_le_one
  }

def G := Formula.prop G_Atom.G (Ag := G_Agent)
def B_G := Formula.bel G_Agent.a G
def not_B_G := Formula.not B_G

-- Let's evaluate the right-hand side of the Diagonal Lemma: ¬B_a(G).
-- In GodelModel, G evaluates to B.
-- Since the probability of G being positive is 1 (>= c), and negative is 1 (>= c),
-- B_a(G) evaluates to B.
-- Consequently, ¬B_a(G) also evaluates to B.
#eval! eval GodelModel G_World.w not_B_G

-- We have verified computationally that:
-- v(G) = B
-- v(¬B_a(G)) = B
-- Thus, v(G) = v(¬B_a(G)) holds. The Glut state is the stable fixpoint 
-- of the Epistemic Gödel Sentence. The system is "Inconsistent" (Glut)
-- rather than "Incomplete" (Gap) under these boundary conditions.

end PEL4.Godel
