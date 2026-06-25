import PEL4.ProductUpdate
import PEL4.Belief

namespace PEL4

-- A simple string-based agent and atom setup
def Ag := String
def Atom := String

-- We define an agent "A"
def A : Ag := "A"

-- A paradoxical sentence: "This announcement is false."
-- In our setup, this translates to an action whose precondition is a Liar paradox.
-- So `pre(act) = B` (Glut).
def LiarPrecondition : Formula String String := Formula.prop "Liar"

def act_liar : String := "announce_liar"

def paradoxicalActionModel : ActionModel String String String :=
  {
    events := [act_liar]
    sim := fun _ a => [a] -- perfect observability
    pre := fun _ => LiarPrecondition
    plausibility := fun _ _ => 1 -- Only one action, plausibility 1
  }

-- A base model where the Liar atom evaluates to B
def baseWorld : String := "w0"

def base_mu : FiniteSet String -> Rat
| S => if S.contains baseWorld then 1 else 0

def baseModel : Model String String String :=
  {
    worlds := [baseWorld]
    R := fun _ _ => [baseWorld]
    mu := fun _ _ => base_mu
    val := fun _ _ => { pos := true, neg := true } -- Evaluate everything to B
    c := fun _ => 3/4
    mu_total := by
      intro _ _
      rfl
    mu_empty := by
      intro _ _
      rfl
    c_gt_half := by
      intro _
      native_decide
    c_le_one := by
      intro _
      native_decide
  }

-- The product update
def updatedModel := productUpdateModel baseModel paradoxicalActionModel

-- Let's check the evaluation of the positive extension of the precondition in the base model.
#eval! (eval baseModel baseWorld LiarPrecondition).pos -- Should be true

-- Because the precondition has `pos = true`, the pair `(w0, announce_liar)` survives the update.
#eval! updatedModel.worlds -- Should be [("w0", "announce_liar")]

-- The evaluation of the Liar atom in the updated model remains a Glut
#eval! updatedModel.val ("w0", act_liar) "Liar" -- Should be { pos := true, neg := true }

end PEL4
