import PEL4.Conservation
import PEL4.Paradoxes.Liar

namespace PEL4.Paradoxes

open PEL4

-- Let's test the Strong Conservation Hypothesis on the LiarModel.
-- In LiarModel, c = 3/4. 
-- P(wT) = 1/4, P(wF) = 1/4, P(wB) = 1/2.
-- For the atom 'p':
-- Positive mass = P(wT) + P(wB) = 3/4 >= c.
-- Negative mass = P(wF) + P(wB) = 3/4 >= c.
-- Thus, B_a(p) evaluates to B at ALL worlds.

def O_G := ontological_glut_set LiarModel (Formula.prop LiarAtom.p)
def E_G := epistemic_glut_set LiarModel Agent.a (Formula.prop LiarAtom.p)

-- Mass of Ontological Glut Set:
-- Expected: 1/2
#eval! LiarModel.mu Agent.a World.wT O_G

-- Mass of Epistemic Glut Set:
-- Expected: 1 (because B_a(p) = B globally)
#eval! LiarModel.mu Agent.a World.wT E_G

-- Result: mu(E_G) = 1, mu(O_G) = 1/2.
-- Thus, mu(E_G) <= mu(O_G) is FALSE!
-- This proves that epistemic contradictions CAN amplify beyond ontological contradictions
-- once the phase transition boundary (P_B >= 2c - 1) is crossed.

end PEL4.Paradoxes
