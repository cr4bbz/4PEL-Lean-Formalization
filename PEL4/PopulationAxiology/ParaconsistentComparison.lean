import PEL4.Evidence
import PEL4.PopulationAxiology.FiniteFineGrainedness

namespace PEL4.PopulationAxiology

/-!
# Four-valued population comparison

A classical impossibility proof treats support for a comparison and support
for its rejection as a metatheoretic inconsistency.  This module records the
same pair of judgements in the existing Belnap-Dunn carrier.  It does not claim
that the original impossibility theorem is false; it changes the target from a
consistent total ordering to a non-explosive evidence semantics for ordering
claims.
-/

universe u

/-- Turn independent positive and negative comparison relations into a 4-PEL
value for the claim that `x` is at least as good as `y`. -/
def comparisonValue
    {A : Type u}
    (supports rejects : A -> A -> Prop)
    [DecidableRel supports] [DecidableRel rejects]
    (x y : A) : FDEValue :=
  { pos := decide (supports x y)
  , neg := decide (rejects x y) }

/-- Simultaneous support and rejection is represented by the glut value `B`. -/
theorem comparisonValue_eq_B
    {A : Type u}
    (supports rejects : A -> A -> Prop)
    [DecidableRel supports] [DecidableRel rejects]
    {x y : A}
    (hPos : supports x y)
    (hNeg : rejects x y) :
    comparisonValue supports rejects x y = FDEValue.B := by
  simp [comparisonValue, hPos, hNeg, FDEValue.B]

/-- The central bridge theorem: finite-chain transport may derive the positive
side of a comparison while an independent adequacy condition supplies its
rejection.  The result is an axiological glut, not arbitrary derivability. -/
theorem finite_chain_axiological_glut
    {A : Type u}
    {slight supports rejects : A -> A -> Prop}
    [DecidableRel supports] [DecidableRel rejects]
    (supports_refl : forall x, supports x x)
    (supports_trans : forall {x y z},
      supports x y -> supports y z -> supports x z)
    (local_transport : forall {x y}, slight x y -> supports x y)
    {x y : A}
    (hChain : FiniteStepChain slight x y)
    (hReject : rejects x y) :
    comparisonValue supports rejects x y = FDEValue.B := by
  apply comparisonValue_eq_B supports rejects
  · exact hChain.transport supports_refl supports_trans local_transport
  · exact hReject

/-!
## Non-triviality witness

One comparison can be glutty while an unrelated claim remains unsupported.
This tiny witness is the exact non-explosion boundary needed before richer
axiological axioms are introduced.
-/

inductive ResearchClaim
  | targetComparison
  | unrelated
  deriving DecidableEq, Repr

def nonExplosiveWitness : ResearchClaim -> FDEValue
  | .targetComparison => FDEValue.B
  | .unrelated => FDEValue.N

theorem target_comparison_is_glut :
    nonExplosiveWitness .targetComparison = FDEValue.B :=
  rfl

theorem unrelated_claim_not_true :
    nonExplosiveWitness .unrelated ≠ FDEValue.T := by
  native_decide

end PEL4.PopulationAxiology
