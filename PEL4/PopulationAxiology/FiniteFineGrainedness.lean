namespace PEL4.PopulationAxiology

/-!
# Finite Fine-Grainedness as finite path connectivity

This module isolates the structural assumption used by finite-chain
impossibility arguments in population axiology.  A relation `slight x y`
records that the move from welfare level `x` to welfare level `y` is small.
`FiniteStepChain slight x y` is the finite reflexive-transitive closure of
that relation.

The definition

```text
FiniteFineGrained slight := every pair is joined by a finite slight-step chain
```

therefore states a graph-connectivity property.  The transport theorem below
makes the hidden proof mechanism explicit: a reflexive and transitive global
comparison that accepts every local step accepts every comparison connected by
such a chain.
-/

universe u v

/-- A finite chain of `slight` steps, including the empty chain. -/
inductive FiniteStepChain {W : Type u} (slight : W -> W -> Prop) : W -> W -> Prop
  | refl (x : W) : FiniteStepChain slight x x
  | cons {x y z : W} :
      slight x y ->
      FiniteStepChain slight y z ->
      FiniteStepChain slight x z

namespace FiniteStepChain

/-- Finite step chains compose. -/
theorem trans
    {W : Type u} {slight : W -> W -> Prop} {x y z : W}
    (hxy : FiniteStepChain slight x y)
    (hyz : FiniteStepChain slight y z) :
    FiniteStepChain slight x z := by
  induction hxy with
  | refl _ => exact hyz
  | cons hStep _ ih => exact .cons hStep (ih hyz)

/-- Any invariant preserved by slight steps is preserved along their finite
closure.  This is the component-separation principle used by lexical
countermodels. -/
theorem preserves
    {W : Type u} {C : Type v} {slight : W -> W -> Prop}
    (colour : W -> C)
    (hStep : forall {x y}, slight x y -> colour x = colour y)
    {x y : W}
    (hxy : FiniteStepChain slight x y) :
    colour x = colour y := by
  induction hxy with
  | refl _ => rfl
  | cons hLocal _ ih => exact Eq.trans (hStep hLocal) ih

/-- Local comparison judgements propagate through a finite small-step chain
when the global comparison is reflexive and transitive. -/
theorem transport
    {W : Type u}
    {slight comparison : W -> W -> Prop}
    (comparison_refl : forall x, comparison x x)
    (comparison_trans : forall {x y z},
      comparison x y -> comparison y z -> comparison x z)
    (local_transport : forall {x y}, slight x y -> comparison x y)
    {x y : W}
    (hxy : FiniteStepChain slight x y) :
    comparison x y := by
  induction hxy with
  | refl x => exact comparison_refl x
  | cons hLocal _ ih =>
      exact comparison_trans (local_transport hLocal) ih

end FiniteStepChain

/-- Finite Fine-Grainedness: all welfare levels lie in one finite-path
component of the slight-difference graph. -/
def FiniteFineGrained {W : Type u} (slight : W -> W -> Prop) : Prop :=
  forall x y, FiniteStepChain slight x y

/-- Under Finite Fine-Grainedness, local transport plus transitivity becomes a
global comparison principle. -/
theorem global_transport_of_finiteFineGrained
    {W : Type u}
    {slight comparison : W -> W -> Prop}
    (hFFG : FiniteFineGrained slight)
    (comparison_refl : forall x, comparison x x)
    (comparison_trans : forall {x y z},
      comparison x y -> comparison y z -> comparison x z)
    (local_transport : forall {x y}, slight x y -> comparison x y)
    (x y : W) :
    comparison x y :=
  (hFFG x y).transport comparison_refl comparison_trans local_transport

/-!
## A minimal lexical countermodel

The amount coordinate may vary inside either tier, but a slight move never
changes tier.  Hence no finite chain can connect a higher-tier life to a
lower-tier life.  This is the abstract obstruction exploited by lexical
population axiologies; no substantive interpretation of either tier is built
into the theorem.
-/

inductive LexicalTier
  | higher
  | lower
  deriving DecidableEq, Repr

structure LexicalWelfare where
  tier : LexicalTier
  amount : Nat
  deriving DecidableEq, Repr

/-- The deliberately weak structural core of a lexical small-step relation:
small changes stay inside one lexical tier. -/
def sameTierSlight (x y : LexicalWelfare) : Prop :=
  x.tier = y.tier

theorem sameTierSlight_preserves_tier {x y : LexicalWelfare}
    (h : sameTierSlight x y) :
    x.tier = y.tier :=
  h

/-- A two-tier lexical welfare space is not finitely fine-grained when every
slight step preserves tier. -/
theorem sameTierSlight_not_finitely_fine_grained :
    ¬ FiniteFineGrained sameTierSlight := by
  intro hFFG
  let high : LexicalWelfare := { tier := .higher, amount := 0 }
  let low : LexicalWelfare := { tier := .lower, amount := 0 }
  have hChain : FiniteStepChain sameTierSlight high low := hFFG high low
  have hTier : high.tier = low.tier :=
    FiniteStepChain.preserves
      (fun x => x.tier) sameTierSlight_preserves_tier hChain
  have hImpossible : LexicalTier.higher = LexicalTier.lower := by
    simpa [high, low] using hTier
  cases hImpossible

end PEL4.PopulationAxiology
