import PEL4.Model

namespace PEL4

/-!
# Finite probability integrity

The original finite 4-PEL `Model` intentionally keeps its probability contract
lightweight: local measures are arbitrary rational-valued functions on the
list-based finite-set representation, with only normalization of the accessible
range and the empty event built into the model structure.

That interface was sufficient for the earlier finite theorem laboratory, but it
is too weak for a strong claim that affine support trajectories are trajectories
of genuine probabilistic models.  This module therefore adds a *separate*,
backwards-compatible integrity layer rather than changing `Model` and breaking
the existing development.

The stronger local contract records the ordinary finite-probability behavior
needed by the next dynamic gates:

* nonnegative mass on accessible events;
* extensionality with respect to set membership rather than list presentation;
* monotonicity under inclusion;
* finite additivity for disjoint events;
* empty-event mass zero;
* accessible total mass one.

Because `FiniteSet` is currently represented by `List`, well-formed events are
also required to be duplicate-free where set-theoretic laws are invoked.
Future weight-generated measures should derive these fields constructively.
-/

/-- Set-like inclusion for the current list representation of finite events. -/
def FiniteEventSubset {W : Type}
    (A B : FiniteSet W) : Prop :=
  ∀ x, x ∈ A → x ∈ B

/-- Extensional equality of finite events, ignoring list order. -/
def FiniteEventExtEq {W : Type}
    (A B : FiniteSet W) : Prop :=
  ∀ x, x ∈ A ↔ x ∈ B

/-- Set-like disjointness for finite events. -/
def FiniteEventDisjoint {W : Type}
    (A B : FiniteSet W) : Prop :=
  ∀ x, x ∈ A → x ∈ B → False

/-- Strong finite-probability laws for one local measure on one accessible
support.  This is an additional semantic contract, not a replacement for the
legacy `ProbMeasure` type. -/
structure FiniteProbabilityIntegrity
    {W : Type}
    (mu : ProbMeasure W)
    (support : FiniteSet W) : Prop where
  support_nodup : support.Nodup
  nonnegative :
    ∀ S : FiniteSet W,
      S.Nodup →
      FiniteEventSubset S support →
      0 ≤ mu S
  extensional :
    ∀ A B : FiniteSet W,
      A.Nodup →
      B.Nodup →
      FiniteEventSubset A support →
      FiniteEventSubset B support →
      FiniteEventExtEq A B →
      mu A = mu B
  monotone :
    ∀ A B : FiniteSet W,
      A.Nodup →
      B.Nodup →
      FiniteEventSubset A B →
      FiniteEventSubset B support →
      mu A ≤ mu B
  add_disjoint :
    ∀ A B : FiniteSet W,
      A.Nodup →
      B.Nodup →
      FiniteEventSubset A support →
      FiniteEventSubset B support →
      FiniteEventDisjoint A B →
      mu (A ++ B) = mu A + mu B
  empty : mu [] = 0
  total : mu support = 1

/-- A legacy 4-PEL model has finite probability integrity when every local
measure satisfies the stronger contract on its accessible range. -/
def ModelProbabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : Prop :=
  ∀ (i : Ag) (w : W),
    FiniteProbabilityIntegrity (m.mu i w) (m.R i w)

/-- Wrapper for developments that should only quantify over models whose local
probabilities satisfy the stronger finite-measure laws.  Existing `Model`
values remain untouched and can be promoted by supplying an integrity proof. -/
structure StrongProbabilityModel
    (W Ag Atom : Type) [DecidableEq W] where
  toModel : Model W Ag Atom
  probability_integrity : ModelProbabilityIntegrity toModel

/-- The stronger contract recovers the legacy empty-event law locally. -/
theorem probabilityIntegrity_empty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : ModelProbabilityIntegrity m)
    (i : Ag) (w : W) :
    m.mu i w [] = 0 := by
  exact (h i w).empty

/-- The stronger contract recovers the legacy normalization law locally. -/
theorem probabilityIntegrity_total
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : ModelProbabilityIntegrity m)
    (i : Ag) (w : W) :
    m.mu i w (m.R i w) = 1 := by
  exact (h i w).total

/-- Every accessible event in an integrity-certified model has nonnegative
mass. -/
theorem probabilityIntegrity_nonnegative
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (S : FiniteSet W)
    (hNoDup : S.Nodup)
    (hSub : FiniteEventSubset S (m.R i w)) :
    0 ≤ m.mu i w S := by
  exact (h i w).nonnegative S hNoDup hSub

/-- Integrity certification also makes every explicit accessibility list a
well-formed duplicate-free finite support. -/
theorem probabilityIntegrity_accessibility_nodup
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : ModelProbabilityIntegrity m)
    (i : Ag) (w : W) :
    (m.R i w).Nodup := by
  exact (h i w).support_nodup

/-!
## Research boundary

This gate does not yet claim that the concrete models already present in the
repository satisfy `ModelProbabilityIntegrity`.  Those promotion theorems are
separate proof obligations and are scientifically important: they tell us which
old witnesses remain valid under the stronger probabilistic reading.

The next intended gate is a weight-generated local measure constructor whose
integrity laws are proved once and then inherited by concrete models.  After
that, convex rational interpolation of weights can be studied without relying
on the deliberately weak legacy measure interface.
-/

end PEL4
