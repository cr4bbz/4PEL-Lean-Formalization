import PEL4.Syntax
import PEL4.Evidence

namespace PEL4

/-!
# Epistemic status layer

Four-valued epistemic logic makes several notions diverge that coincide in a
classical setting. In particular, internal FDE negation of a belief formula is
not in general the same thing as absence of positive belief.

For a belief state `v = (pos, neg)`:

* internal negation has positive bit `neg`;
* absence of positive belief is `not pos`.

These agree exactly at the classical values `T` and `F`, and disagree at the
nonclassical values `B` and `N`.

This module gives those notions explicit names before a later knowledge layer
introduces a distinct factive operator `K`.
-/

/-- Positive threshold support for believing `phi`. -/
def positivelyBelieves {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (eval m w (Formula.bel i phi)).pos

/-- Negative threshold support for believing `phi`. This is independent of
positive support and therefore should not be identified with simple absence of
belief. -/
def negativelyBelieves {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (eval m w (Formula.bel i phi)).neg

/-- Meta-level absence of positive threshold belief. -/
def lacksPositiveBelief {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  !(positivelyBelieves m i w phi)

/-- Meta-level absence of negative threshold belief. -/
def lacksNegativeBelief {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  !(negativelyBelieves m i w phi)

/-- Strict positive belief: positive support without negative support. -/
def strictlyPositivelyBelieves {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  positivelyBelieves m i w phi && lacksNegativeBelief m i w phi

/-- Strict negative belief / disbelief: negative support without positive
support. -/
def strictlyNegativelyBelieves {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  lacksPositiveBelief m i w phi && negativelyBelieves m i w phi

/-- Belief-level glut: both positive and negative threshold support. -/
def hasGluttyBelief {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  positivelyBelieves m i w phi && negativelyBelieves m i w phi

/-- Belief-level gap: neither positive nor negative threshold support. -/
def hasGappyBelief {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  lacksPositiveBelief m i w phi && lacksNegativeBelief m i w phi

/-- Internal FDE negation swaps the positive and negative support bits. -/
theorem internal_negated_belief_positive_is_negative_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    (eval m w (Formula.not (Formula.bel i phi))).pos =
      negativelyBelieves m i w phi := by
  rfl

/-- Dually, negative support for the internally negated belief is positive
support for the original belief. -/
theorem internal_negated_belief_negative_is_positive_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    (eval m w (Formula.not (Formula.bel i phi))).neg =
      positivelyBelieves m i w phi := by
  rfl

/-- At the level of arbitrary FDE values, internal negation behaves like
absence of positive support exactly on the classical subspace. -/
theorem internal_negation_matches_positive_absence_iff_classical
    (v : FDEValue) :
    (FDEValue.not v).pos = !v.pos ↔ isClassical v = true := by
  rcases v with ⟨pos, neg⟩
  cases pos <;> cases neg <;> native_decide

/-- Model-level version of the same separation theorem. -/
theorem internal_not_belief_matches_absence_iff_classical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    (eval m w (Formula.not (Formula.bel i phi))).pos =
        lacksPositiveBelief m i w phi ↔
      isClassical (eval m w (Formula.bel i phi)) = true := by
  simpa [lacksPositiveBelief, positivelyBelieves] using
    internal_negation_matches_positive_absence_iff_classical
      (eval m w (Formula.bel i phi))

/-- The glut state witnesses one direction of the nonclassical divergence. -/
example : (FDEValue.not FDEValue.B).pos ≠ !FDEValue.B.pos := by
  native_decide

/-- The gap state witnesses the opposite divergence. -/
example : (FDEValue.not FDEValue.N).pos ≠ !FDEValue.N.pos := by
  native_decide

end PEL4
