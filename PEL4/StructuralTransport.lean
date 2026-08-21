namespace PEL4

/-!
# Structural transport

This module turns the current cross-paradox research heuristic into a small
formal vocabulary. A property may or may not be preserved when an object is
transformed, and an observation/projection may or may not commute with a
transformation.

The definitions are intentionally domain-agnostic. Later paradox modules can
instantiate them with belief update, conjunction, projection, counterfactual
context change, or other structure-changing maps.
-/

/-- A predicate `P` on source objects transports to predicate `Q` on target
objects along `T` when every `P`-source is sent to a `Q`-target. -/
def TransportsPredicate {α β : Type}
    (T : α → β) (P : α → Prop) (Q : β → Prop) : Prop :=
  ∀ x, P x → Q (T x)

/-- Same-type preservation as the special case where source and target
predicates coincide. -/
def PreservesPredicate {α : Type}
    (T : α → α) (P : α → Prop) : Prop :=
  TransportsPredicate T P P

/-- A concrete witness refutes predicate transport. -/
theorem transport_fails_of_witness {α β : Type}
    (T : α → β) (P : α → Prop) (Q : β → Prop)
    (x : α) (hP : P x) (hQ : ¬ Q (T x)) :
    ¬ TransportsPredicate T P Q := by
  intro h
  exact hQ (h x hP)

/-- A projection `pi` commutes with source transformation `T` and target
transformation `Tstar` when transforming before or after projection gives the
same observable result. -/
def Commutes {α β : Type}
    (pi : α → β) (T : α → α) (Tstar : β → β) : Prop :=
  ∀ x, pi (T x) = Tstar (pi x)

/-- A single non-commuting point refutes commutation. -/
theorem commutation_fails_of_witness {α β : Type}
    (pi : α → β) (T : α → α) (Tstar : β → β)
    (x : α) (h : pi (T x) ≠ Tstar (pi x)) :
    ¬ Commutes pi T Tstar := by
  intro hcomm
  exact h (hcomm x)

/-- Two observations are extensionally equivalent after transport when the
observable target value after `T` is exactly the source observation. -/
def PreservesObservation {α β γ : Type}
    (T : α → β) (observeSource : α → γ) (observeTarget : β → γ) : Prop :=
  ∀ x, observeTarget (T x) = observeSource x

/-- Concrete observation change witnesses failure of observational
preservation. -/
theorem observation_preservation_fails_of_witness
    {α β γ : Type}
    (T : α → β) (observeSource : α → γ) (observeTarget : β → γ)
    (x : α) (h : observeTarget (T x) ≠ observeSource x) :
    ¬ PreservesObservation T observeSource observeTarget := by
  intro hp
  exact h (hp x)

end PEL4
