import Lean.Elab.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictIncidenceN

namespace PEL4.Paradoxes

/-!
# Arbitrary n-claim co-conflict hierarchy

The exact incidence representation stores masses `x_A` for local-glut patterns
`A`.  This module adds the cumulative (zeta-transform) coordinates

  J_Q = sum_{A superset Q} x_A,

where `Q` is a Boolean query pattern.  A query of size one is a first-order
local glut marginal, size two records pairwise co-conflict, and so on.

This is the natural arbitrary-arity extension of `PrefaceConflictMobius3.lean`.
-/

/-- Boolean subset test on incidence patterns.  `patternContains q p = true`
means every `true` coordinate requested by `q` is also `true` in `p`.  Lengths
must agree. -/
def patternContains : List Bool → List Bool → Bool
| [], [] => true
| q :: qs, p :: ps => ((!q) || p) && patternContains qs ps
| _, _ => false

/-- Every pattern contains itself. -/
theorem patternContains_refl :
    ∀ p : List Bool, patternContains p p = true
| [] => by simp [patternContains]
| b :: bs => by
    have ih := patternContains_refl bs
    cases b <;> simp [patternContains, ih]

/-- Containment is transitive. -/
theorem patternContains_trans :
    ∀ a b c : List Bool,
      patternContains a b = true →
      patternContains b c = true →
      patternContains a c = true := by
  intro a
  induction a with
  | nil =>
      intro b c
      cases b with
      | nil =>
          cases c <;> simp [patternContains]
      | cons b bs =>
          cases c <;> simp [patternContains]
  | cons a as ih =>
      intro b c
      cases b with
      | nil =>
          cases c <;> simp [patternContains]
      | cons b bs =>
          cases c with
          | nil => simp [patternContains]
          | cons c cs =>
              intro hab hbc
              simp [patternContains] at hab hbc ⊢
              constructor
              · cases a <;> cases b <;> cases c <;> simp_all
              · exact ih bs cs hab.2 hbc.2

/-- Cumulative co-conflict mass for one query pattern. -/
def coConflictMass {n : Nat}
    (query : List Bool) : List (ConflictPatternCell n) → Nat
| [] => 0
| c :: cs =>
    (if patternContains query c.pattern then c.mass else 0) +
      coConflictMass query cs

/-- A cumulative query can never exceed total carrier mass. -/
theorem coConflictMass_le_carrier {n : Nat}
    (query : List Bool) :
    ∀ cells : List (ConflictPatternCell n),
      coConflictMass query cells ≤ incidenceCarrierMass cells
| [] => by simp [coConflictMass, incidenceCarrierMass]
| c :: cs => by
    have ih := coConflictMass_le_carrier query cs
    by_cases h : patternContains query c.pattern = true
    · simp [coConflictMass, incidenceCarrierMass, h]
      omega
    · have hf : patternContains query c.pattern = false := by
        cases hx : patternContains query c.pattern <;> simp_all
      simp [coConflictMass, incidenceCarrierMass, hf]
      omega

/-- Zeta hierarchy is antitone in the query: requesting more simultaneous local
gluts can only decrease cumulative mass. -/
theorem coConflictMass_antitone {n : Nat}
    (small large : List Bool)
    (hsub : patternContains small large = true) :
    ∀ cells : List (ConflictPatternCell n),
      coConflictMass large cells ≤ coConflictMass small cells
| [] => by simp [coConflictMass]
| c :: cs => by
    have ih := coConflictMass_antitone small large hsub cs
    by_cases hl : patternContains large c.pattern = true
    · have hs : patternContains small c.pattern = true :=
        patternContains_trans small large c.pattern hsub hl
      simp [coConflictMass, hl, hs]
      omega
    · have hlf : patternContains large c.pattern = false := by
        cases hx : patternContains large c.pattern <;> simp_all
      simp [coConflictMass, hlf]
      by_cases hs : patternContains small c.pattern = true
      · simp [hs]
        omega
      · have hsf : patternContains small c.pattern = false := by
          cases hx : patternContains small c.pattern <;> simp_all
        simp [hsf]
        exact ih

/-- Query order is the number of propositions required to be simultaneously B. -/
def coConflictOrder (query : List Bool) : Nat := conflictPatternSize query

/-- A query cannot have order above its arity. -/
theorem coConflictOrder_le_length (query : List Bool) :
    coConflictOrder query ≤ query.length := by
  exact conflictPatternSize_le_length query

/-- A full incidence profile exposes cumulative co-conflict coordinates. -/
def ConflictIncidenceN.coConflict {n : Nat}
    (s : ConflictIncidenceN n) (query : List Bool) : Nat :=
  coConflictMass query s.cells

/-- Every co-conflict coordinate lies below the carrier mass. -/
theorem ConflictIncidenceN.coConflict_le_carrier {n : Nat}
    (s : ConflictIncidenceN n) (query : List Bool) :
    s.coConflict query ≤ s.d := by
  have h := coConflictMass_le_carrier query s.cells
  rw [s.total] at h
  exact h

/-- Profile-level antitonicity of the co-conflict hierarchy. -/
theorem ConflictIncidenceN.coConflict_antitone {n : Nat}
    (s : ConflictIncidenceN n)
    (small large : List Bool)
    (hsub : patternContains small large = true) :
    s.coConflict large ≤ s.coConflict small := by
  exact coConflictMass_antitone small large hsub s.cells

/-!
## Fixed-arity query constructors

The constructors below let us name first- and higher-order conflict coordinates
without introducing Finset/Mathlib machinery.  `orQuery` forms unions of
requirements.
-/

/-- Boolean union of equal-length query patterns. -/
def orQuery : List Bool → List Bool → List Bool
| [], [] => []
| a :: as, b :: bs => (a || b) :: orQuery as bs
| _, _ => []

/-- Every input query is contained in its Boolean union. -/
theorem patternContains_left_orQuery :
    ∀ a b : List Bool,
      a.length = b.length →
      patternContains a (orQuery a b) = true := by
  intro a
  induction a with
  | nil =>
      intro b hlen
      cases b with
      | nil => simp [patternContains, orQuery]
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro b hlen
      cases b with
      | nil => simp at hlen
      | cons b bs =>
          have htail : as.length = bs.length := by simpa using hlen
          have hrec := ih bs htail
          cases a <;> cases b <;> simp [patternContains, orQuery, hrec]

/-- Symmetric containment into Boolean query union. -/
theorem patternContains_right_orQuery :
    ∀ a b : List Bool,
      a.length = b.length →
      patternContains b (orQuery a b) = true := by
  intro a
  induction a with
  | nil =>
      intro b hlen
      cases b with
      | nil => simp [patternContains, orQuery]
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro b hlen
      cases b with
      | nil => simp at hlen
      | cons b bs =>
          have htail : as.length = bs.length := by simpa using hlen
          have hrec := ih bs htail
          cases a <;> cases b <;> simp [patternContains, orQuery, hrec]

/-- Adding requirements by Boolean union can only lower co-conflict mass. -/
theorem ConflictIncidenceN.coConflict_orQuery_le_left {n : Nat}
    (s : ConflictIncidenceN n)
    (a b : List Bool)
    (hlen : a.length = b.length) :
    s.coConflict (orQuery a b) ≤ s.coConflict a := by
  exact s.coConflict_antitone a (orQuery a b)
    (patternContains_left_orQuery a b hlen)

/-- And symmetrically for the right query. -/
theorem ConflictIncidenceN.coConflict_orQuery_le_right {n : Nat}
    (s : ConflictIncidenceN n)
    (a b : List Bool)
    (hlen : a.length = b.length) :
    s.coConflict (orQuery a b) ≤ s.coConflict b := by
  exact s.coConflict_antitone b (orQuery a b)
    (patternContains_right_orQuery a b hlen)

/-!
## Philosophical reading

The hierarchy

  order 1 : proposition-wise latent conflict,
  order 2 : pairwise co-conflict,
  order 3 : triple co-conflict,
  ...

is monotone downward as order requirements are strengthened.  First-order
marginals therefore do not merely omit "some detail": they are the bottom layer
of a complete cumulative interaction hierarchy over the Boolean incidence
lattice.
-/

end PEL4.Paradoxes
