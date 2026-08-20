import Lean.Elab.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictMobiusN

namespace PEL4.Paradoxes
namespace ConflictIncidenceN

/-!
# Conflict nerve and co-conflict filtration

The co-conflict hierarchy already supplies the data of a weighted abstract
simplicial complex.  A Boolean query represents a set of claims.  At threshold
`t`, the query belongs to the conflict nerve when its simultaneous co-conflict
mass is at least `t`.

  N_t = { Q : J_Q >= t }.

Because co-conflict is antitone under inclusion, every face of a simplex in
`N_t` is again in `N_t`.  Thus every fixed threshold defines an abstract
simplicial complex (with the all-false query representing the empty simplex).

For persistence it is convenient to reverse the co-conflict strength:

  f(Q) = d - J_Q.

Then Q subset R implies f(Q) <= f(R), exactly the face/coface monotonicity
required of a simplicial filtration.
-/

/-- Membership in the co-conflict nerve at raw mass threshold `threshold`. -/
def inConflictNerveAt {n : Nat}
    (s : ConflictIncidenceN n)
    (threshold : Nat)
    (query : List Bool) : Prop :=
  query.length = n ∧ threshold ≤ s.coConflict query

/-- Every fixed threshold is downward closed under the Boolean subset order. -/
theorem conflictNerveAt_downward_closed {n : Nat}
    (s : ConflictIncidenceN n)
    (threshold : Nat)
    (small large : List Bool)
    (hsmallLen : small.length = n)
    (hsub : patternContains small large = true)
    (hlarge : s.inConflictNerveAt threshold large) :
    s.inConflictNerveAt threshold small := by
  rcases hlarge with ⟨_, hthreshold⟩
  constructor
  · exact hsmallLen
  · have hanti := s.coConflict_antitone small large hsub
    omega

/-- Raising the mass threshold can only remove simplices. -/
theorem conflictNerveAt_threshold_antitone {n : Nat}
    (s : ConflictIncidenceN n)
    (low high : Nat)
    (hle : low ≤ high)
    (query : List Bool)
    (hhigh : s.inConflictNerveAt high query) :
    s.inConflictNerveAt low query := by
  rcases hhigh with ⟨hlen, hmass⟩
  constructor
  · exact hlen
  · omega

/-- The support conflict nerve retains exactly the positive-mass co-conflicts. -/
def inSupportConflictNerve {n : Nat}
    (s : ConflictIncidenceN n)
    (query : List Bool) : Prop :=
  query.length = n ∧ 0 < s.coConflict query

/-- The support nerve is the threshold-1 nerve for natural-valued masses. -/
theorem supportConflictNerve_iff_threshold_one {n : Nat}
    (s : ConflictIncidenceN n)
    (query : List Bool) :
    s.inSupportConflictNerve query ↔ s.inConflictNerveAt 1 query := by
  constructor
  · rintro ⟨hlen, hpos⟩
    exact ⟨hlen, by omega⟩
  · rintro ⟨hlen, hone⟩
    exact ⟨hlen, by omega⟩

/-- The support nerve is downward closed as well. -/
theorem supportConflictNerve_downward_closed {n : Nat}
    (s : ConflictIncidenceN n)
    (small large : List Bool)
    (hsmallLen : small.length = n)
    (hsub : patternContains small large = true)
    (hlarge : s.inSupportConflictNerve large) :
    s.inSupportConflictNerve small := by
  rw [supportConflictNerve_iff_threshold_one] at hlarge ⊢
  exact s.conflictNerveAt_downward_closed 1 small large hsmallLen hsub hlarge

/-- Persistence-compatible filtration value: stronger co-conflict appears
earlier, while weak or absent interactions appear later. -/
def conflictNerveFiltration {n : Nat}
    (s : ConflictIncidenceN n)
    (query : List Bool) : Nat :=
  s.d - s.coConflict query

/-- Face/coface monotonicity of the conflict-nerve filtration. -/
theorem conflictNerveFiltration_monotone {n : Nat}
    (s : ConflictIncidenceN n)
    (small large : List Bool)
    (hsub : patternContains small large = true) :
    s.conflictNerveFiltration small ≤ s.conflictNerveFiltration large := by
  have hanti := s.coConflict_antitone small large hsub
  have hsmall := s.coConflict_le_carrier small
  have hlarge := s.coConflict_le_carrier large
  simp [conflictNerveFiltration]
  omega

/-- A raw co-conflict threshold is equivalent to a sublevel threshold of the
persistence-compatible filtration, provided the threshold lies inside the
carrier range. -/
theorem conflictNerveAt_iff_filtration_sublevel {n : Nat}
    (s : ConflictIncidenceN n)
    (threshold : Nat)
    (hthreshold : threshold ≤ s.d)
    (query : List Bool) :
    threshold ≤ s.coConflict query ↔
      s.conflictNerveFiltration query ≤ s.d - threshold := by
  have hquery := s.coConflict_le_carrier query
  simp [conflictNerveFiltration]
  omega

/-!
## Interpretation

The unweighted support nerve remembers which groups of claims can be jointly
conflicted at all.  The weighted hierarchy remembers how much carrier mass
supports each simplex.  The filtration `d - J_Q` turns that strength hierarchy
into the standard increasing filtration convention used in persistent
homology.
-/

end ConflictIncidenceN
end PEL4.Paradoxes
