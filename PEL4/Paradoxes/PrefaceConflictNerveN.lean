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

/-- Positive co-conflict mass is exactly witnessed by a positive-mass incidence
cell containing the whole query.  This is the finite relational semantics of
the support nerve. -/
theorem coConflictMass_pos_iff_exists_positive_cell {n : Nat}
    (query : List Bool) :
    ∀ cells : List (ConflictPatternCell n),
      0 < coConflictMass query cells ↔
        ∃ c, c ∈ cells ∧
          patternContains query c.pattern = true ∧ 0 < c.mass
| [] => by
    simp [coConflictMass]
| c :: cs => by
    have ih := coConflictMass_pos_iff_exists_positive_cell query cs
    by_cases hc : patternContains query c.pattern = true
    · constructor
      · intro hpos
        by_cases hm : c.mass = 0
        · have htail : 0 < coConflictMass query cs := by
            simpa [coConflictMass, hc, hm] using hpos
          rcases ih.mp htail with ⟨x, hxmem, hxcontains, hxmass⟩
          exact ⟨x, by simp [hxmem], hxcontains, hxmass⟩
        · have hmpos : 0 < c.mass := Nat.pos_of_ne_zero hm
          exact ⟨c, by simp, hc, hmpos⟩
      · rintro ⟨x, hxmem, hxcontains, hxmass⟩
        have hx : x = c ∨ x ∈ cs := by simpa using hxmem
        rcases hx with hxc | hxcs
        · subst x
          simp [coConflictMass, hc]
          omega
        · have htail : 0 < coConflictMass query cs :=
            ih.mpr ⟨x, hxcs, hxcontains, hxmass⟩
          simp [coConflictMass, hc]
          omega
    · have hcf : patternContains query c.pattern = false := by
        cases hx : patternContains query c.pattern <;> simp_all
      constructor
      · intro hpos
        have htail : 0 < coConflictMass query cs := by
          simpa [coConflictMass, hcf] using hpos
        rcases ih.mp htail with ⟨x, hxmem, hxcontains, hxmass⟩
        exact ⟨x, by simp [hxmem], hxcontains, hxmass⟩
      · rintro ⟨x, hxmem, hxcontains, hxmass⟩
        have hx : x = c ∨ x ∈ cs := by simpa using hxmem
        rcases hx with hxc | hxcs
        · subst x
          exact False.elim (hc hxcontains)
        · have htail : 0 < coConflictMass query cs :=
            ih.mpr ⟨x, hxcs, hxcontains, hxmass⟩
          simpa [coConflictMass, hcf] using htail

/-- Profile-level support membership is therefore equivalent to existence of a
positive carrier cell jointly realizing the requested local conflicts. -/
theorem supportConflictNerve_iff_exists_positive_cell {n : Nat}
    (s : ConflictIncidenceN n)
    (query : List Bool) :
    s.inSupportConflictNerve query ↔
      query.length = n ∧
        ∃ c, c ∈ s.cells ∧
          patternContains query c.pattern = true ∧ 0 < c.mass := by
  constructor
  · rintro ⟨hlen, hpos⟩
    change 0 < coConflictMass query s.cells at hpos
    exact ⟨hlen, (coConflictMass_pos_iff_exists_positive_cell query s.cells).mp hpos⟩
  · rintro ⟨hlen, hexists⟩
    constructor
    · exact hlen
    · change 0 < coConflictMass query s.cells
      exact (coConflictMass_pos_iff_exists_positive_cell query s.cells).mpr hexists

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

/-- The exact co-conflict mass is recoverable from its filtration value.
Consequently the full weighted filtration loses no information relative to the
co-conflict hierarchy. -/
theorem coConflict_recovered_from_filtration {n : Nat}
    (s : ConflictIncidenceN n)
    (query : List Bool) :
    s.d - s.conflictNerveFiltration query = s.coConflict query := by
  have hquery := s.coConflict_le_carrier query
  unfold conflictNerveFiltration
  omega

/-!
## Interpretation

The unweighted support nerve remembers which groups of claims can be jointly
conflicted at all.  The weighted hierarchy remembers how much carrier mass
supports each simplex.  The filtration `d - J_Q` turns that strength hierarchy
into the standard increasing filtration convention used in persistent
homology.

Because `J_Q = d - f(Q)`, the complete weighted filtration is information-
equivalent to the complete co-conflict hierarchy.  Information is lost only
when the filtration is thresholded, reduced to support, or compressed further
to invariants such as Betti numbers or persistence barcodes.

The positive-cell witness theorem also makes the relational reading explicit:
a support simplex is present exactly when one positive carrier cell realizes
all of its requested claim-conflict incidences simultaneously.
-/

end ConflictIncidenceN
end PEL4.Paradoxes
