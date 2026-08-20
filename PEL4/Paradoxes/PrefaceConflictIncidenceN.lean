import Std.Tactic.Omega

namespace PEL4.Paradoxes

/-!
# Arbitrary finite conflict incidence patterns

This module lifts the incidence accounting beyond the explicitly enumerated
three-claim `Delta^6`.

A conflict pattern is represented by a Boolean list of fixed arity `n`; `true`
at coordinate `i` means that conjunct `i` is object-level B on that carrier
cell.  Every stored pattern is required to be nonempty.

The representation permits repeated patterns.  It is therefore a convenient
finite measure representation rather than a canonical simplex coordinate
vector.  Equal patterns can later be merged without changing any theorem below.
-/

/-- Number of active local-glut incidences in one Boolean pattern. -/
def conflictPatternSize : List Bool → Nat
| [] => 0
| b :: bs => (if b then 1 else 0) + conflictPatternSize bs

/-- Incidence size never exceeds arity. -/
theorem conflictPatternSize_le_length :
    ∀ pattern : List Bool,
      conflictPatternSize pattern ≤ pattern.length
| [] => by simp [conflictPatternSize]
| b :: bs => by
    have ih := conflictPatternSize_le_length bs
    cases b <;> simp [conflictPatternSize] <;> omega

/-- One weighted nonempty incidence pattern of fixed arity. -/
structure ConflictPatternCell (n : Nat) where
  pattern : List Bool
  mass : Nat
  arity : pattern.length = n
  nonempty : 0 < conflictPatternSize pattern

/-- Raw carrier mass of a finite incidence measure. -/
def incidenceCarrierMass {n : Nat} : List (ConflictPatternCell n) → Nat
| [] => 0
| c :: cs => c.mass + incidenceCarrierMass cs

/-- Total local glut multiplicity `S = sum_A |A| x_A`. -/
def incidenceMultiplicity {n : Nat} : List (ConflictPatternCell n) → Nat
| [] => 0
| c :: cs =>
    c.mass * conflictPatternSize c.pattern + incidenceMultiplicity cs

/-- Redundancy excess `sum_A (|A|-1) x_A`. -/
def incidenceRedundancyExcess {n : Nat} : List (ConflictPatternCell n) → Nat
| [] => 0
| c :: cs =>
    c.mass * (conflictPatternSize c.pattern - 1) +
      incidenceRedundancyExcess cs

/-- One nonempty cell decomposes into its mandatory first membership plus its
redundant memberships. -/
theorem cell_multiplicity_decomposition {n : Nat}
    (c : ConflictPatternCell n) :
    c.mass * conflictPatternSize c.pattern =
      c.mass + c.mass * (conflictPatternSize c.pattern - 1) := by
  have hs : conflictPatternSize c.pattern =
      (conflictPatternSize c.pattern - 1) + 1 := by
    omega
  calc
    c.mass * conflictPatternSize c.pattern =
        c.mass * ((conflictPatternSize c.pattern - 1) + 1) := by rw [hs]
    _ = c.mass + c.mass * (conflictPatternSize c.pattern - 1) := by
      simp [Nat.mul_add, Nat.add_comm]

/-- Generic exact redundancy decomposition:

  S = d + sum_A (|A|-1) x_A.
-/
theorem incidence_multiplicity_decomposition {n : Nat} :
    ∀ cells : List (ConflictPatternCell n),
      incidenceMultiplicity cells =
        incidenceCarrierMass cells + incidenceRedundancyExcess cells
| [] => by simp [incidenceMultiplicity, incidenceCarrierMass,
    incidenceRedundancyExcess]
| c :: cs => by
    have hc := cell_multiplicity_decomposition c
    have ih := incidence_multiplicity_decomposition cs
    simp [incidenceMultiplicity, incidenceCarrierMass,
      incidenceRedundancyExcess]
    omega

/-- Every nonempty pattern contributes at least one membership. -/
theorem cell_mass_le_multiplicity {n : Nat}
    (c : ConflictPatternCell n) :
    c.mass ≤ c.mass * conflictPatternSize c.pattern := by
  have hone : 1 ≤ conflictPatternSize c.pattern := by omega
  have h := Nat.mul_le_mul_left c.mass hone
  simpa using h

/-- Every pattern contributes at most `n` memberships per unit mass. -/
theorem cell_multiplicity_le_n_mass {n : Nat}
    (c : ConflictPatternCell n) :
    c.mass * conflictPatternSize c.pattern ≤ n * c.mass := by
  have hsize0 := conflictPatternSize_le_length c.pattern
  have harity := c.arity
  have hsize : conflictPatternSize c.pattern ≤ n := by omega
  have h := Nat.mul_le_mul_left c.mass hsize
  simpa [Nat.mul_comm] using h

/-- Generic lower bound `d <= S`. -/
theorem incidence_carrier_le_multiplicity {n : Nat} :
    ∀ cells : List (ConflictPatternCell n),
      incidenceCarrierMass cells ≤ incidenceMultiplicity cells
| [] => by simp [incidenceCarrierMass, incidenceMultiplicity]
| c :: cs => by
    have hc := cell_mass_le_multiplicity c
    have ih := incidence_carrier_le_multiplicity cs
    simp [incidenceCarrierMass, incidenceMultiplicity]
    omega

/-- Generic upper bound `S <= n*d`. -/
theorem incidence_multiplicity_le_n_carrier {n : Nat} :
    ∀ cells : List (ConflictPatternCell n),
      incidenceMultiplicity cells ≤ n * incidenceCarrierMass cells
| [] => by simp [incidenceCarrierMass, incidenceMultiplicity]
| c :: cs => by
    have hc := cell_multiplicity_le_n_mass c
    have ih := incidence_multiplicity_le_n_carrier cs
    simp [incidenceCarrierMass, incidenceMultiplicity, Nat.mul_add]
    omega

/-- A finite n-claim conflict incidence measure with total carrier mass `d`. -/
structure ConflictIncidenceN (n : Nat) where
  cells : List (ConflictPatternCell n)
  d : Nat
  total : incidenceCarrierMass cells = d

namespace ConflictIncidenceN

/-- Total local glut multiplicity. -/
def totalLocal {n : Nat} (s : ConflictIncidenceN n) : Nat :=
  incidenceMultiplicity s.cells

/-- Higher-order redundancy excess. -/
def redundancyExcess {n : Nat} (s : ConflictIncidenceN n) : Nat :=
  incidenceRedundancyExcess s.cells

/-- Exact n-claim incidence accounting. -/
theorem redundancy_decomposition {n : Nat} (s : ConflictIncidenceN n) :
    s.totalLocal = s.d + s.redundancyExcess := by
  have h := incidence_multiplicity_decomposition s.cells
  rw [s.total] at h
  exact h

/-- Dimension-independent raw multiplicity interval. -/
theorem carrier_multiplicity_bounds {n : Nat} (s : ConflictIncidenceN n) :
    s.d ≤ s.totalLocal ∧ s.totalLocal ≤ n * s.d := by
  constructor
  · have h := incidence_carrier_le_multiplicity s.cells
    rw [s.total] at h
    exact h
  · have h := incidence_multiplicity_le_n_carrier s.cells
    rw [s.total] at h
    exact h

end ConflictIncidenceN

/-- Zero redundancy forces every positive-mass incidence cell onto a singleton
pattern.  Zero-mass bookkeeping cells are irrelevant. -/
theorem zero_redundancy_forces_singleton_support {n : Nat} :
    ∀ cells : List (ConflictPatternCell n),
      incidenceRedundancyExcess cells = 0 →
      ∀ c, c ∈ cells → 0 < c.mass → conflictPatternSize c.pattern = 1
| [], _ => by simp
| c :: cs, hz => by
    intro x hx hmass
    have hzsum :
        c.mass * (conflictPatternSize c.pattern - 1) +
          incidenceRedundancyExcess cs = 0 := by
      simpa [incidenceRedundancyExcess] using hz
    have hhead : c.mass * (conflictPatternSize c.pattern - 1) = 0 := by
      omega
    have htail : incidenceRedundancyExcess cs = 0 := by omega
    have hx' : x = c ∨ x ∈ cs := by simpa using hx
    rcases hx' with rfl | hmem
    · have hsizePos : 0 < conflictPatternSize c.pattern := c.nonempty
      by_contra hne
      have hgt : 1 < conflictPatternSize c.pattern := by omega
      have hsub : 0 < conflictPatternSize c.pattern - 1 := by omega
      have hprod : 0 < c.mass * (conflictPatternSize c.pattern - 1) :=
        Nat.mul_pos hmass hsub
      omega
    · exact zero_redundancy_forces_singleton_support cs htail x hmem hmass

/-- Conversely, if every positive-mass cell is a singleton pattern, redundancy
is exactly zero. -/
theorem singleton_support_gives_zero_redundancy {n : Nat} :
    ∀ cells : List (ConflictPatternCell n),
      (∀ c, c ∈ cells → 0 < c.mass → conflictPatternSize c.pattern = 1) →
      incidenceRedundancyExcess cells = 0
| [], _ => by simp [incidenceRedundancyExcess]
| c :: cs, hsupport => by
    have htailSupport :
        ∀ x, x ∈ cs → 0 < x.mass → conflictPatternSize x.pattern = 1 := by
      intro x hx hm
      exact hsupport x (by simp [hx]) hm
    have ih := singleton_support_gives_zero_redundancy cs htailSupport
    by_cases hm : c.mass = 0
    · simp [incidenceRedundancyExcess, hm, ih]
    · have hmpos : 0 < c.mass := Nat.pos_of_ne_zero hm
      have hsingle := hsupport c (by simp) hmpos
      simp [incidenceRedundancyExcess, hsingle, ih]

/-- Exact general face characterization for `r = 0`. -/
theorem zero_redundancy_iff_singleton_support {n : Nat}
    (cells : List (ConflictPatternCell n)) :
    incidenceRedundancyExcess cells = 0 ↔
      ∀ c, c ∈ cells → 0 < c.mass → conflictPatternSize c.pattern = 1 := by
  constructor
  · exact zero_redundancy_forces_singleton_support cells
  · exact singleton_support_gives_zero_redundancy cells

end PEL4.Paradoxes
