import PEL4.FiniteProbabilityIntegrity
import PEL4.BeliefClassicalRecovery

namespace PEL4

/-!
# Lockean belief as a two-channel neighbourhood modality

The threshold belief operator of 4-PEL is a Scott–Montague neighbourhood modality:
with `N_c(w) = { X | μ_w(X) ≥ c }`, the positive bit of `B φ` says that the positive
extension of `φ` is a neighbourhood of `w`, and the negative bit says the same of the
negative extension.  This file makes that reading explicit and proves the frame laws:

* **N** – the accessible range is a neighbourhood (legacy `Model` suffices);
* **P** – the empty event is not a neighbourhood (legacy `Model` suffices);
* **M** – neighbourhoods are upward closed (needs `FiniteProbabilityIntegrity`);
* **D** – two disjoint events are never both neighbourhoods (needs integrity and
  `c > 1/2`); lifted to the two channels: a valuation without gluts on the accessible
  range yields a threshold-consistent belief;
* **¬C** – neighbourhoods are not closed under intersection (finite witness).

So Lockean belief validates the non-normal system with M, N, P, D and refutes C;
compare van Benthem–Pacuit evidence models and the logic END of Kogure (2025).
-/

/-- The Lockean neighbourhood system of a measure at threshold `c`. -/
def ThresholdNeighbourhood {W : Type} (mu : ProbMeasure W) (c : Rat)
    (X : FiniteSet W) : Prop :=
  mu X ≥ c

/-- The neighbourhood system of agent `i` at world `w`. -/
def BeliefNeighbourhood {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (X : FiniteSet W) : Prop :=
  ThresholdNeighbourhood (m.mu i w) (m.c i) X

/-- Positive extension of a four-valued proposition inside the accessible range. -/
def posExtension {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) : FiniteSet W :=
  filterWorlds (m.R i w) (fun u => (value u).pos)

/-- Negative extension of a four-valued proposition inside the accessible range. -/
def negExtension {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) : FiniteSet W :=
  filterWorlds (m.R i w) (fun u => (value u).neg)

/-- Channel 1: belief is supported iff the positive extension is a neighbourhood. -/
theorem belief_pos_iff_neighbourhood
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) :
    (belief m i w value).pos = true ↔
      BeliefNeighbourhood m i w (posExtension m i w value) := by
  simp [belief, BeliefNeighbourhood, ThresholdNeighbourhood, posExtension]

/-- Channel 2: belief is refuted iff the negative extension is a neighbourhood. -/
theorem belief_neg_iff_neighbourhood
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) :
    (belief m i w value).neg = true ↔
      BeliefNeighbourhood m i w (negExtension m i w value) := by
  simp [belief, BeliefNeighbourhood, ThresholdNeighbourhood, negExtension]

/-- **N**: the whole accessible range is a neighbourhood. -/
theorem neighbourhood_N
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) :
    BeliefNeighbourhood m i w (m.R i w) := by
  have h1 := m.mu_total i w
  have h2 := m.c_le_one i
  unfold BeliefNeighbourhood ThresholdNeighbourhood
  grind

/-- **P**: the empty event is never a neighbourhood. -/
theorem neighbourhood_P
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) :
    ¬ BeliefNeighbourhood m i w [] := by
  have h1 := m.mu_empty i w
  have h2 := m.c_gt_half i
  unfold BeliefNeighbourhood ThresholdNeighbourhood
  grind

/-- **M**: under finite probability integrity, neighbourhoods are upward closed. -/
theorem neighbourhood_M
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (A B : FiniteSet W) (hA : A.Nodup) (hB : B.Nodup)
    (hAB : FiniteEventSubset A B) (hB' : FiniteEventSubset B (m.R i w))
    (hN : BeliefNeighbourhood m i w A) :
    BeliefNeighbourhood m i w B := by
  have h1 := (h i w).monotone A B hA hB hAB hB'
  unfold BeliefNeighbourhood ThresholdNeighbourhood at *
  grind

/-- **D**: under integrity and `c > 1/2`, two disjoint events are never both
neighbourhoods. -/
theorem neighbourhood_D
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (A B : FiniteSet W) (hA : A.Nodup) (hB : B.Nodup)
    (hA' : FiniteEventSubset A (m.R i w)) (hB' : FiniteEventSubset B (m.R i w))
    (hDis : FiniteEventDisjoint A B) :
    ¬ (BeliefNeighbourhood m i w A ∧ BeliefNeighbourhood m i w B) := by
  intro ⟨hNA, hNB⟩
  have hadd := (h i w).add_disjoint A B hA hB hA' hB' hDis
  have hnd : (A ++ B).Nodup := by
    rw [List.nodup_append]
    exact ⟨hA, hB, fun a ha b hb hab => hDis a ha (hab ▸ hb)⟩
  have hsub : FiniteEventSubset (A ++ B) (m.R i w) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hA' x hx
    · exact hB' x hx
  have hmono := (h i w).monotone (A ++ B) (m.R i w) hnd (h i w).support_nodup hsub
    (fun x hx => hx)
  have htot := (h i w).total
  have hc := m.c_gt_half i
  unfold BeliefNeighbourhood ThresholdNeighbourhood at *
  grind

/-- Two-channel **D**: if no accessible world carries a glut, Lockean belief is
threshold-consistent, i.e. `B φ` is never `B`. -/
theorem belief_thresholdConsistent_of_no_glut
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (value : W → FDEValue)
    (hNoGlut : ∀ u, u ∈ m.R i w → ¬ ((value u).pos = true ∧ (value u).neg = true)) :
    BeliefThresholdConsistent m i w value := by
  intro ⟨hp, hn⟩
  have hnd := (h i w).support_nodup
  refine neighbourhood_D m h i w (posExtension m i w value) (negExtension m i w value)
    (hnd.filter _) (hnd.filter _) ?_ ?_ ?_ ⟨?_, ?_⟩
  · intro x hx; exact (List.mem_filter.mp hx).1
  · intro x hx; exact (List.mem_filter.mp hx).1
  · intro x hx hx'
    exact hNoGlut x (List.mem_filter.mp hx).1
      ⟨(List.mem_filter.mp hx).2, (List.mem_filter.mp hx').2⟩
  · simpa [beliefPositiveThresholdBit, BeliefNeighbourhood, ThresholdNeighbourhood,
      posExtension] using hp
  · simpa [beliefNegativeThresholdBit, BeliefNeighbourhood, ThresholdNeighbourhood,
      negExtension] using hn

/-! ## Failure of C (aggregation): a finite witness -/

/-- Uniform counting measure on three worlds. -/
def uniform3 : ProbMeasure (Fin 3) := fun S => (S.length : Rat) / 3

/-- **¬C**: at threshold `2/3`, `{0,1}` and `{1,2}` are neighbourhoods but their
intersection `{1}` is not.  Lockean belief is not closed under conjunction. -/
theorem neighbourhood_not_C :
    ThresholdNeighbourhood uniform3 (2 / 3) [0, 1] ∧
    ThresholdNeighbourhood uniform3 (2 / 3) [1, 2] ∧
    ¬ ThresholdNeighbourhood uniform3 (2 / 3) [1] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ThresholdNeighbourhood, uniform3] <;> grind

end PEL4
