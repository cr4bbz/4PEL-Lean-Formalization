import PEL4.ModalDynamicsRobustness

namespace PEL4

/-!
# Combinatorial geometry of dynamic four-valued status

An FDE value is already a pair of Boolean threshold coordinates:

```text
N = (0,0)    T = (1,0)
F = (0,1)    B = (1,1)
```

This module treats those four values as the vertices of a Boolean square.  The
natural combinatorial distance counts how many threshold coordinates differ.
It therefore takes only the values 0, 1, and 2.

This is deliberately a combinatorial result.  It does not yet assert that a
continuous path of probability measures literally crosses a topological wall.
That stronger statement would require a separate path/continuity layer.
-/

/-- Number of positive/negative threshold coordinates that differ between two
complete FDE values. -/
def thresholdWallCount (a b : FDEValue) : Nat :=
  (if a.pos = b.pos then 0 else 1) +
  (if a.neg = b.neg then 0 else 1)

/-- One-wall adjacency in the threshold square. -/
def ThresholdAdjacent (a b : FDEValue) : Prop :=
  thresholdWallCount a b = 1

/-- Opposite corners differ in both threshold coordinates. -/
def ThresholdOpposite (a b : FDEValue) : Prop :=
  thresholdWallCount a b = 2

/-- Threshold-wall count is symmetric. -/
theorem thresholdWallCount_symm (a b : FDEValue) :
    thresholdWallCount a b = thresholdWallCount b a := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- The Boolean square has diameter two. -/
theorem thresholdWallCount_le_two (a b : FDEValue) :
    thresholdWallCount a b ≤ 2 := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- Zero threshold displacement is exactly equality of complete FDE status. -/
theorem thresholdWallCount_eq_zero_iff (a b : FDEValue) :
    thresholdWallCount a b = 0 ↔ a = b := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- Distance two means that both threshold coordinates flip. -/
theorem thresholdWallCount_eq_two_iff (a b : FDEValue) :
    thresholdWallCount a b = 2 ↔
      a.pos ≠ b.pos ∧ a.neg ≠ b.neg := by
  by_cases hp : a.pos = b.pos <;>
    by_cases hn : a.neg = b.neg <;>
      simp [thresholdWallCount, hp, hn]

/-- Every pair lies at combinatorial distance zero, one, or two. -/
theorem thresholdWallCount_trichotomy (a b : FDEValue) :
    thresholdWallCount a b = 0 ∨
    thresholdWallCount a b = 1 ∨
    thresholdWallCount a b = 2 := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- Every genuine status change flips either one or both threshold coordinates. -/
theorem thresholdWallCount_of_ne (a b : FDEValue) (h : a ≠ b) :
    thresholdWallCount a b = 1 ∨ thresholdWallCount a b = 2 := by
  rcases thresholdWallCount_trichotomy a b with h0 | h12
  · exact False.elim (h ((thresholdWallCount_eq_zero_iff a b).1 h0))
  · exact h12

/-!
## The square explicitly

The four edge-neighbour relations are

```text
N -- T
|    |
F -- B
```

while `T/F` and `N/B` are the two diagonals.
-/

example : thresholdWallCount FDEValue.N FDEValue.T = 1 := by native_decide
example : thresholdWallCount FDEValue.N FDEValue.F = 1 := by native_decide
example : thresholdWallCount FDEValue.T FDEValue.B = 1 := by native_decide
example : thresholdWallCount FDEValue.F FDEValue.B = 1 := by native_decide
example : thresholdWallCount FDEValue.T FDEValue.F = 2 := by native_decide
example : thresholdWallCount FDEValue.N FDEValue.B = 2 := by native_decide

/-!
## Dynamic interpretation

Threshold-Side Robustness says that probabilistic belief is unchanged exactly
when its two threshold bits are unchanged.  In the square geometry this is
precisely zero displacement.
-/

/-- Exact geometric restatement of the pointwise belief-robustness theorem. -/
theorem modal_belief_zero_wall_iff_threshold_bits_eq
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    thresholdWallCount
        (evalModal before w (ModalFormula.bel i phi))
        (evalModal after w (ModalFormula.bel i phi)) = 0 ↔
      decide (modalPositiveBeliefMass after i w phi ≥ after.c i) =
          decide (modalPositiveBeliefMass before i w phi ≥ before.c i) ∧
      decide (modalNegativeBeliefMass after i w phi ≥ after.c i) =
          decide (modalNegativeBeliefMass before i w phi ≥ before.c i) := by
  constructor
  · intro h0
    have hEq :
        evalModal before w (ModalFormula.bel i phi) =
          evalModal after w (ModalFormula.bel i phi) :=
      (thresholdWallCount_eq_zero_iff _ _).1 h0
    exact (modal_belief_value_eq_iff_threshold_bits_eq
      before after i w phi).1 hEq.symm
  · intro hBits
    have hEq :
        evalModal after w (ModalFormula.bel i phi) =
          evalModal before w (ModalFormula.bel i phi) :=
      (modal_belief_value_eq_iff_threshold_bits_eq
        before after i w phi).2 hBits
    exact (thresholdWallCount_eq_zero_iff _ _).2 hEq.symm

/-- Every compositionally robust modal formula has zero dynamic displacement
under its designated conditionalization. -/
theorem robust_formula_has_zero_threshold_displacement
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    {phi : ModalFormula Atom Ag}
    (hRobust : ModalConditionalizationRobust m E hAdm phi)
    (w : W) :
    thresholdWallCount
        (evalModal m w phi)
        (evalModal (conditionalize m E hAdm) w phi) = 0 := by
  apply (thresholdWallCount_eq_zero_iff _ _).2
  exact (evalModal_conditionalize_of_robust m E hAdm hRobust w).symm

/-- The complete reachability family realizes exactly the combinatorial
threshold displacement requested by its source and target values. -/
theorem dynamic_reachability_realizes_exact_threshold_displacement
    (source target : FDEValue) :
    thresholdWallCount
        (evalModal (DynamicReachabilityModel source target)
          DynamicReachabilityWorld.focus dynamicReachabilityKBelP)
        (evalModal (DynamicReachabilityUpdated source target)
          DynamicReachabilityWorld.focus dynamicReachabilityKBelP) =
      thresholdWallCount source target := by
  rw [dynamic_reachability_knowledge_before,
      dynamic_reachability_knowledge_after]

/-- Hence the verified reachability construction realizes zero-, one-, and
 two-wall transitions, including both diagonals of the square. -/
theorem dynamic_reachability_realizes_two_wall_truth_false :
    thresholdWallCount
        (evalModal (DynamicReachabilityModel FDEValue.T FDEValue.F)
          DynamicReachabilityWorld.focus dynamicReachabilityKBelP)
        (evalModal (DynamicReachabilityUpdated FDEValue.T FDEValue.F)
          DynamicReachabilityWorld.focus dynamicReachabilityKBelP) = 2 := by
  native_decide

/-!
## Interpretation

The categorical dynamic state space of a single four-valued belief/knowledge
status is the two-dimensional Boolean cube.  Its coordinates record whether
positive and negative support are on or above their respective Lockean
thresholds.

This gives a precise combinatorial distinction:

```text
0 walls: robust / same FDE status
1 wall : one support side changes threshold phase
2 walls: both support sides change threshold phase
```

Complete Dynamic Epistemic Reachability says every ordered pair of vertices is
realizable. Threshold-Side Robustness identifies the zero-displacement region.
The remaining one- and two-wall classes quantify the minimal categorical
change between the endpoints.

Working name: **Threshold Square Geometry**.
-/

end PEL4
