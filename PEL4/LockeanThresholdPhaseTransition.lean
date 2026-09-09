import PEL4.BeliefClassicalRecovery
import PEL4.FiniteProbabilityIntegrity
import PEL4.ModalFormulaClassicalRecovery
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Gate 7: Lockean threshold phase transition

Gate 6 identified `BeliefThresholdRegular` as the exact local condition under
which Lockean belief remains in the recovered classical `{T,F}` sector.  The
condition was semantic, however: threshold consistency and threshold
completeness were still obligations rather than consequences of the stronger
probability layer.

Gate 7 begins the missing bridge.  On an integrity-certified local probability
space, a classical accessible profile partitions the accessibility support into
positive and negative events.  Their masses therefore sum to one.  Since the
legacy 4-PEL `Model` already requires the Lockean threshold to be strictly above
one half, both threshold decisions cannot fire simultaneously.

Thus probabilistic integrity + a classical accessible profile derives the
*consistency* half of classical Lockean belief.  The remaining obstruction is
threshold incompleteness, i.e. the indecision gap isolated by Gate 6.
-/

/-- Accessible worlds positively supporting a semantic value profile. -/
def positiveSupportEvent
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue) : FiniteSet W :=
  filterWorlds support (fun u => (value u).pos)

/-- Accessible worlds negatively supporting a semantic value profile. -/
def negativeSupportEvent
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue) : FiniteSet W :=
  filterWorlds support (fun u => (value u).neg)

/-- Positive support is an event inside the accessibility support. -/
theorem positiveSupportEvent_subset
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue) :
    FiniteEventSubset (positiveSupportEvent support value) support := by
  intro x hx
  exact (List.mem_filter.mp hx).1

/-- Negative support is an event inside the accessibility support. -/
theorem negativeSupportEvent_subset
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue) :
    FiniteEventSubset (negativeSupportEvent support value) support := by
  intro x hx
  exact (List.mem_filter.mp hx).1

/-- Filtering a duplicate-free accessibility support preserves duplicate-freedom. -/
theorem positiveSupportEvent_nodup
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue)
    (h : support.Nodup) :
    (positiveSupportEvent support value).Nodup := by
  exact List.Pairwise.filter _ h

/-- Negative support is duplicate-free for the same reason. -/
theorem negativeSupportEvent_nodup
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue)
    (h : support.Nodup) :
    (negativeSupportEvent support value).Nodup := by
  exact List.Pairwise.filter _ h

/-- On a classical accessible profile, positive and negative support events are
set-theoretically disjoint. -/
theorem classicalSupportEvents_disjoint
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ support → IsClassicalValue (value u)) :
    FiniteEventDisjoint
      (positiveSupportEvent support value)
      (negativeSupportEvent support value) := by
  intro x hxPos hxNeg
  have hx : x ∈ support := (List.mem_filter.mp hxPos).1
  have hp : (value x).pos = true := by
    exact (List.mem_filter.mp hxPos).2
  have hn : (value x).neg = true := by
    exact (List.mem_filter.mp hxNeg).2
  rcases hClassical x hx with hT | hF
  · subst value x
    simp [FDEValue.T] at hn
  · subst value x
    simp [FDEValue.F] at hp

/-- On a classical profile every accessible world belongs to exactly one support
channel, hence the concatenation of the two filtered events is extensionally
the whole accessibility support. -/
theorem classicalSupportEvents_cover
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ support → IsClassicalValue (value u)) :
    FiniteEventExtEq
      (positiveSupportEvent support value ++
        negativeSupportEvent support value)
      support := by
  intro x
  constructor
  · intro hx
    rcases List.mem_append.mp hx with hxPos | hxNeg
    · exact (List.mem_filter.mp hxPos).1
    · exact (List.mem_filter.mp hxNeg).1
  · intro hx
    rcases hClassical x hx with hT | hF
    · have hxPos : x ∈ positiveSupportEvent support value := by
        subst value x
        simp [positiveSupportEvent, filterWorlds, hx, FDEValue.T]
      exact List.mem_append.mpr (Or.inl hxPos)
    · have hxNeg : x ∈ negativeSupportEvent support value := by
        subst value x
        simp [negativeSupportEvent, filterWorlds, hx, FDEValue.F]
      exact List.mem_append.mpr (Or.inr hxNeg)

/-- The two support events form a duplicate-free list presentation of their
classical partition. -/
theorem classicalSupportEvents_append_nodup
    {W : Type}
    (support : FiniteSet W)
    (value : W → FDEValue)
    (hSupport : support.Nodup)
    (hClassical : ∀ u, u ∈ support → IsClassicalValue (value u)) :
    (positiveSupportEvent support value ++
      negativeSupportEvent support value).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨
    positiveSupportEvent_nodup support value hSupport,
    negativeSupportEvent_nodup support value hSupport,
    ?_⟩
  intro a ha b hb hab
  subst b
  exact classicalSupportEvents_disjoint support value hClassical a ha hb

/-- Core probability bridge: under finite probability integrity, a classical
accessible value profile has complementary positive/negative support masses. -/
theorem classicalSupportMasses_sum_one
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    m.mu i w (positiveSupportEvent (m.R i w) value) +
      m.mu i w (negativeSupportEvent (m.R i w) value) = 1 := by
  let P := positiveSupportEvent (m.R i w) value
  let N := negativeSupportEvent (m.R i w) value
  have hInt := hIntegrity i w
  have hPsub : FiniteEventSubset P (m.R i w) := by
    simpa [P] using positiveSupportEvent_subset (m.R i w) value
  have hNsub : FiniteEventSubset N (m.R i w) := by
    simpa [N] using negativeSupportEvent_subset (m.R i w) value
  have hPnodup : P.Nodup := by
    simpa [P] using
      positiveSupportEvent_nodup (m.R i w) value hInt.support_nodup
  have hNnodup : N.Nodup := by
    simpa [N] using
      negativeSupportEvent_nodup (m.R i w) value hInt.support_nodup
  have hDis : FiniteEventDisjoint P N := by
    simpa [P, N] using
      classicalSupportEvents_disjoint (m.R i w) value hClassical
  have hAppendNodup : (P ++ N).Nodup := by
    simpa [P, N] using
      classicalSupportEvents_append_nodup
        (m.R i w) value hInt.support_nodup hClassical
  have hAppendSub : FiniteEventSubset (P ++ N) (m.R i w) := by
    intro x hx
    rcases List.mem_append.mp hx with hxP | hxN
    · exact hPsub x hxP
    · exact hNsub x hxN
  have hCover : FiniteEventExtEq (P ++ N) (m.R i w) := by
    simpa [P, N] using
      classicalSupportEvents_cover (m.R i w) value hClassical
  have hAdd : m.mu i w (P ++ N) = m.mu i w P + m.mu i w N :=
    hInt.add_disjoint P N hPnodup hNnodup hPsub hNsub hDis
  have hExt : m.mu i w (P ++ N) = m.mu i w (m.R i w) :=
    hInt.extensional
      (P ++ N) (m.R i w)
      hAppendNodup hInt.support_nodup
      hAppendSub (fun _ hx => hx) hCover
  calc
    m.mu i w P + m.mu i w N = m.mu i w (P ++ N) := hAdd.symm
    _ = m.mu i w (m.R i w) := hExt
    _ = 1 := hInt.total

/-- Generic arithmetic core: complementary masses cannot both meet a threshold
strictly above one half. -/
theorem complementaryMasses_supermajority_consistent
    (p n c : Rat)
    (hSum : p + n = 1)
    (hc : (1 / 2 : Rat) < c) :
    ¬ (c ≤ p ∧ c ≤ n) := by
  intro hBoth
  have hcc : c + c ≤ p + n :=
    Rat.add_le_add hBoth.1 hBoth.2
  have hHalf : (1 : Rat) < c + c := by
    have h := Rat.add_lt_add hc hc
    simpa using h
  have hOneLe : c + c ≤ 1 := by
    simpa [hSum] using hcc
  exact ((Rat.lt_iff_le_and_not_ge).1 hHalf).2 hOneLe

/-- Gate-7 supermajority theorem: finite probability integrity and a classical
accessible profile derive the consistency half of Lockean belief recovery. -/
theorem probabilityIntegrity_classicalProfile_thresholdConsistent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    BeliefThresholdConsistent m i w value := by
  have hSum := classicalSupportMasses_sum_one
    m hIntegrity i w value hClassical
  unfold BeliefThresholdConsistent
  intro hBoth
  have hp : m.c i ≤
      m.mu i w (positiveSupportEvent (m.R i w) value) := by
    simpa [beliefPositiveThresholdBit, positiveSupportEvent] using hBoth.1
  have hn : m.c i ≤
      m.mu i w (negativeSupportEvent (m.R i w) value) := by
    simpa [beliefNegativeThresholdBit, negativeSupportEvent] using hBoth.2
  exact complementaryMasses_supermajority_consistent
    (m.mu i w (positiveSupportEvent (m.R i w) value))
    (m.mu i w (negativeSupportEvent (m.R i w) value))
    (m.c i) hSum (m.c_gt_half i) ⟨hp, hn⟩

/-- Once integrity has supplied threshold consistency, classical Lockean belief
reduces exactly to threshold completeness. -/
theorem probabilityIntegrity_classicalProfile_beliefClassical_iff_complete
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    IsClassicalValue (belief m i w value) ↔
      BeliefThresholdComplete m i w value := by
  rw [belief_isClassical_iff_thresholdRegular]
  unfold BeliefThresholdRegular
  have hCons := probabilityIntegrity_classicalProfile_thresholdConsistent
    m hIntegrity i w value hClassical
  constructor
  · intro h
    exact h.1
  · intro hComplete
    exact ⟨hComplete, hCons⟩

/-!
## First Gate-7 consequence

For the legacy model class, the threshold is already constrained to `c > 1/2`.
Therefore Gate 7 does not yet quantify internally over the three regimes
`c < 1/2`, `c = 1/2`, and `c > 1/2`.  What is proved here is the scientifically
relevant supermajority regime of 4-PEL itself:

```
finite probability integrity
+ classical accessible profile
+ the model's built-in c > 1/2
        -> no threshold glut
        -> belief is classical iff at least one side is decisive.
```

A later pure threshold-geometry layer can relax the `Model` threshold contract
and classify all three regimes without weakening the semantics of existing
4-PEL models.
-/

end PEL4
