import PEL4.LockeanThresholdPhaseTransition

namespace PEL4

/-!
# Gate 7: model-independent threshold phase geometry

The legacy `Model` fixes `c > 1/2`. To understand why that assumption removes
threshold gluts but leaves threshold gaps possible, this file factors the
threshold arithmetic away from the model.

For complementary masses `p + n = 1`, the critical point is one half:

* `c ≤ 1/2` guarantees threshold completeness, so gaps are impossible;
* `c > 1/2` guarantees threshold consistency, so gluts are impossible;
* at the exact tie `p = n = 1/2`, every threshold is nevertheless
  non-regular: `c ≤ 1/2` produces a glut-like pair, whereas `c > 1/2`
  produces a gap-like pair.

Thus no inclusive Lockean threshold makes every complementary probability
profile classically two-valued. Exact 50/50 ties are the unavoidable boundary.
-/

/-- The positive and negative masses exhaust one unit of probability. -/
def ComplementaryMasses (p n : Rat) : Prop :=
  p + n = 1

/-- At least one threshold decision fires. -/
def ThresholdCompleteAt (c p n : Rat) : Prop :=
  c ≤ p ∨ c ≤ n

/-- The two threshold decisions do not both fire. -/
def ThresholdConsistentAt (c p n : Rat) : Prop :=
  ¬ (c ≤ p ∧ c ≤ n)

/-- Both threshold decisions fire, the abstract `B`-like phase. -/
def ThresholdGlutAt (c p n : Rat) : Prop :=
  c ≤ p ∧ c ≤ n

/-- Neither threshold decision fires, the abstract `N`-like phase. -/
def ThresholdGapAt (c p n : Rat) : Prop :=
  ¬ c ≤ p ∧ ¬ c ≤ n

/-- Exactly one threshold decision fires. -/
def ThresholdRegularAt (c p n : Rat) : Prop :=
  ThresholdCompleteAt c p n ∧ ThresholdConsistentAt c p n

/-- A threshold gap is exactly failure of threshold completeness. -/
theorem thresholdGapAt_iff_not_complete
    (c p n : Rat) :
    ThresholdGapAt c p n ↔ ¬ ThresholdCompleteAt c p n := by
  unfold ThresholdGapAt ThresholdCompleteAt
  constructor
  · intro h hComplete
    rcases hComplete with hp | hn
    · exact h.1 hp
    · exact h.2 hn
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hn
      exact h (Or.inr hn)

/-- A threshold glut is exactly failure of threshold consistency. -/
theorem thresholdGlutAt_iff_not_consistent
    (c p n : Rat) :
    ThresholdGlutAt c p n ↔ ¬ ThresholdConsistentAt c p n := by
  unfold ThresholdGlutAt ThresholdConsistentAt
  constructor
  · intro h hCons
    exact hCons h
  · intro h
    exact Decidable.byContradiction fun hNotBoth => h hNotBoth

/-- If the threshold is at most one half, complementary masses cannot both fall
below it. Hence the threshold decision is always complete. -/
theorem complementaryMasses_atMostHalf_complete
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : c ≤ (1 / 2 : Rat)) :
    ThresholdCompleteAt c p n := by
  unfold ComplementaryMasses at hSum
  unfold ThresholdCompleteAt
  apply Decidable.byContradiction
  intro hIncomplete
  have hp : p < c := by
    apply Rat.not_le.mp
    intro hcp
    exact hIncomplete (Or.inl hcp)
  have hn : n < c := by
    apply Rat.not_le.mp
    intro hcn
    exact hIncomplete (Or.inr hcn)
  have hpn₁ : p + n < c + n :=
    (Rat.add_lt_add_right (a := p) (b := c) (c := n)).2 hp
  have hpn₂ : c + n < c + c :=
    (Rat.add_lt_add_left (a := n) (b := c) (c := c)).2 hn
  have hpn : p + n < c + c := rat_lt_trans hpn₁ hpn₂
  have hcc₁ : c + c ≤ (1 / 2 : Rat) + c :=
    (Rat.add_le_add_right (a := c) (b := (1 / 2 : Rat)) (c := c)).2 hc
  have hcc₂ : (1 / 2 : Rat) + c ≤ 1 / 2 + 1 / 2 :=
    (Rat.add_le_add_left (a := c) (b := (1 / 2 : Rat))
      (c := (1 / 2 : Rat))).2 hc
  have hcc : c + c ≤ (1 : Rat) := by
    have hle := Rat.le_trans hcc₁ hcc₂
    rw [rat_half_add_half] at hle
    exact hle
  rw [hSum] at hpn
  exact ((Rat.lt_iff_le_and_not_ge).1 hpn).2 hcc

/-- Equivalent no-gap form of the at-most-half theorem. -/
theorem complementaryMasses_atMostHalf_noGap
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : c ≤ (1 / 2 : Rat)) :
    ¬ ThresholdGapAt c p n := by
  intro hGap
  have hComplete := complementaryMasses_atMostHalf_complete p n c hSum hc
  exact (thresholdGapAt_iff_not_complete c p n).1 hGap hComplete

/-- In the strict supermajority regime, complementary masses cannot both meet
the threshold. This is the model-independent no-glut half of Gate 7. -/
theorem complementaryMasses_supermajority_noGlut
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : (1 / 2 : Rat) < c) :
    ¬ ThresholdGlutAt c p n := by
  unfold ComplementaryMasses at hSum
  unfold ThresholdGlutAt
  exact complementaryMasses_supermajority_consistent p n c hSum hc

/-- The same result expressed as threshold consistency. -/
theorem complementaryMasses_supermajority_thresholdConsistent
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : (1 / 2 : Rat) < c) :
    ThresholdConsistentAt c p n := by
  unfold ThresholdConsistentAt
  exact complementaryMasses_supermajority_noGlut p n c hSum hc

/-- Below or at the critical threshold, completeness is automatic. Therefore
regularity reduces exactly to the remaining consistency obligation. -/
theorem complementaryMasses_atMostHalf_regular_iff_consistent
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : c ≤ (1 / 2 : Rat)) :
    ThresholdRegularAt c p n ↔ ThresholdConsistentAt c p n := by
  have hComplete := complementaryMasses_atMostHalf_complete p n c hSum hc
  unfold ThresholdRegularAt
  constructor
  · intro h
    exact h.2
  · intro hCons
    exact ⟨hComplete, hCons⟩

/-- Above the critical threshold, consistency is automatic. Therefore regularity
reduces exactly to the remaining completeness obligation. -/
theorem complementaryMasses_supermajority_regular_iff_complete
    (p n c : Rat)
    (hSum : ComplementaryMasses p n)
    (hc : (1 / 2 : Rat) < c) :
    ThresholdRegularAt c p n ↔ ThresholdCompleteAt c p n := by
  have hCons := complementaryMasses_supermajority_thresholdConsistent p n c hSum hc
  unfold ThresholdRegularAt
  constructor
  · intro h
    exact h.1
  · intro hComplete
    exact ⟨hComplete, hCons⟩

/-- The exact 50/50 profile lies on the complementary-mass line. -/
theorem halfHalf_complementary :
    ComplementaryMasses (1 / 2 : Rat) (1 / 2 : Rat) := by
  exact rat_half_add_half

/-- At a 50/50 tie, every threshold at or below one half fires on both sides. -/
theorem halfHalf_thresholdGlut_iff_atMostHalf
    (c : Rat) :
    ThresholdGlutAt c (1 / 2 : Rat) (1 / 2 : Rat) ↔
      c ≤ (1 / 2 : Rat) := by
  unfold ThresholdGlutAt
  constructor
  · intro h
    exact h.1
  · intro hc
    exact ⟨hc, hc⟩

/-- At a 50/50 tie, every strict supermajority threshold fires on neither side. -/
theorem halfHalf_thresholdGap_iff_supermajority
    (c : Rat) :
    ThresholdGapAt c (1 / 2 : Rat) (1 / 2 : Rat) ↔
      (1 / 2 : Rat) < c := by
  unfold ThresholdGapAt
  constructor
  · intro h
    exact Rat.not_le.mp h.1
  · intro hc
    have hnot : ¬ c ≤ (1 / 2 : Rat) := Rat.not_le.mpr hc
    exact ⟨hnot, hnot⟩

/-- The critical threshold itself places a 50/50 tie in the glut-like phase. -/
theorem halfHalf_at_half_isGlut :
    ThresholdGlutAt (1 / 2 : Rat) (1 / 2 : Rat) (1 / 2 : Rat) := by
  exact ⟨Rat.le_refl, Rat.le_refl⟩

/-- The critical threshold itself is not a gap at a 50/50 tie. -/
theorem halfHalf_at_half_notGap :
    ¬ ThresholdGapAt (1 / 2 : Rat) (1 / 2 : Rat) (1 / 2 : Rat) := by
  intro h
  exact h.1 Rat.le_refl

/-- Below one half, the 50/50 tie is a glut witness. -/
theorem submajority_has_tie_glut
    (c : Rat)
    (hc : c < (1 / 2 : Rat)) :
    ThresholdGlutAt c (1 / 2 : Rat) (1 / 2 : Rat) := by
  exact (halfHalf_thresholdGlut_iff_atMostHalf c).2 (Rat.le_of_lt hc)

/-- Above one half, the 50/50 tie is a gap witness. -/
theorem supermajority_has_tie_gap
    (c : Rat)
    (hc : (1 / 2 : Rat) < c) :
    ThresholdGapAt c (1 / 2 : Rat) (1 / 2 : Rat) := by
  exact (halfHalf_thresholdGap_iff_supermajority c).2 hc

/-- No inclusive threshold makes the exact 50/50 complementary profile regular.
This is the sharp obstruction behind Gate 6's belief counterexample. -/
theorem halfHalf_never_thresholdRegular
    (c : Rat) :
    ¬ ThresholdRegularAt c (1 / 2 : Rat) (1 / 2 : Rat) := by
  intro hRegular
  by_cases hc : c ≤ (1 / 2 : Rat)
  · have hGlut : ThresholdGlutAt c (1 / 2 : Rat) (1 / 2 : Rat) :=
      (halfHalf_thresholdGlut_iff_atMostHalf c).2 hc
    exact hRegular.2 hGlut
  · have hGap : ThresholdGapAt c (1 / 2 : Rat) (1 / 2 : Rat) := by
      exact ⟨hc, hc⟩
    have hNotComplete := (thresholdGapAt_iff_not_complete
      c (1 / 2 : Rat) (1 / 2 : Rat)).1 hGap
    exact hNotComplete hRegular.1

/-- Phase dichotomy at the tie profile: thresholds at/below one half are
`B`-like, strict supermajority thresholds are `N`-like. -/
theorem halfHalf_phase_dichotomy
    (c : Rat) :
    (c ≤ (1 / 2 : Rat) ∧
      ThresholdGlutAt c (1 / 2 : Rat) (1 / 2 : Rat)) ∨
    ((1 / 2 : Rat) < c ∧
      ThresholdGapAt c (1 / 2 : Rat) (1 / 2 : Rat)) := by
  by_cases hc : c ≤ (1 / 2 : Rat)
  · exact Or.inl ⟨hc, (halfHalf_thresholdGlut_iff_atMostHalf c).2 hc⟩
  · have hgt : (1 / 2 : Rat) < c := Rat.not_le.mp hc
    exact Or.inr ⟨hgt, (halfHalf_thresholdGap_iff_supermajority c).2 hgt⟩

end PEL4
