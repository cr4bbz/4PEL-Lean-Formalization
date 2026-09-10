import PEL4.DynamicCompositionalRecovery
import PEL4.ModalDynamicsThresholdCrossing

namespace PEL4

/-!
# Gate 12: directional threshold-wall recovery

The existing threshold-straddling relation is symmetric: it records that two
support masses lie on opposite sides of a threshold, but not which endpoint is
the prior state. Gate 12 orients the wall and connects its direction to gap and
glut creation at belief nodes.

The final recursive theorem refines Gate 11. Under prior probability integrity
and prior compositional recovery, posterior recovery is equivalent to the
absence of a directed gap-creation pattern at every syntactically and modally
reachable belief node.
-/

/-! ## One-dimensional directed threshold motion -/

/-- A support mass moves from below threshold to the accepted side. -/
def ThresholdRises (c before after : Rat) : Prop :=
  ¬ c ≤ before ∧ c ≤ after

/-- A support mass moves from the accepted side to below threshold. -/
def ThresholdFalls (c before after : Rat) : Prop :=
  c ≤ before ∧ ¬ c ≤ after

/-- Both endpoints remain below threshold. -/
def ThresholdStaysBelow (c before after : Rat) : Prop :=
  ¬ c ≤ before ∧ ¬ c ≤ after

/-- Both endpoints remain on or above threshold. -/
def ThresholdStaysAbove (c before after : Rat) : Prop :=
  c ≤ before ∧ c ≤ after

/-- Symmetric straddling is the disjoint union of a rise and a fall. -/
theorem thresholdStraddles_iff_rises_or_falls (c before after : Rat) :
    ThresholdStraddles c before after ↔
      ThresholdRises c before after ∨ ThresholdFalls c before after := by
  constructor
  · rintro (hFall | hRise)
    · exact Or.inr hFall
    · exact Or.inl ⟨hRise.2, hRise.1⟩
  · rintro (hRise | hFall)
    · exact Or.inr ⟨hRise.2, hRise.1⟩
    · exact Or.inl hFall

/-- Rise has the exact directed Boolean threshold signature `false -> true`. -/
theorem thresholdRises_iff_decisions (c before after : Rat) :
    ThresholdRises c before after ↔
      decide (c ≤ before) = false ∧ decide (c ≤ after) = true := by
  simp [ThresholdRises]

/-- Fall has the exact directed Boolean threshold signature `true -> false`. -/
theorem thresholdFalls_iff_decisions (c before after : Rat) :
    ThresholdFalls c before after ↔
      decide (c ≤ before) = true ∧ decide (c ≤ after) = false := by
  simp [ThresholdFalls]

/-- The four directed motions exhaust one threshold coordinate. -/
theorem thresholdMotion_exhaustive (c before after : Rat) :
    ThresholdStaysBelow c before after ∨
    ThresholdRises c before after ∨
    ThresholdFalls c before after ∨
    ThresholdStaysAbove c before after := by
  by_cases hb : c ≤ before <;> by_cases ha : c ≤ after <;>
    simp [ThresholdStaysBelow, ThresholdRises, ThresholdFalls,
      ThresholdStaysAbove, hb, ha]

/-! ## Directional motion for conditionalized modal belief -/

def ConditionalizedPositiveRises
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdRises (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedPositiveFalls
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdFalls (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedPositiveStaysBelow
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdStaysBelow (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedPositiveStaysAbove
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdStaysAbove (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedNegativeRises
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdRises (m.c i)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedNegativeFalls
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdFalls (m.c i)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedNegativeStaysBelow
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdStaysBelow (m.c i)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedNegativeStaysAbove
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  ThresholdStaysAbove (m.c i)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

/-! ## Exact endpoint phase changes -/

/-- FDE threshold state generated by positive and negative masses. -/
def thresholdPair (c positive negative : Rat) : FDEValue :=
  { pos := decide (c ≤ positive), neg := decide (c ≤ negative) }

theorem thresholdPair_T_to_N_iff
    (c p0 p1 n0 n1 : Rat)
    (hT : thresholdPair c p0 n0 = FDEValue.T) :
    thresholdPair c p1 n1 = FDEValue.N ↔
      ThresholdFalls c p0 p1 ∧ ThresholdStaysBelow c n0 n1 := by
  by_cases hp0 : c ≤ p0 <;> by_cases hp1 : c ≤ p1 <;>
    by_cases hn0 : c ≤ n0 <;> by_cases hn1 : c ≤ n1 <;>
    simp_all [thresholdPair, ThresholdFalls, ThresholdStaysBelow,
      FDEValue.T, FDEValue.N]

theorem thresholdPair_F_to_N_iff
    (c p0 p1 n0 n1 : Rat)
    (hF : thresholdPair c p0 n0 = FDEValue.F) :
    thresholdPair c p1 n1 = FDEValue.N ↔
      ThresholdFalls c n0 n1 ∧ ThresholdStaysBelow c p0 p1 := by
  by_cases hp0 : c ≤ p0 <;> by_cases hp1 : c ≤ p1 <;>
    by_cases hn0 : c ≤ n0 <;> by_cases hn1 : c ≤ n1 <;>
    simp_all [thresholdPair, ThresholdFalls, ThresholdStaysBelow,
      FDEValue.F, FDEValue.N]

theorem thresholdPair_N_to_nonGap_iff
    (c p0 p1 n0 n1 : Rat)
    (hN : thresholdPair c p0 n0 = FDEValue.N) :
    thresholdPair c p1 n1 ≠ FDEValue.N ↔
      ThresholdRises c p0 p1 ∨ ThresholdRises c n0 n1 := by
  by_cases hp0 : c ≤ p0 <;> by_cases hp1 : c ≤ p1 <;>
    by_cases hn0 : c ≤ n0 <;> by_cases hn1 : c ≤ n1 <;>
    simp_all [thresholdPair, ThresholdRises, FDEValue.N]

theorem thresholdPair_T_to_B_iff
    (c p0 p1 n0 n1 : Rat)
    (hT : thresholdPair c p0 n0 = FDEValue.T) :
    thresholdPair c p1 n1 = FDEValue.B ↔
      ThresholdStaysAbove c p0 p1 ∧ ThresholdRises c n0 n1 := by
  by_cases hp0 : c ≤ p0 <;> by_cases hp1 : c ≤ p1 <;>
    by_cases hn0 : c ≤ n0 <;> by_cases hn1 : c ≤ n1 <;>
    simp_all [thresholdPair, ThresholdStaysAbove, ThresholdRises,
      FDEValue.T, FDEValue.B]

theorem thresholdPair_F_to_B_iff
    (c p0 p1 n0 n1 : Rat)
    (hF : thresholdPair c p0 n0 = FDEValue.F) :
    thresholdPair c p1 n1 = FDEValue.B ↔
      ThresholdStaysAbove c n0 n1 ∧ ThresholdRises c p0 p1 := by
  by_cases hp0 : c ≤ p0 <;> by_cases hp1 : c ≤ p1 <;>
    by_cases hn0 : c ≤ n0 <;> by_cases hn1 : c ≤ n1 <;>
    simp_all [thresholdPair, ThresholdStaysAbove, ThresholdRises,
      FDEValue.F, FDEValue.B]

/-- Exact directed pattern by which a prior classical threshold pair becomes a
gap. -/
def DirectionalGapPattern
    (c p0 p1 n0 n1 : Rat) : Prop :=
  (thresholdPair c p0 n0 = FDEValue.T ∧
    ThresholdFalls c p0 p1 ∧ ThresholdStaysBelow c n0 n1) ∨
  (thresholdPair c p0 n0 = FDEValue.F ∧
    ThresholdFalls c n0 n1 ∧ ThresholdStaysBelow c p0 p1)

/-- Exact directed pattern by which a prior classical threshold pair becomes a
glut. -/
def DirectionalGlutPattern
    (c p0 p1 n0 n1 : Rat) : Prop :=
  (thresholdPair c p0 n0 = FDEValue.T ∧
    ThresholdStaysAbove c p0 p1 ∧ ThresholdRises c n0 n1) ∨
  (thresholdPair c p0 n0 = FDEValue.F ∧
    ThresholdStaysAbove c n0 n1 ∧ ThresholdRises c p0 p1)

theorem classical_thresholdPair_to_N_iff_directionalGap
    (c p0 p1 n0 n1 : Rat)
    (hClassical : IsClassicalValue (thresholdPair c p0 n0)) :
    thresholdPair c p1 n1 = FDEValue.N ↔
      DirectionalGapPattern c p0 p1 n0 n1 := by
  rcases hClassical with hT | hF
  · rw [thresholdPair_T_to_N_iff c p0 p1 n0 n1 hT]
    have hTF : FDEValue.T ≠ FDEValue.F := by decide +kernel
    simp [DirectionalGapPattern, hT, hTF]
  · rw [thresholdPair_F_to_N_iff c p0 p1 n0 n1 hF]
    have hFT : FDEValue.F ≠ FDEValue.T := by decide +kernel
    simp [DirectionalGapPattern, hF, hFT]

theorem classical_thresholdPair_to_B_iff_directionalGlut
    (c p0 p1 n0 n1 : Rat)
    (hClassical : IsClassicalValue (thresholdPair c p0 n0)) :
    thresholdPair c p1 n1 = FDEValue.B ↔
      DirectionalGlutPattern c p0 p1 n0 n1 := by
  rcases hClassical with hT | hF
  · rw [thresholdPair_T_to_B_iff c p0 p1 n0 n1 hT]
    have hTF : FDEValue.T ≠ FDEValue.F := by decide +kernel
    simp [DirectionalGlutPattern, hT, hTF]
  · rw [thresholdPair_F_to_B_iff c p0 p1 n0 n1 hF]
    have hFT : FDEValue.F ≠ FDEValue.T := by decide +kernel
    simp [DirectionalGlutPattern, hF, hFT]

/-! ## Modal belief specialization -/

def ConditionalizedBeliefGapPattern
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  DirectionalGapPattern (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

def ConditionalizedBeliefGlutPattern
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  DirectionalGlutPattern (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)

theorem evalModal_bel_eq_thresholdPair
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.bel i phi) =
      thresholdPair (m.c i)
        (modalPositiveBeliefMass m i w phi)
        (modalNegativeBeliefMass m i w phi) := by
  exact evalModal_bel_eq_threshold_pair m i w phi

/-- A belief node is threshold-complete exactly when its value is not the gap
vertex `N`. -/
theorem beliefThresholdComplete_iff_evalModal_bel_ne_N
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    BeliefThresholdComplete m i w (fun u => evalModal m u phi) ↔
      evalModal m w (ModalFormula.bel i phi) ≠ FDEValue.N := by
  rw [evalModal_bel_eq_thresholdPair]
  change
    (decide (m.c i ≤ modalPositiveBeliefMass m i w phi) = true ∨
      decide (m.c i ≤ modalNegativeBeliefMass m i w phi) = true) ↔
    thresholdPair (m.c i)
      (modalPositiveBeliefMass m i w phi)
      (modalNegativeBeliefMass m i w phi) ≠ FDEValue.N
  by_cases hp : m.c i ≤ modalPositiveBeliefMass m i w phi <;>
    by_cases hn : m.c i ≤ modalNegativeBeliefMass m i w phi <;>
    simp [thresholdPair, hp, hn, FDEValue.N]

/-- Under a prior classical belief value, posterior gap creation is exactly the
directed gap pattern. -/
theorem conditionalization_classical_belief_to_N_iff_directionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hClassical :
      IsClassicalValue (evalModal m w (ModalFormula.bel i phi))) :
    evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi) =
        FDEValue.N ↔
      ConditionalizedBeliefGapPattern m E hAdm i w phi := by
  rw [evalModal_bel_eq_thresholdPair] at hClassical ⊢
  exact classical_thresholdPair_to_N_iff_directionalGap
    (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
    hClassical

/-- Under a prior classical belief value, posterior glut creation is exactly
the directed glut pattern. -/
theorem conditionalization_classical_belief_to_B_iff_directionalGlut
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hClassical :
      IsClassicalValue (evalModal m w (ModalFormula.bel i phi))) :
    evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi) =
        FDEValue.B ↔
      ConditionalizedBeliefGlutPattern m E hAdm i w phi := by
  rw [evalModal_bel_eq_thresholdPair] at hClassical ⊢
  exact classical_thresholdPair_to_B_iff_directionalGlut
    (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
    hClassical

/-- A prior gap becomes complete exactly when at least one support coordinate
rises through threshold. -/
theorem conditionalization_N_belief_becomes_complete_iff_rise
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hN : evalModal m w (ModalFormula.bel i phi) = FDEValue.N) :
    BeliefThresholdComplete (conditionalize m E hAdm) i w
        (fun u => evalModal (conditionalize m E hAdm) u phi) ↔
      ConditionalizedPositiveRises m E hAdm i w phi ∨
      ConditionalizedNegativeRises m E hAdm i w phi := by
  rw [beliefThresholdComplete_iff_evalModal_bel_ne_N]
  rw [evalModal_bel_eq_thresholdPair] at hN ⊢
  exact thresholdPair_N_to_nonGap_iff
    (m.c i)
    (modalPositiveBeliefMass m i w phi)
    (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
    (modalNegativeBeliefMass m i w phi)
    (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
    hN

/-! ## Recursive directional recovery criterion -/

/-- No directed gap-creation pattern occurs at any belief node reachable from
`phi` at `w`. -/
def ModalFormula.NoDirectionalGapAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E) :
    W → ModalFormula Atom Ag → Prop
  | _, ModalFormula.prop _ => True
  | w, ModalFormula.not phi =>
      ModalFormula.NoDirectionalGapAt m E hAdm w phi
  | w, ModalFormula.and phi psi =>
      ModalFormula.NoDirectionalGapAt m E hAdm w phi ∧
      ModalFormula.NoDirectionalGapAt m E hAdm w psi
  | w, ModalFormula.bel i phi =>
      (∀ u, u ∈ m.R i w →
        ModalFormula.NoDirectionalGapAt m E hAdm u phi) ∧
      ¬ ConditionalizedBeliefGapPattern m E hAdm i w phi
  | w, ModalFormula.know i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.NoDirectionalGapAt m E hAdm u phi
  | w, ModalFormula.poss i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.NoDirectionalGapAt m E hAdm u phi

/-- Gate-12 local bridge from the Gate-11 completeness predicate to the exact
absence of directional gap patterns. -/
theorem postUpdateBeliefCompleteAt_iff_noDirectionalGapAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag) :
    ∀ w,
      ModalFormula.CompositionalRecoveryAt m w phi →
      (ModalFormula.PostUpdateBeliefCompleteAt m E hAdm w phi ↔
        ModalFormula.NoDirectionalGapAt m E hAdm w phi) := by
  induction phi with
  | prop p =>
      intro w _
      exact Iff.rfl
  | not phi ih =>
      intro w hBefore
      exact ih w hBefore
  | and phi psi ihPhi ihPsi =>
      intro w hBefore
      constructor
      · intro hPost
        exact
          ⟨(ihPhi w hBefore.1).1 hPost.1,
            (ihPsi w hBefore.2).1 hPost.2⟩
      · intro hNoGap
        exact
          ⟨(ihPhi w hBefore.1).2 hNoGap.1,
            (ihPsi w hBefore.2).2 hNoGap.2⟩
  | bel i phi ih =>
      intro w hBefore
      have hClassical :
          IsClassicalValue
            (evalModal m w (ModalFormula.bel i phi)) :=
        evalModal_isClassical_of_compositionalRecovery
          m hIntegrity (ModalFormula.bel i phi) w hBefore
      have hCompleteIff :
          BeliefThresholdComplete (conditionalize m E hAdm) i w
              (fun u => evalModal (conditionalize m E hAdm) u phi) ↔
            ¬ ConditionalizedBeliefGapPattern m E hAdm i w phi := by
        rw [beliefThresholdComplete_iff_evalModal_bel_ne_N]
        exact not_congr
          (conditionalization_classical_belief_to_N_iff_directionalGap
            m E hAdm i w phi hClassical)
      constructor
      · intro hPost
        exact
          ⟨fun u hu => (ih u (hBefore.1 u hu)).1 (hPost.1 u hu),
            hCompleteIff.1 hPost.2⟩
      · intro hNoGap
        exact
          ⟨fun u hu => (ih u (hBefore.1 u hu)).2 (hNoGap.1 u hu),
            hCompleteIff.2 hNoGap.2⟩
  | know i phi ih =>
      intro w hBefore
      constructor
      · intro hPost u hu
        exact (ih u (hBefore u hu)).1 (hPost u hu)
      · intro hNoGap u hu
        exact (ih u (hBefore u hu)).2 (hNoGap u hu)
  | poss i phi ih =>
      intro w hBefore
      constructor
      · intro hPost u hu
        exact (ih u (hBefore u hu)).1 (hPost u hu)
      · intro hNoGap u hu
        exact (ih u (hBefore u hu)).2 (hNoGap u hu)

def ModalFormula.NoDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, ModalFormula.NoDirectionalGapAt m E hAdm w phi

/-- Gate-12 main theorem: on an integrity-certified prior model, a recovered
modal formula remains recovered after conditionalization exactly when no
reachable belief node exhibits the directed gap-creation pattern. -/
theorem compositionalRecovery_conditionalize_iff_noDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalFormula.CompositionalRecovery m phi) :
    ModalFormula.CompositionalRecovery (conditionalize m E hAdm) phi ↔
      ModalFormula.NoDirectionalGap m E hAdm phi := by
  rw [compositionalRecovery_conditionalize_iff_postUpdateBeliefComplete
    m E hAdm phi hBefore]
  constructor
  · intro hPost w
    exact
      (postUpdateBeliefCompleteAt_iff_noDirectionalGapAt
        m hIntegrity E hAdm phi w (hBefore w)).1 (hPost w)
  · intro hNoGap w
    exact
      (postUpdateBeliefCompleteAt_iff_noDirectionalGapAt
        m hIntegrity E hAdm phi w (hBefore w)).2 (hNoGap w)

/-! ## Finite witnesses for the directional patterns -/

/-- The Gate-11 fracture witness realizes the exact directed gap pattern at
world `b`. -/
theorem dynamic_instability_b_realizes_directionalGap :
    ConditionalizedBeliefGapPattern
      DynamicInstabilityModel dynamicInstabilityEvidence
      dynamic_instability_evidence_admissible
      DynamicInstabilityAgent.i DynamicInstabilityWorld.b
      dynamicInstabilityP := by
  apply
    (conditionalization_classical_belief_to_N_iff_directionalGap
      DynamicInstabilityModel dynamicInstabilityEvidence
      dynamic_instability_evidence_admissible
      DynamicInstabilityAgent.i DynamicInstabilityWorld.b
      dynamicInstabilityP (Or.inl
        dynamic_instability_belief_profile_before.2.1)).1
  exact dynamic_instability_belief_profile_after.2.1

/-- The Gate-11 restoration witness leaves the gap at world `b` through at
least one upward directed threshold crossing. -/
theorem dynamic_restoration_b_realizes_thresholdRise :
    ConditionalizedPositiveRises
        DynamicRestorationModel dynamicRestorationEvidence
        dynamic_restoration_evidence_admissible
        DynamicInstabilityAgent.i DynamicInstabilityWorld.b
        dynamicInstabilityP ∨
      ConditionalizedNegativeRises
        DynamicRestorationModel dynamicRestorationEvidence
        dynamic_restoration_evidence_admissible
        DynamicInstabilityAgent.i DynamicInstabilityWorld.b
        dynamicInstabilityP := by
  apply
    (conditionalization_N_belief_becomes_complete_iff_rise
      DynamicRestorationModel dynamicRestorationEvidence
      dynamic_restoration_evidence_admissible
      DynamicInstabilityAgent.i DynamicInstabilityWorld.b
      dynamicInstabilityP
      dynamic_restoration_belief_profile_before.2.1).1
  exact beliefThresholdComplete_of_evalModal_bel_eq_T
    DynamicRestorationUpdated DynamicInstabilityAgent.i
    DynamicInstabilityWorld.b dynamicInstabilityP
    dynamic_restoration_belief_profile_after.2.1

/-- The complete reachability family also realizes a directed glut pattern:
starting at `T`, negative support rises while positive support remains above. -/
theorem dynamic_reachability_T_to_B_realizes_directionalGlut :
    ConditionalizedBeliefGlutPattern
      (DynamicReachabilityModel FDEValue.T FDEValue.B)
      dynamicReachabilityEvidence
      (dynamic_reachability_evidence_admissible FDEValue.T FDEValue.B)
      DynamicReachabilityAgent.i DynamicReachabilityWorld.focus
      dynamicReachabilityP := by
  apply
    (conditionalization_classical_belief_to_B_iff_directionalGlut
      (DynamicReachabilityModel FDEValue.T FDEValue.B)
      dynamicReachabilityEvidence
      (dynamic_reachability_evidence_admissible FDEValue.T FDEValue.B)
      DynamicReachabilityAgent.i DynamicReachabilityWorld.focus
      dynamicReachabilityP
      (Or.inl (dynamic_reachability_belief_before
        FDEValue.T FDEValue.B DynamicReachabilityWorld.focus))).1
  exact dynamic_reachability_belief_after
    FDEValue.T FDEValue.B DynamicReachabilityWorld.focus

end PEL4
