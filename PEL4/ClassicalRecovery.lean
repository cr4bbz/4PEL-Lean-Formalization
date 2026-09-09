import PEL4.MatroidEvidenceMinorSemantics
import PEL4.ModalProbability.StatusTransport

namespace PEL4

/-!
# Gate 5: classical recovery from evidential regularity

The purpose of this gate is not to replace FDE/4-PEL by classical logic.
Instead it asks when the classical fragment is recovered from structural
conditions on evidence.

At the coarse two-channel level three notions are separated:

* completeness: at least one of the positive/negative channels is supported;
* consistency: the positive and negative channels are not jointly supported;
* stability: a local evidence value is preserved through the accessible range.

Completeness removes the gap N. Consistency removes the glut B. Together they
isolate exactly T and F. Stability is then a modal propagation condition: if a
regular value is stable at a world, every accessible world carries that same
classical value.

This distinction also separates two familiar classical principles. Under the
LP/tolerant reading, excluded middle is recovered already from gap-freedom,
whereas ex falso is recovered already from glut-freedom. Requiring the value of
excluded middle to be strictly T needs both conditions.
-/

universe u

/-- A value has no evidential gap. -/
def GapFreeValue (v : FDEValue) : Prop :=
  isGap v = false

/-- A value has no evidential glut. -/
def GlutFreeValue (v : FDEValue) : Prop :=
  isGlut v = false

/-- Local evidential regularity: neither gap nor glut. -/
def EvidentiallyRegularValue (v : FDEValue) : Prop :=
  GapFreeValue v ∧ GlutFreeValue v

/-- Propositional classical slice of FDE. -/
def IsClassicalValue (v : FDEValue) : Prop :=
  v = FDEValue.T ∨ v = FDEValue.F

/-- A body of evidence supports at least one primitive polarity. -/
def ChannelComplete {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α) : Prop :=
  supportsChannel polarity A EvidencePolarity.positive ∨
  supportsChannel polarity A EvidencePolarity.negative

/-- A body of evidence does not jointly support both primitive polarities. -/
def ChannelConsistent {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α) : Prop :=
  ¬ (supportsChannel polarity A EvidencePolarity.positive ∧
     supportsChannel polarity A EvidencePolarity.negative)

/-- Complete and consistent coarse evidence. -/
def ChannelRegular {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α) : Prop :=
  ChannelComplete polarity A ∧ ChannelConsistent polarity A

/-- Gap-freedom is exactly coarse channel completeness for a realized value. -/
theorem realizesFDE_gapFree_iff_channelComplete
    {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α)
    (v : FDEValue)
    (h : RealizesFDE polarity A v) :
    GapFreeValue v ↔ ChannelComplete polarity A := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [GapFreeValue, isGap, ChannelComplete, RealizesFDE] at h ⊢ <;>
        aesop

/-- Glut-freedom is exactly coarse channel consistency for a realized value. -/
theorem realizesFDE_glutFree_iff_channelConsistent
    {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α)
    (v : FDEValue)
    (h : RealizesFDE polarity A v) :
    GlutFreeValue v ↔ ChannelConsistent polarity A := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [GlutFreeValue, isGlut, ChannelConsistent, RealizesFDE] at h ⊢ <;>
        aesop

/-- Regular four-valued evidence is exactly the classical T/F slice. -/
theorem evidentiallyRegularValue_iff_classical
    (v : FDEValue) :
    EvidentiallyRegularValue v ↔ IsClassicalValue v := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [EvidentiallyRegularValue, GapFreeValue, GlutFreeValue,
          isGap, isGlut, IsClassicalValue, FDEValue.T, FDEValue.F]

/-- Geometric recovery theorem: complete and consistent channel evidence
realizes exactly a classical FDE value. -/
theorem realizesFDE_channelRegular_iff_classical
    {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α)
    (v : FDEValue)
    (h : RealizesFDE polarity A v) :
    ChannelRegular polarity A ↔ IsClassicalValue v := by
  rw [← evidentiallyRegularValue_iff_classical]
  constructor
  · intro hRegular
    exact ⟨
      (realizesFDE_gapFree_iff_channelComplete polarity A v h).2 hRegular.1,
      (realizesFDE_glutFree_iff_channelConsistent polarity A v h).2 hRegular.2⟩
  · intro hRegular
    exact ⟨
      (realizesFDE_gapFree_iff_channelComplete polarity A v h).1 hRegular.1,
      (realizesFDE_glutFree_iff_channelConsistent polarity A v h).1 hRegular.2⟩

/-- FDE negation preserves the recovered classical slice. -/
theorem classicalValue_not
    (v : FDEValue)
    (h : IsClassicalValue v) :
    IsClassicalValue (FDEValue.not v) := by
  rcases h with h | h
  · subst v
    exact Or.inr rfl
  · subst v
    exact Or.inl rfl

/-- FDE conjunction restricts to classical conjunction on the T/F slice. -/
theorem classicalValue_and
    (v w : FDEValue)
    (hv : IsClassicalValue v)
    (hw : IsClassicalValue w) :
    IsClassicalValue (FDEValue.and v w) := by
  rcases hv with hv | hv <;> rcases hw with hw | hw <;>
    subst v <;> subst w <;>
    simp [IsClassicalValue, FDEValue.and, FDEValue.T, FDEValue.F]

/-- FDE disjunction restricts to classical disjunction on the T/F slice. -/
theorem classicalValue_or
    (v w : FDEValue)
    (hv : IsClassicalValue v)
    (hw : IsClassicalValue w) :
    IsClassicalValue (FDEValue.or v w) := by
  rcases hv with hv | hv <;> rcases hw with hw | hw <;>
    subst v <;> subst w <;>
    simp [IsClassicalValue, FDEValue.or, FDEValue.T, FDEValue.F]

/-- Value of excluded middle in the FDE algebra. -/
def excludedMiddleValue (v : FDEValue) : FDEValue :=
  FDEValue.or v (FDEValue.not v)

/-- Tolerant/designated excluded middle needs exactly gap-freedom. -/
theorem excludedMiddle_designated_iff_gapFree
    (v : FDEValue) :
    (excludedMiddleValue v).pos = true ↔ GapFreeValue v := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [excludedMiddleValue, FDEValue.or, FDEValue.not,
          GapFreeValue, isGap]

/-- Strict-T excluded middle characterizes the recovered classical slice. -/
theorem excludedMiddle_eq_T_iff_classical
    (v : FDEValue) :
    excludedMiddleValue v = FDEValue.T ↔ IsClassicalValue v := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [excludedMiddleValue, FDEValue.or, FDEValue.not,
          IsClassicalValue, FDEValue.T, FDEValue.F]

/-- Complete and consistent evidence restores excluded middle strictly as T. -/
theorem realizesFDE_channelRegular_restores_strict_LEM
    {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α)
    (v : FDEValue)
    (hRealizes : RealizesFDE polarity A v)
    (hRegular : ChannelRegular polarity A) :
    excludedMiddleValue v = FDEValue.T :=
  (excludedMiddle_eq_T_iff_classical v).2
    ((realizesFDE_channelRegular_iff_classical polarity A v hRealizes).1 hRegular)

/-- Value of a direct contradiction `v ∧ ¬v`. -/
def contradictionValue (v : FDEValue) : FDEValue :=
  FDEValue.and v (FDEValue.not v)

/-- A contradiction is LP-designated exactly at a glut. -/
theorem contradiction_designated_iff_glut
    (v : FDEValue) :
    (contradictionValue v).pos = true ↔ isGlut v = true := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [contradictionValue, FDEValue.and, FDEValue.not, isGlut]

/-- Under glut-freedom, LP explosion is recovered vacuously: the contradiction
premise cannot be designated. No gap-freedom assumption is required. -/
theorem glutFree_restores_LP_explosion
    (v q : FDEValue)
    (h : GlutFreeValue v) :
    LP_valid (contradictionValue v) q := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [GlutFreeValue, isGlut, contradictionValue,
          FDEValue.and, FDEValue.not, LP_valid, FDEValue.T, FDEValue.B] at h ⊢

/-- Coarse channel consistency alone suffices for LP ex falso at the realized
value. This is weaker than full classical recovery. -/
theorem realizesFDE_channelConsistency_restores_LP_explosion
    {α : Type u}
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α)
    (v q : FDEValue)
    (hRealizes : RealizesFDE polarity A v)
    (hConsistent : ChannelConsistent polarity A) :
    LP_valid (contradictionValue v) q := by
  apply glutFree_restores_LP_explosion v q
  exact (realizesFDE_glutFree_iff_channelConsistent polarity A v hRealizes).2 hConsistent

/-- Stability is not needed for local T/F recovery. It becomes relevant when
classicality must persist through a modal accessibility range. -/
theorem stable_regular_value_is_classical_through_accessibility
    {W : Type}
    (R : W → W → Prop)
    (v : W → FDEValue)
    (w : W)
    (hStable : ModalProbability.StableAt R v w)
    (hRegular : EvidentiallyRegularValue (v w)) :
    ∀ u, R w u → IsClassicalValue (v u) := by
  intro u hwu
  have huv : v u = v w := hStable u hwu
  rw [huv]
  exact (evidentiallyRegularValue_iff_classical (v w)).1 hRegular

end PEL4
