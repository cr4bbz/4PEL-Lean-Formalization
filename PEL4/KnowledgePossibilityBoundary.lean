import PEL4.KnowledgePossibility

namespace PEL4

/-!
# Possibility duality boundary

`KnowledgePossibility.lean` establishes that raw accessibility possibility and
the internal dual `not K(not phi)` agree on homogeneous examples but can diverge
under accessible FDE-value heterogeneity.

This module isolates the exact boundary.

For the evidence-stable knowledge candidate, the internal dual has the component
form

  dual.pos = not Stable(phi) OR Diamond_raw+(phi)
  dual.neg = Diamond_raw-(phi) AND Stable(phi).

Hence stability makes the dual coincide with raw possibility. Under instability
the dual collapses to strict `T`, so equality can survive only when raw
possibility is already `T`.
-/

/-- Component form of the internal knowledge dual. It exposes exactly where
accessible FDE instability enters the modal dual. -/
theorem knowledge_dual_possibility_components
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    knowledgeDualPossibilityValue m i w phi =
      { pos := (!accessibleFDEValueStable m i w phi) ||
          rawPossibilityPositive m i w phi
      , neg := rawPossibilityNegative m i w phi &&
          accessibleFDEValueStable m i w phi } := by
  unfold knowledgeDualPossibilityValue
  unfold evidenceStableKnowledgeValue
  unfold evidenceStableKnowledgePositive
  unfold evidenceStableKnowledgeNegative
  rw [accessible_negation_preserves_stability m i w phi]
  rfl

/-- Stable accessible FDE information restores the classical-looking modal
duality between raw possibility and `not K(not phi)`. -/
theorem raw_possibility_eq_knowledge_dual_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (hstable : accessibleFDEValueStable m i w phi = true) :
    rawPossibilityValue m i w phi =
      knowledgeDualPossibilityValue m i w phi := by
  rw [knowledge_dual_possibility_components m i w phi]
  unfold rawPossibilityValue
  simp [hstable]

/-- Under accessible instability the internal dual is `T`; therefore equality
with raw possibility holds exactly when raw possibility is itself `T`. -/
theorem raw_possibility_eq_knowledge_dual_of_instability_iff_true
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (hunstable : accessibleFDEValueStable m i w phi = false) :
    rawPossibilityValue m i w phi =
        knowledgeDualPossibilityValue m i w phi ↔
      rawPossibilityValue m i w phi = FDEValue.T := by
  rw [knowledge_dual_possibility_true_of_instability m i w phi hunstable]

/-- Exact Possibility Duality Boundary Theorem.

Raw accessibility possibility agrees with the internal knowledge dual iff the
accessible FDE value is stable, or the raw possibility value is already strict
`T`. The second disjunct records accidental agreement under instability. -/
theorem raw_possibility_eq_knowledge_dual_iff_stable_or_raw_true
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    rawPossibilityValue m i w phi =
        knowledgeDualPossibilityValue m i w phi ↔
      accessibleFDEValueStable m i w phi = true ∨
        rawPossibilityValue m i w phi = FDEValue.T := by
  cases hs : accessibleFDEValueStable m i w phi with
  | false =>
      have hiff :=
        raw_possibility_eq_knowledge_dual_of_instability_iff_true
          m i w phi hs
      simpa [hs] using hiff
  | true =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        exact raw_possibility_eq_knowledge_dual_of_stable m i w phi hs

/-- If the accessible profile is unstable and raw possibility is not already
strict `T`, then the two possibility notions necessarily diverge. -/
theorem raw_possibility_ne_knowledge_dual_of_instable_nontrue
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (hunstable : accessibleFDEValueStable m i w phi = false)
    (hraw : rawPossibilityValue m i w phi ≠ FDEValue.T) :
    rawPossibilityValue m i w phi ≠
      knowledgeDualPossibilityValue m i w phi := by
  intro heq
  have hT :=
    (raw_possibility_eq_knowledge_dual_of_instability_iff_true
      m i w phi hunstable).1 heq
  exact hraw hT

/-!
## Finite witnesses around the boundary

The existing `B/F` and `N/F` examples sit on the divergence side because their
raw possibility values are respectively `B` and `N`, not `T`.

An unstable `T/F` profile is different. Raw possibility is already `T`, so the
internal dual's instability collapse also yields `T`. This is genuine equality,
but not stability-based modal duality.
-/

/-- Unstable accessible information can satisfy the equality accidentally when
raw possibility is already strict `T`. -/
theorem unstable_true_profile_is_accidental_duality :
    accessibleFDEValueStable
        (PossibilityPairModel FDEValue.T FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = false ∧
    rawPossibilityValue
        (PossibilityPairModel FDEValue.T FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.T ∧
    knowledgeDualPossibilityValue
        (PossibilityPairModel FDEValue.T FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.T := by
  native_decide

/-!
## Interpretation

The boundary has two qualitatively different regions.

1. Stable region:

     Stable(phi) -> Diamond_raw(phi) = not K(not phi).

   Here the classical-looking duality is structurally justified.

2. Unstable region:

     not Stable(phi) -> not K(not phi) = T.

   Equality can then occur only when raw possibility is independently `T`.
   Such equality is extensional coincidence, not preservation of the finer
   four-valued modal structure.

This distinction matters for Fitch. If knowability is represented by raw
accessibility possibility, replacing it with `not K(not _)` is licensed on the
stable fragment, but outside that fragment it can silently collapse glut/gap
information into strict truth.
-/

end PEL4
