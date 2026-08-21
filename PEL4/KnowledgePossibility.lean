import PEL4.KnowledgeConjunctionIntroduction

namespace PEL4

/-!
# Raw possibility versus the internal knowledge dual

Fitch-style knowability requires a possibility notion. In a four-valued setting
we should not silently identify raw accessibility possibility with the familiar
classical abbreviation

  Diamond phi := not K(not phi).

The evidence-stable knowledge candidate treats variation of the complete FDE
value as negative knowledge support. Consequently, instability of `not phi`
forces `K(not phi)` to `F`, and internal FDE negation then turns the dual into
`T`. Raw accessibility possibility does not in general collapse this way.

This module therefore compares the two notions before either is promoted to
object-language syntax.
-/

/-- Positive raw possibility: some accessible world positively supports `phi`. -/
def rawPossibilityPositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (m.R i w).any (fun w' => (eval m w' phi).pos)

/-- Negative raw possibility: every accessible world negatively supports `phi`.
This is the standard FDE-style negative component for an accessibility
possibility operator. -/
def rawPossibilityNegative {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (m.R i w).all (fun w' => (eval m w' phi).neg)

/-- Full four-valued raw accessibility possibility. -/
def rawPossibilityValue {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : FDEValue :=
  { pos := rawPossibilityPositive m i w phi
  , neg := rawPossibilityNegative m i w phi
  }

/-- Internal De-Morgan-style dual built from evidence-stable knowledge. This is
kept semantically separate from raw accessibility possibility. -/
def knowledgeDualPossibilityValue {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : FDEValue :=
  FDEValue.not
    (evidenceStableKnowledgeValue m i w (Formula.not phi))

/-- FDE negation is injective at the value level. The decidable equality form is
useful for rewriting the accessibility-stability predicate. -/
theorem decide_fde_not_eq_not_eq (a b : FDEValue) :
    decide (FDEValue.not a = FDEValue.not b) = decide (a = b) := by
  rcases a with ⟨apos, aneg⟩
  rcases b with ⟨bpos, bneg⟩
  cases apos <;> cases aneg <;> cases bpos <;> cases bneg <;> native_decide

/-- Internal negation preserves exactly whether the complete FDE value is stable
across the accessible range. -/
theorem accessible_negation_preserves_stability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    accessibleFDEValueStable m i w (Formula.not phi) =
      accessibleFDEValueStable m i w phi := by
  cases hR : m.R i w with
  | nil =>
      simp [accessibleFDEValueStable, hR]
  | cons first rest =>
      simp only [accessibleFDEValueStable, hR]
      change
        (rest.all fun w' =>
          decide (FDEValue.not (eval m w' phi) =
            FDEValue.not (eval m first phi))) =
        rest.all fun w' =>
          decide (eval m w' phi = eval m first phi)
      simp [decide_fde_not_eq_not_eq]

/-- Instability forces the internal knowledge dual of possibility to strict
truth. This is the key reason the dual can diverge from raw accessibility
possibility. -/
theorem knowledge_dual_possibility_true_of_instability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (h : accessibleFDEValueStable m i w phi = false) :
    knowledgeDualPossibilityValue m i w phi = FDEValue.T := by
  have hnot : accessibleFDEValueStable m i w (Formula.not phi) = false := by
    rw [accessible_negation_preserves_stability m i w phi]
    exact h
  have hk := knowledge_instability_forces_false
    m i w (Formula.not phi) hnot
  unfold knowledgeDualPossibilityValue
  rw [hk]
  rfl

/-!
## Finite comparison family

We reuse the two accessible worlds from the knowledge gate and assign arbitrary
FDE values to the left and right worlds. This lets us test stable and unstable
possibility profiles without changing the underlying 4-PEL model structure.
-/

/-- Two-world possibility comparison model. -/
def PossibilityPairModel (leftValue rightValue : FDEValue) :
    Model KnowledgeGateWorld KnowledgeGateAgent KnowledgeGateAtom :=
  { worlds := [KnowledgeGateWorld.root,
      KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , R := fun _ _ => [KnowledgeGateWorld.left, KnowledgeGateWorld.right]
  , mu := fun _ _ => knowledgeGateMu
  , val := fun world _ =>
      match world with
      | KnowledgeGateWorld.root => FDEValue.T
      | KnowledgeGateWorld.left => leftValue
      | KnowledgeGateWorld.right => rightValue
  , c := fun _ => 2 / 3
  , mu_total := by
      intro _ _
      native_decide
  , mu_empty := by
      intro _ _
      native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }

/-- On homogeneous accessible information, raw possibility and the internal
knowledge dual both recover the same complete FDE value. -/
theorem homogeneous_possibility_duality_recovers_value (v : FDEValue) :
    rawPossibilityValue (PossibilityPairModel v v)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = v ∧
    knowledgeDualPossibilityValue (PossibilityPairModel v v)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = v := by
  rcases v with ⟨pos, neg⟩
  cases pos <;> cases neg <;> native_decide

/-- A glut divergence witness. With accessible values `B` and `F`, raw
possibility is `B`, while instability makes the internal knowledge dual `T`. -/
theorem raw_and_dual_possibility_diverge_on_glut_profile :
    rawPossibilityValue (PossibilityPairModel FDEValue.B FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.B ∧
    knowledgeDualPossibilityValue (PossibilityPairModel FDEValue.B FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.T := by
  native_decide

/-- A gap divergence witness. With accessible values `N` and `F`, raw
possibility is `N`, while the internal knowledge dual again becomes `T`. -/
theorem raw_and_dual_possibility_diverge_on_gap_profile :
    rawPossibilityValue (PossibilityPairModel FDEValue.N FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.N ∧
    knowledgeDualPossibilityValue (PossibilityPairModel FDEValue.N FDEValue.F)
        KnowledgeGateAgent.a KnowledgeGateWorld.root knowledgeGateP = FDEValue.T := by
  native_decide

/-!
## Interpretation

The comparison has a simple structural shape.

When accessible information is homogeneous, raw possibility and `not K(not _)`
agree in the finite gate and reproduce the underlying FDE value. Under
heterogeneity, however, evidence-stable knowledge records instability as
negative knowledge support. Applied to `not phi`, that makes `K(not phi) = F`,
so outer internal negation produces `T` regardless of the finer raw possibility
profile.

Hence

  raw Diamond(phi)

and

  internal not K(not phi)

cannot be identified globally. The internal dual can erase glut/gap structure
by converting epistemic instability into strict truth. For a future Fitch
formalization, knowability should therefore be based on an explicit raw
accessibility possibility operator unless an equivalence theorem is proved for
a restricted fragment.
-/

end PEL4
