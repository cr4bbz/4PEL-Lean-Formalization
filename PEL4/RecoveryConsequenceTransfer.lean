import PEL4.CPELConsequenceBridge
import PEL4.ProbabilityIntegrityFormulaRecovery

namespace PEL4

/-!
# Gate 9: recovery transfer to logical laws and consequence

Gate 8 represents every four-valued evaluation by two Boolean CPEL channels and
identifies classical values with their anti-diagonal.  This file transfers that
pointwise result to excluded middle and explosion while keeping three levels apart:

1. recovery of one formula value at one model/world point;
2. recovery throughout one fixed model;
3. semantic consequence quantified over all models.

No proof-system completeness or unrestricted collapse to classical consequence is
claimed.  In particular, LP explosion is recovered only where the source value is
glut-free; it remains invalid over the unrestricted four-valued model class.
-/

/-! ## Local recovery predicates and laws -/

/-- A formula is gap-free at one model/world point. -/
def Formula.GapFreeAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  GapFreeValue (eval m w phi)

/-- A formula is glut-free at one model/world point. -/
def Formula.GlutFreeAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  GlutFreeValue (eval m w phi)

/-- A formula has a recovered classical value at one model/world point. -/
def Formula.ClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  IsClassicalValue (eval m w phi)

/-- Tolerant excluded middle at one model/world point. -/
def Formula.TolerantLEMAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  (eval m w (Formula.excludedMiddle phi)).pos = true

/-- Strict excluded middle at one model/world point. -/
def Formula.StrictLEMAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  eval m w (Formula.excludedMiddle phi) = FDEValue.T

/-- LP explosion from `phi ∧ ¬phi` to every possible FDE conclusion value at one
model/world point.  Quantifying over values makes the glut-free boundary exact,
without assuming that every value is denoted by a formula in the fixed model. -/
def Formula.UniversalLPExplosionAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) : Prop :=
  ∀ q : FDEValue,
    LP_valid (eval m w (Formula.contradiction phi)) q

/-- Tolerant excluded middle is exactly local gap-freedom. -/
theorem tolerantLEMAt_iff_gapFreeAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.TolerantLEMAt m w phi ↔ Formula.GapFreeAt m w phi := by
  change (excludedMiddleValue (eval m w phi)).pos = true ↔
    GapFreeValue (eval m w phi)
  exact excludedMiddle_designated_iff_gapFree (eval m w phi)

/-- Strict excluded middle is exactly local value classicality. -/
theorem strictLEMAt_iff_classicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.StrictLEMAt m w phi ↔ Formula.ClassicalAt m w phi := by
  change excludedMiddleValue (eval m w phi) = FDEValue.T ↔
    IsClassicalValue (eval m w phi)
  exact excludedMiddle_eq_T_iff_classical (eval m w phi)

/-- Value-level universal LP explosion has exactly the glut-free boundary. -/
theorem universal_LP_explosion_iff_glutFree
    (v : FDEValue) :
    (∀ q : FDEValue, LP_valid (contradictionValue v) q) ↔
      GlutFreeValue v := by
  constructor
  · intro h
    cases v with
    | mk pos neg =>
        cases pos <;> cases neg
        · simp [GlutFreeValue, isGlut]
        · simp [GlutFreeValue, isGlut]
        · simp [GlutFreeValue, isGlut]
        · have hF := h FDEValue.F
          simp [contradictionValue, FDEValue.and, FDEValue.not,
            LP_valid, FDEValue.T, FDEValue.B, FDEValue.F] at hF
  · intro h q
    exact glutFree_restores_LP_explosion v q h

/-- Formula-level universal LP explosion is exactly local glut-freedom. -/
theorem universalLPExplosionAt_iff_glutFreeAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.UniversalLPExplosionAt m w phi ↔
      Formula.GlutFreeAt m w phi := by
  change (∀ q : FDEValue,
      LP_valid (contradictionValue (eval m w phi)) q) ↔
    GlutFreeValue (eval m w phi)
  exact universal_LP_explosion_iff_glutFree (eval m w phi)

/-- Full local classical recovery is exactly the conjunction of tolerant LEM and
universal LP explosion.  The two laws remove gaps and gluts independently. -/
theorem classicalAt_iff_tolerantLEMAt_and_universalLPExplosionAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.ClassicalAt m w phi ↔
      Formula.TolerantLEMAt m w phi ∧
      Formula.UniversalLPExplosionAt m w phi := by
  rw [tolerantLEMAt_iff_gapFreeAt,
    universalLPExplosionAt_iff_glutFreeAt]
  change IsClassicalValue (eval m w phi) ↔
    EvidentiallyRegularValue (eval m w phi)
  exact (evidentiallyRegularValue_iff_classical (eval m w phi)).symm

/-! ## Gate-8 split-coordinate characterizations -/

/-- In the split CPEL representation, tolerant LEM says that at least one support
channel is true. -/
theorem tolerantLEMAt_iff_split_complete
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.TolerantLEMAt m w phi ↔
      evalCPEL m w (tr_pos phi) = true ∨
      evalCPEL m w (tr_neg phi) = true := by
  rw [tolerantLEMAt_iff_gapFreeAt, evalCPEL_tr_pos, evalCPEL_tr_neg]
  cases h : eval m w phi with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [h, Formula.GapFreeAt, GapFreeValue, isGap]

/-- In the split CPEL representation, universal LP explosion says that the two
support channels are not jointly true. -/
theorem universalLPExplosionAt_iff_split_consistent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.UniversalLPExplosionAt m w phi ↔
      ¬ (evalCPEL m w (tr_pos phi) = true ∧
         evalCPEL m w (tr_neg phi) = true) := by
  rw [universalLPExplosionAt_iff_glutFreeAt,
    evalCPEL_tr_pos, evalCPEL_tr_neg]
  cases h : eval m w phi with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [h, Formula.GlutFreeAt, GlutFreeValue, isGlut]

/-- Strict LEM is exactly Gate 8's classical anti-diagonal equation. -/
theorem strictLEMAt_iff_split_complement
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : Formula Atom Ag) :
    Formula.StrictLEMAt m w phi ↔
      evalCPEL m w (tr_neg phi) =
        !(evalCPEL m w (tr_pos phi)) := by
  rw [strictLEMAt_iff_classicalAt]
  exact isClassicalValue_iff_splitTranslations_complement m w phi

/-! ## Fixed-model recovery and consequence -/

/-- A formula is gap-free at every world of one fixed model. -/
def Formula.GapFreeIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.GapFreeAt m w phi

/-- A formula is glut-free at every world of one fixed model. -/
def Formula.GlutFreeIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.GlutFreeAt m w phi

/-- A formula is classical at every world of one fixed model. -/
def Formula.ClassicalIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.ClassicalAt m w phi

/-- Tolerant excluded middle holds throughout one fixed model. -/
def Formula.TolerantLEMIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.TolerantLEMAt m w phi

/-- Strict excluded middle holds throughout one fixed model. -/
def Formula.StrictLEMIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.StrictLEMAt m w phi

/-- Universal value-level LP explosion holds throughout one fixed model. -/
def Formula.UniversalLPExplosionIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.UniversalLPExplosionAt m w phi

theorem tolerantLEMIn_iff_gapFreeIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) :
    Formula.TolerantLEMIn m phi ↔ Formula.GapFreeIn m phi := by
  constructor <;> intro h w
  · exact (tolerantLEMAt_iff_gapFreeAt m w phi).1 (h w)
  · exact (tolerantLEMAt_iff_gapFreeAt m w phi).2 (h w)

theorem strictLEMIn_iff_classicalIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) :
    Formula.StrictLEMIn m phi ↔ Formula.ClassicalIn m phi := by
  constructor <;> intro h w
  · exact (strictLEMAt_iff_classicalAt m w phi).1 (h w)
  · exact (strictLEMAt_iff_classicalAt m w phi).2 (h w)

theorem universalLPExplosionIn_iff_glutFreeIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : Formula Atom Ag) :
    Formula.UniversalLPExplosionIn m phi ↔ Formula.GlutFreeIn m phi := by
  constructor <;> intro h w
  · exact (universalLPExplosionAt_iff_glutFreeAt m w phi).1 (h w)
  · exact (universalLPExplosionAt_iff_glutFreeAt m w phi).2 (h w)

/-- Probability-recovery admissibility yields model-wide value classicality. -/
theorem classicalIn_of_probabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (hRecovery : Formula.ProbabilityRecoveryAdmissible m phi) :
    Formula.ClassicalIn m phi := by
  intro w
  exact eval_isClassical_of_global_probabilityRecoveryAdmissible
    m hIntegrity phi hRecovery w

/-- Gate-7 recovery transfers to strict excluded middle throughout the model. -/
theorem strictLEMIn_of_probabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (hRecovery : Formula.ProbabilityRecoveryAdmissible m phi) :
    Formula.StrictLEMIn m phi :=
  (strictLEMIn_iff_classicalIn m phi).2
    (classicalIn_of_probabilityRecoveryAdmissible m hIntegrity phi hRecovery)

/-- Gate-7 recovery transfers to universal LP explosion throughout the model. -/
theorem universalLPExplosionIn_of_probabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (hRecovery : Formula.ProbabilityRecoveryAdmissible m phi) :
    Formula.UniversalLPExplosionIn m phi := by
  intro w
  exact
    (classicalAt_iff_tolerantLEMAt_and_universalLPExplosionAt m w phi).1
      (classicalIn_of_probabilityRecoveryAdmissible
        m hIntegrity phi hRecovery w) |>.2

/-- LP consequence restricted to one fixed model. -/
def LP_SemanticEntailsIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi psi : Formula Atom Ag) : Prop :=
  ∀ w, (eval m w phi).pos = true → (eval m w psi).pos = true

/-- ST consequence restricted to one fixed model. -/
def ST_SemanticEntailsIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi psi : Formula Atom Ag) : Prop :=
  ∀ w, eval m w phi = FDEValue.T → (eval m w psi).pos = true

/-- LP consequence is always at least as demanding as ST consequence in a fixed
model, because every strict antecedent is positively designated. -/
theorem LP_SemanticEntailsIn_implies_ST
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi psi : Formula Atom Ag)
    (h : LP_SemanticEntailsIn m phi psi) :
    ST_SemanticEntailsIn m phi psi := by
  intro w hT
  apply h w
  rw [hT]
  rfl

/-- Once the antecedent is classical throughout a fixed model, ST and LP
consequence coincide there.  This is a model-relative transfer theorem, not an
unrestricted global consequence collapse. -/
theorem ST_iff_LP_SemanticEntailsIn_of_classicalAntecedent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi psi : Formula Atom Ag)
    (hClassical : Formula.ClassicalIn m phi) :
    ST_SemanticEntailsIn m phi psi ↔
      LP_SemanticEntailsIn m phi psi := by
  constructor
  · intro hST w hPos
    apply hST w
    rcases hClassical w with hT | hF
    · exact hT
    · rw [hF] at hPos
      contradiction
  · exact LP_SemanticEntailsIn_implies_ST m phi psi

/-! ## Globally quantified consequence, restricted to recovered points -/

/-- LP consequence over all model/world points at which the antecedent has a
classical value.  The restriction is local to each quantified point; no
classicality premise on the consequent is needed. -/
def ClassicalRestrictedLP_SemanticEntails
    {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    IsClassicalValue (eval m w phi) →
    (eval m w phi).pos = true →
      (eval m w psi).pos = true

/-- ST consequence over the same antecedent-classical points. -/
def ClassicalRestrictedST_SemanticEntails
    {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    IsClassicalValue (eval m w phi) →
    eval m w phi = FDEValue.T →
      (eval m w psi).pos = true

/-- On the globally quantified but pointwise recovered domain, ST and LP consequence
coincide. -/
theorem classicalRestricted_ST_iff_LP
    {Atom Ag : Type} (phi psi : Formula Atom Ag) :
    ClassicalRestrictedST_SemanticEntails phi psi ↔
      ClassicalRestrictedLP_SemanticEntails phi psi := by
  constructor
  · intro hST W _ m w hPhi hPos
    apply hST m w hPhi
    rcases hPhi with hT | hF
    · exact hT
    · rw [hF] at hPos
      contradiction
  · intro hLP W _ m w hPhi hT
    apply hLP m w hPhi
    rw [hT]
    rfl

/-- Unrestricted LP consequence implies its recovered restriction. -/
theorem LP_SemanticEntails_implies_classicalRestricted
    {Atom Ag : Type} (phi psi : Formula Atom Ag)
    (h : LP_SemanticEntails phi psi) :
    ClassicalRestrictedLP_SemanticEntails phi psi := by
  intro W _ m w _ hPos
  exact h m w hPos

/-- Direct contradictions are never strictly true, independently of recovery. -/
theorem contradictionValue_ne_T (v : FDEValue) :
    contradictionValue v ≠ FDEValue.T := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [contradictionValue, FDEValue.and, FDEValue.not,
          FDEValue.T]

/-- Therefore direct contradiction entails every formula under unrestricted ST
consequence already; recovery is not needed for this consequence regime. -/
theorem contradiction_ST_SemanticEntails
    {Atom Ag : Type} (phi psi : Formula Atom Ag) :
    ST_SemanticEntails (Formula.contradiction phi) psi := by
  intro W _ m w hT
  exact False.elim (contradictionValue_ne_T (eval m w phi) hT)

/-- At points where the contradictory antecedent is recovered, direct contradiction
entails every formula under LP; the consequent need not itself be classical. -/
theorem contradiction_classicalRestrictedLP_SemanticEntails
    {Atom Ag : Type} (phi psi : Formula Atom Ag) :
    ClassicalRestrictedLP_SemanticEntails
      (Formula.contradiction phi) psi := by
  intro W _ m w hPremise hPos
  have hT : eval m w (Formula.contradiction phi) = FDEValue.T := by
    rcases hPremise with hT | hF
    · exact hT
    · rw [hF] at hPos
      contradiction
  exact False.elim (contradictionValue_ne_T (eval m w phi) hT)

/-! ## Boundary witness: recovered consequence is not unrestricted LP consequence -/

/-- A one-world boundary model with a glutty `false` atom and a strictly false
`true` atom.  Its probability component is immaterial to the propositional witness. -/
def gate9ExplosionBoundaryModel : Model Unit Unit Bool where
  worlds := [()]
  R := fun _ _ => [()]
  mu := fun _ _ S => if S = [()] then 1 else 0
  val := fun _ p => if p then FDEValue.F else FDEValue.B
  c := fun _ => 3 / 4
  mu_total := by
    intro _ _
    decide +kernel
  mu_empty := by
    intro _ _
    decide +kernel
  c_gt_half := by
    intro _
    decide +kernel
  c_le_one := by
    intro _
    decide +kernel

/-- The same explosion schema that is valid on recovered points remains invalid for
unrestricted LP consequence because the four-valued model class still contains
gluts. -/
theorem contradiction_not_LP_SemanticEntails :
    ¬ LP_SemanticEntails
      (Formula.contradiction (Formula.prop false : Formula Bool Unit))
      (Formula.prop true) := by
  intro h
  have hAt := h gate9ExplosionBoundaryModel ()
  have hConclusion := hAt (by decide +kernel)
  change false = true at hConclusion
  exact Bool.noConfusion hConclusion

/-- Explicit separation between recovered global consequence and unrestricted LP
consequence. -/
theorem classicalRestricted_explosion_not_global :
    ClassicalRestrictedLP_SemanticEntails
        (Formula.contradiction (Formula.prop false : Formula Bool Unit))
        (Formula.prop true) ∧
      ¬ LP_SemanticEntails
        (Formula.contradiction (Formula.prop false : Formula Bool Unit))
        (Formula.prop true) := by
  exact ⟨
    contradiction_classicalRestrictedLP_SemanticEntails
      (Formula.prop false : Formula Bool Unit) (Formula.prop true),
    contradiction_not_LP_SemanticEntails⟩

end PEL4
