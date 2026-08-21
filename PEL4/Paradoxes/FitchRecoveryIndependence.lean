import PEL4.Paradoxes.FitchRecovery

namespace PEL4

/-!
# Independence of the local Fitch recovery assumptions

`FitchRecovery.lean` proves that positive knowledge of the Moorean conjunction

  K+(phi and not K phi)

is impossible when three local conditions hold together:

* reflexivity at the candidate witness,
* full FDE-value stability of `phi` across the accessible range,
* a no-glut condition for `K phi`.

This module tests whether any one of those assumptions can simply be dropped
while the other two remain in place.  Three finite witnesses are used.

The goal is independence in the following local sense:

  omit reflexivity  -> Fitch witness can survive;
  omit stability    -> Fitch witness can survive;
  omit no-glut      -> Fitch witness can survive.

Thus no single member of the recovery package is redundant relative to the
other two.
-/

/-!
## 1. Reflexivity independence

The root sees one witness world but does not see itself.  `p` is therefore
trivially stable over the root's singleton accessible range and `K p` is strict
`T` there.  The witness world itself sees a source where `p = F`, making
`not K p` true at the witness.  Hence the root positively knows the Moorean
conjunction even though the root is not reflexive.
-/

inductive FitchNoRefWorld where
  | root | witness | source
deriving DecidableEq, Repr

def fitchNoRefR : FitchAgent → FitchNoRefWorld → FiniteSet FitchNoRefWorld
  | _, FitchNoRefWorld.root => [FitchNoRefWorld.witness]
  | _, FitchNoRefWorld.witness => [FitchNoRefWorld.source]
  | _, FitchNoRefWorld.source => [FitchNoRefWorld.source]

def fitchNoRefVal : FitchNoRefWorld → FitchAtom → FDEValue
  | FitchNoRefWorld.root, _ => FDEValue.T
  | FitchNoRefWorld.witness, _ => FDEValue.T
  | FitchNoRefWorld.source, _ => FDEValue.F

def fitchNoRefMu : FitchNoRefWorld → FiniteSet FitchNoRefWorld → Rat
  | FitchNoRefWorld.root, S =>
      if S.contains FitchNoRefWorld.witness then 1 else 0
  | FitchNoRefWorld.witness, S =>
      if S.contains FitchNoRefWorld.source then 1 else 0
  | FitchNoRefWorld.source, S =>
      if S.contains FitchNoRefWorld.source then 1 else 0

def FitchNoRefModel : Model FitchNoRefWorld FitchAgent FitchAtom :=
  { worlds := [FitchNoRefWorld.root, FitchNoRefWorld.witness,
      FitchNoRefWorld.source]
  , R := fitchNoRefR
  , mu := fun _ w => fitchNoRefMu w
  , val := fitchNoRefVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro i w
      cases i
      cases w <;> native_decide
  , mu_empty := by
      intro i w
      cases i
      cases w <;> native_decide
  , c_gt_half := by
      intro i
      cases i
      native_decide
  , c_le_one := by
      intro i
      cases i
      native_decide
  }

/-- At the non-reflexive root, `K p` is strict `T`. -/
theorem fitch_no_ref_root_kp_true :
    evalModal FitchNoRefModel FitchNoRefWorld.root
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.T := by
  native_decide

/-- At the non-reflexive root, the Moorean conjunction is positively known. -/
theorem fitch_no_ref_root_knows_moore :
    (evalModal FitchNoRefModel FitchNoRefWorld.root
      (ModalFormula.know FitchAgent.a
        (ModalFormula.and fitchP
          (ModalFormula.not (ModalFormula.know FitchAgent.a fitchP))))).pos = true := by
  native_decide

/-- The root satisfies the two retained recovery assumptions but fails
reflexivity. -/
theorem fitch_reflexivity_assumption_is_independent :
    (evalModal FitchNoRefModel FitchNoRefWorld.root
      (ModalFormula.know FitchAgent.a
        (ModalFormula.and fitchP
          (ModalFormula.not (ModalFormula.know FitchAgent.a fitchP))))).pos = true ∧
    modalAccessibleValueStable
        (FitchNoRefModel.R FitchAgent.a FitchNoRefWorld.root)
        (fun w' => evalModal FitchNoRefModel w' fitchP) = true ∧
    ModalKnowledgeNoGlutAt
        FitchNoRefModel FitchAgent.a FitchNoRefWorld.root fitchP ∧
    FitchNoRefWorld.root ∉
      FitchNoRefModel.R FitchAgent.a FitchNoRefWorld.root := by
  constructor
  · exact fitch_no_ref_root_knows_moore
  constructor
  · native_decide
  constructor
  · intro _
    rw [fitch_no_ref_root_kp_true]
    rfl
  · native_decide

/-!
## 2. Stability independence

The already verified Fitch witness supplies this case.  It is reflexive and
`K p = F`, so the no-glut condition is vacuously satisfied.  Nevertheless
`p` is unstable over the witness's accessible range while
`K+(p and not K p)` holds.
-/

/-- The original Fitch witness keeps reflexivity and no-glut while dropping only
left-component stability. -/
theorem fitch_stability_assumption_is_independent :
    (evalModal FitchModel FitchWorld.witness fitchKMoore).pos = true ∧
    FitchWorld.witness ∈ FitchModel.R FitchAgent.a FitchWorld.witness ∧
    ModalKnowledgeNoGlutAt
        FitchModel FitchAgent.a FitchWorld.witness fitchP ∧
    modalAccessibleValueStable
        (FitchModel.R FitchAgent.a FitchWorld.witness)
        (fun w' => evalModal FitchModel w' fitchP) = false := by
  constructor
  · have h := fitch_witness_knows_moore_gluttily
    rw [h]
    rfl
  constructor
  · exact fitch_witness_is_reflexive
  constructor
  · intro hKpos
    have hk :
        evalModal FitchModel FitchWorld.witness
          (ModalFormula.know FitchAgent.a fitchP) = FDEValue.F := by
      simpa [fitchKP] using fitch_witness_kp_is_false
    rw [hk] at hKpos
    change false = true at hKpos
    cases hKpos
  · exact fitch_moore_masks_component_instability.2.1

/-!
## 3. No-glut independence

A one-world reflexive model with `p = B` makes every relevant value stable.
Because the only accessible value of `p` is `B`, evidence-stable knowledge
recovers `K p = B`.  Therefore `not K p = B`, the Moorean conjunction is `B`,
and knowledge of that conjunction is again `B`.

The Fitch witness survives precisely because glutty knowledge is permitted.
-/

inductive FitchGlutWorld where
  | only
deriving DecidableEq, Repr

def fitchGlutR : FitchAgent → FitchGlutWorld → FiniteSet FitchGlutWorld
  | _, _ => [FitchGlutWorld.only]

def fitchGlutVal : FitchGlutWorld → FitchAtom → FDEValue
  | _, _ => FDEValue.B

def fitchGlutMu : FiniteSet FitchGlutWorld → Rat
  | S => if S.contains FitchGlutWorld.only then 1 else 0

def FitchGlutModel : Model FitchGlutWorld FitchAgent FitchAtom :=
  { worlds := [FitchGlutWorld.only]
  , R := fitchGlutR
  , mu := fun _ _ => fitchGlutMu
  , val := fitchGlutVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro i w
      cases i
      cases w
      native_decide
  , mu_empty := by
      intro i w
      cases i
      cases w
      native_decide
  , c_gt_half := by
      intro i
      cases i
      native_decide
  , c_le_one := by
      intro i
      cases i
      native_decide
  }

/-- In the glut witness, `K p` itself is `B`. -/
theorem fitch_glut_kp_is_glut :
    evalModal FitchGlutModel FitchGlutWorld.only
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.B := by
  native_decide

/-- Positive knowledge of the Moorean conjunction survives in the one-world
reflexive stable model. -/
theorem fitch_glut_knows_moore :
    evalModal FitchGlutModel FitchGlutWorld.only
      (ModalFormula.know FitchAgent.a
        (ModalFormula.and fitchP
          (ModalFormula.not (ModalFormula.know FitchAgent.a fitchP)))) =
      FDEValue.B := by
  native_decide

/-- The one-world model keeps reflexivity and stability but violates exactly the
no-glut assumption. -/
theorem fitch_no_glut_assumption_is_independent :
    (evalModal FitchGlutModel FitchGlutWorld.only
      (ModalFormula.know FitchAgent.a
        (ModalFormula.and fitchP
          (ModalFormula.not (ModalFormula.know FitchAgent.a fitchP))))).pos = true ∧
    FitchGlutWorld.only ∈
      FitchGlutModel.R FitchAgent.a FitchGlutWorld.only ∧
    modalAccessibleValueStable
        (FitchGlutModel.R FitchAgent.a FitchGlutWorld.only)
        (fun w' => evalModal FitchGlutModel w' fitchP) = true ∧
    ¬ ModalKnowledgeNoGlutAt
        FitchGlutModel FitchAgent.a FitchGlutWorld.only fitchP := by
  constructor
  · rw [fitch_glut_knows_moore]
    rfl
  constructor
  · native_decide
  constructor
  · native_decide
  · intro hNoGlut
    have hKpos :
        (evalModal FitchGlutModel FitchGlutWorld.only
          (ModalFormula.know FitchAgent.a fitchP)).pos = true := by
      rw [fitch_glut_kp_is_glut]
      rfl
    have hKnegFalse := hNoGlut hKpos
    rw [fitch_glut_kp_is_glut] at hKnegFalse
    change true = false at hKnegFalse
    cases hKnegFalse

/-!
## Independence conclusion

The three finite witnesses establish pairwise retention of the other two
assumptions while the omitted one fails and positive knowledge of the Moorean
conjunction survives.

This supports calling

  reflexivity + component stability + knowledge no-glut

a locally irredundant Fitch recovery package for the present semantics.

"Irredundant" is deliberately narrower than a universal logical minimality
claim: the theorem says that none of these three assumptions follows from the
other two strongly enough to block all finite Fitch witnesses constructed here.
-/

end PEL4
