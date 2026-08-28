import PEL4.TopologicalEvidenceFixedPoints
import PEL4.ModalKnowledgeTransitive

namespace PEL4

/-!
# Gate 8: full stable-knowledge idempotence on S4 frames

Gate 7 proved the raw topological statement

```text
Box(K_stable(phi)) = K_stable(phi).
```

That is not automatically the same as genuine iteration `K(K(phi))`, because
the latter recomputes evidence stability for the already formed knowledge
profile.

The existing modal development proves positive introspection from transitivity,
but only under the assumption that `K(phi)` has positive support.  The missing
case is especially four-valued: an unstable profile forces `K(phi) = F`.

This gate shows that adding reflexivity closes that gap.  On a reflexive and
transitive frame the complete stable-knowledge value is idempotent for all four
values.  A transitive but non-reflexive finite countermodel then shows that
reflexivity is genuinely doing work in the non-positive phase.
-/

/-- Generic value stability is exactly pairwise constancy on a successor neighbourhood. -/
theorem modal_value_stability_iff_successor_local_constancy
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (value : W → FDEValue) (w : W) :
    modalAccessibleValueStable (R w) value = true ↔
      SuccessorLocallyConstantAt R value w := by
  cases hR : R w with
  | nil =>
      simp [SuccessorLocallyConstantAt, modalAccessibleValueStable, hR]
  | cons first rest =>
      constructor
      · intro hStable u hu v hv
        have hStableRest : ∀ x, x ∈ rest → value x = value first := by
          unfold modalAccessibleValueStable at hStable
          simp only [List.all_eq_true] at hStable
          intro x hx
          have hEq := hStable x hx
          simpa using hEq
        have huCases : u = first ∨ u ∈ rest := by
          simpa [hR] using hu
        have hvCases : v = first ∨ v ∈ rest := by
          simpa [hR] using hv
        have huEq : value u = value first := by
          cases huCases with
          | inl h => simpa [h]
          | inr h => exact hStableRest u h
        have hvEq : value v = value first := by
          cases hvCases with
          | inl h => simpa [h]
          | inr h => exact hStableRest v h
        exact huEq.trans hvEq.symm
      · intro hConst
        unfold modalAccessibleValueStable
        simp only [List.all_eq_true]
        intro x hx
        have hEq : value x = value first :=
          hConst x (by simp [hR, hx]) first (by simp [hR])
        simpa using hEq

/-- Generic evidence-stable knowledge recovers any nonempty constant FDE profile. -/
theorem modalKnowledgeValue_recovers_nonempty_constant_profile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) (v : FDEValue)
    (hNonempty : m.R i w ≠ [])
    (hConst : ∀ u, u ∈ m.R i w → value u = v) :
    modalKnowledgeValue m i w value = v := by
  have hStable :
      modalAccessibleValueStable (m.R i w) value = true :=
    modal_stability_of_constant_profile (m.R i w) value v hConst
  have hAllPos :
      (m.R i w).all (fun u => (value u).pos) = v.pos := by
    cases hp : v.pos with
    | false =>
        cases hR : m.R i w with
        | nil => exact False.elim (hNonempty hR)
        | cons first rest =>
            have hFirst : value first = v := hConst first (by simp [hR])
            simp [hFirst, hp]
    | true =>
        simp only [List.all_eq_true]
        intro u hu
        rw [hConst u hu, hp]
  have hAnyNeg :
      (m.R i w).any (fun u => (value u).neg) = v.neg := by
    cases hn : v.neg with
    | false =>
        cases hAny : (m.R i w).any (fun u => (value u).neg) with
        | false => rfl
        | true =>
            have hWitness : ∃ u ∈ m.R i w, (value u).neg = true := by
              simpa only [List.any_eq_true] using hAny
            rcases hWitness with ⟨u, hu, hNeg⟩
            rw [hConst u hu, hn] at hNeg
            cases hNeg
    | true =>
        cases hR : m.R i w with
        | nil => exact False.elim (hNonempty hR)
        | cons first rest =>
            have hFirst : value first = v := hConst first (by simp [hR])
            simp [hFirst, hn]
  simp [modalKnowledgeValue, hStable, hAllPos, hAnyNeg]

/-- Instability of a generic FDE profile forces its knowledge value to strict false. -/
theorem modalKnowledgeValue_false_of_instability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue)
    (hUnstable : modalAccessibleValueStable (m.R i w) value = false) :
    modalKnowledgeValue m i w value = FDEValue.F := by
  simp [modalKnowledgeValue, hUnstable, FDEValue.F]

/-- Pointwise application of the stable-knowledge transform to a value profile. -/
def modalKnowledgeTransform
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (value : W → FDEValue) : W → FDEValue :=
  fun w => modalKnowledgeValue m i w value

/--
On every reflexive and transitive frame, the complete stable-knowledge transform
is idempotent, with no positivity assumption.
-/
theorem modalKnowledgeValue_idempotent_of_reflexive_transitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hRefl : SuccessorReflexive (m.R i))
    (hTrans : SuccessorTransitive (m.R i))
    (value : W → FDEValue) (w : W) :
    modalKnowledgeValue m i w (modalKnowledgeTransform m i value) =
      modalKnowledgeValue m i w value := by
  cases hStable : modalAccessibleValueStable (m.R i w) value with
  | true =>
      have hPairwise : SuccessorLocallyConstantAt (m.R i) value w :=
        (modal_value_stability_iff_successor_local_constancy
          (m.R i) value w).1 hStable
      have hConstW : ∀ u, u ∈ m.R i w → value u = value w := by
        intro u hu
        exact hPairwise u hu w (hRefl w)
      have hSource : modalKnowledgeValue m i w value = value w :=
        modalKnowledgeValue_recovers_nonempty_constant_profile
          m i w value (value w) (model_accessibility_nonempty m i w) hConstW
      have hEach : ∀ u, u ∈ m.R i w →
          modalKnowledgeTransform m i value u = value w := by
        intro u hu
        apply modalKnowledgeValue_recovers_nonempty_constant_profile
        · exact model_accessibility_nonempty m i u
        · intro v hv
          exact hConstW v (hTrans w u hu v hv)
      have hOuter :
          modalKnowledgeValue m i w (modalKnowledgeTransform m i value) =
            value w :=
        modalKnowledgeValue_recovers_nonempty_constant_profile
          m i w (modalKnowledgeTransform m i value) (value w)
          (model_accessibility_nonempty m i w) hEach
      rw [hOuter, hSource]
  | false =>
      have hSourceF : modalKnowledgeValue m i w value = FDEValue.F :=
        modalKnowledgeValue_false_of_instability m i w value hStable
      cases hOuterStable :
          modalAccessibleValueStable (m.R i w) (modalKnowledgeTransform m i value) with
      | false =>
          have hOuterF :
              modalKnowledgeValue m i w (modalKnowledgeTransform m i value) =
                FDEValue.F :=
            modalKnowledgeValue_false_of_instability
              m i w (modalKnowledgeTransform m i value) hOuterStable
          rw [hOuterF, hSourceF]
      | true =>
          have hPairwiseK :
              SuccessorLocallyConstantAt (m.R i)
                (modalKnowledgeTransform m i value) w :=
            (modal_value_stability_iff_successor_local_constancy
              (m.R i) (modalKnowledgeTransform m i value) w).1 hOuterStable
          have hConstKF : ∀ u, u ∈ m.R i w →
              modalKnowledgeTransform m i value u = FDEValue.F := by
            intro u hu
            have hEq :
                modalKnowledgeTransform m i value u =
                  modalKnowledgeTransform m i value w :=
              hPairwiseK u hu w (hRefl w)
            change modalKnowledgeValue m i u value =
              modalKnowledgeValue m i w value at hEq
            exact hEq.trans hSourceF
          have hOuterF :
              modalKnowledgeValue m i w (modalKnowledgeTransform m i value) =
                FDEValue.F :=
            modalKnowledgeValue_recovers_nonempty_constant_profile
              m i w (modalKnowledgeTransform m i value) FDEValue.F
              (model_accessibility_nonempty m i w) hConstKF
          rw [hOuterF, hSourceF]

/-- Formula-level full idempotence of primitive stable knowledge on S4 frames. -/
theorem modal_knowledge_full_idempotent_of_reflexive_transitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hRefl : SuccessorReflexive (m.R i))
    (hTrans : SuccessorTransitive (m.R i))
    (w : W) (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i (ModalFormula.know i phi)) =
      evalModal m w (ModalFormula.know i phi) := by
  change modalKnowledgeValue m i w
      (fun u => modalKnowledgeValue m i u (fun v => evalModal m v phi)) =
    modalKnowledgeValue m i w (fun u => evalModal m u phi)
  exact modalKnowledgeValue_idempotent_of_reflexive_transitive
    m i hRefl hTrans (fun u => evalModal m u phi) w

/-!
## Sharpness: transitivity without reflexivity

At the root, the accessible raw values are `T` and `B`, so `K p = F` by
instability.  Yet both accessible worlds themselves know `p` as `T`: one sees
itself at `T`, while the `B` world sees only the `T` world.  The relation is
transitive but not reflexive.  Therefore the root sees the homogeneous profile
`T,T` after one knowledge step and obtains `K K p = T`.
-/

inductive FullIdemAtom where
  | p
deriving DecidableEq, Repr

inductive FullIdemAgent where
  | a
deriving DecidableEq, Repr

inductive FullIdemWorld where
  | root | left | right
deriving DecidableEq, Repr

def fullIdemR : FullIdemAgent → FullIdemWorld → FiniteSet FullIdemWorld
  | _, FullIdemWorld.root => [FullIdemWorld.left, FullIdemWorld.right]
  | _, FullIdemWorld.left => [FullIdemWorld.left]
  | _, FullIdemWorld.right => [FullIdemWorld.left]

def fullIdemVal : FullIdemWorld → FullIdemAtom → FDEValue
  | FullIdemWorld.root, _ => FDEValue.T
  | FullIdemWorld.left, _ => FDEValue.T
  | FullIdemWorld.right, _ => FDEValue.B

def fullIdemMu : FullIdemWorld → FiniteSet FullIdemWorld → Rat
  | FullIdemWorld.root, S =>
      let pl := if S.contains FullIdemWorld.left then (1 : Rat) / 2 else 0
      let pr := if S.contains FullIdemWorld.right then (1 : Rat) / 2 else 0
      pl + pr
  | FullIdemWorld.left, S =>
      if S.contains FullIdemWorld.left then 1 else 0
  | FullIdemWorld.right, S =>
      if S.contains FullIdemWorld.left then 1 else 0

def FullIdemModel : Model FullIdemWorld FullIdemAgent FullIdemAtom :=
  { worlds := [FullIdemWorld.root, FullIdemWorld.left, FullIdemWorld.right]
  , R := fullIdemR
  , mu := fun _ w => fullIdemMu w
  , val := fullIdemVal
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

def fullIdemP : ModalFormula FullIdemAtom FullIdemAgent :=
  ModalFormula.prop FullIdemAtom.p

/-- The countermodel relation is globally transitive. -/
theorem full_idem_countermodel_transitive :
    SuccessorTransitive (FullIdemModel.R FullIdemAgent.a) := by
  intro w u hu v hv
  cases w <;> cases u <;> cases v <;>
    simp [FullIdemModel, fullIdemR] at *

/-- The same relation is not reflexive at the root. -/
theorem full_idem_countermodel_not_reflexive :
    ¬ SuccessorReflexive (FullIdemModel.R FullIdemAgent.a) := by
  intro hRefl
  have hRoot := hRefl FullIdemWorld.root
  simp [FullIdemModel, fullIdemR] at hRoot

/-- At the non-reflexive root, first-order stable knowledge is strict false. -/
theorem full_idem_countermodel_k_is_false :
    evalModal FullIdemModel FullIdemWorld.root
      (ModalFormula.know FullIdemAgent.a fullIdemP) = FDEValue.F := by
  native_decide

/-- But one further stable-knowledge iteration becomes strict true. -/
theorem full_idem_countermodel_kk_is_true :
    evalModal FullIdemModel FullIdemWorld.root
      (ModalFormula.know FullIdemAgent.a
        (ModalFormula.know FullIdemAgent.a fullIdemP)) = FDEValue.T := by
  native_decide

/-- Hence transitivity alone does not give full four-valued knowledge idempotence. -/
theorem full_knowledge_idempotence_fails_on_transitive_nonreflexive_frame :
    evalModal FullIdemModel FullIdemWorld.root
        (ModalFormula.know FullIdemAgent.a fullIdemP) = FDEValue.F ∧
      evalModal FullIdemModel FullIdemWorld.root
        (ModalFormula.know FullIdemAgent.a
          (ModalFormula.know FullIdemAgent.a fullIdemP)) = FDEValue.T := by
  exact ⟨full_idem_countermodel_k_is_false,
    full_idem_countermodel_kk_is_true⟩

/-!
## Interpretation

Gate 8 pins down the exact four-valued role of reflexivity in introspection.

* Transitivity already suffices for the positive fragment, as proved earlier in
  `PEL4.ModalKnowledgeTransitive`.
* Full value idempotence additionally needs reflexivity.
* The reason is specifically the unstable `F` phase.  Reflexivity forces the
  current knowledge value back into its own next epistemic neighbourhood.  If
  `K(phi)=F`, the outer profile therefore cannot become homogeneously non-`F`
  without contradicting stability.
* Without reflexivity, the current failure can disappear from the next
  neighbourhood entirely.  The explicit countermodel realizes the jump
  `F -> T` under one further `K`.

Thus the topological S4 reading is doing more than supplying familiar modal
axioms.  Its reflexive/interior character prevents an epistemic failure from
being erased merely by moving one modal level outward.
-/

end PEL4
