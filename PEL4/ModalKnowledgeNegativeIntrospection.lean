import PEL4.ModalKnowledgeTransitive

namespace PEL4

/-!
# Negative introspection and Euclidean frames

Positive introspection is recovered by ordinary transitivity. Negative
introspection is subtler because evidence-stable knowledge tracks the complete
FDE profile, not only universal positive support.

The classical axiom-5 frame condition is local Euclideanness:

  wRu and wRv  implies  uRv.

In the present semantics this is enough to make every successor see every
source successor, but it does not prevent a successor from seeing additional
worlds. Those additional worlds can change the complete value of `K phi` and
therefore destroy stability of `not K phi` at the source.

The gate has three parts:

* a finite Euclidean countermodel to unrestricted positive negative
  introspection;
* a semantic extensionality lemma showing that transitivity plus Euclideanness
  makes `K phi` constant over the source successor set;
* full value-idempotence of both `K K phi` and `K (not K phi)` under the combined
  frame conditions.
-/

/-- Local Euclideanness at `w`: any source successor sees every source
successor. -/
def ModalEuclideanAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) : Prop :=
  ∀ u, u ∈ m.R i w → ∀ v, v ∈ m.R i w → v ∈ m.R i u

/-- A nonempty stable profile has a single common FDE value. -/
theorem modal_constant_profile_of_stable_nonempty
    {W : Type} [DecidableEq W]
    (worlds : FiniteSet W) (value : W → FDEValue)
    (hNonempty : worlds ≠ [])
    (hStable : modalAccessibleValueStable worlds value = true) :
    ∃ v, ∀ x, x ∈ worlds → value x = v := by
  cases hR : worlds with
  | nil =>
      exact False.elim (hNonempty hR)
  | cons first rest =>
      refine ⟨value first, ?_⟩
      intro x hx
      have hxCases : x = first ∨ x ∈ rest := by
        simpa [hR] using hx
      rcases hxCases with rfl | hxRest
      · rfl
      · rw [hR] at hStable
        unfold modalAccessibleValueStable at hStable
        simp only [List.all_eq_true] at hStable
        exact hStable x hxRest

/-- Instability of a modal formula forces its evidence-stable knowledge value to
strict `F`. -/
theorem modal_knowledge_false_of_instability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hStable : modalAccessibleValueStable (m.R i w)
      (fun u => evalModal m u phi) = false) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.F := by
  change modalKnowledgeValue m i w (fun u => evalModal m u phi) = FDEValue.F
  simp [modalKnowledgeValue, hStable, FDEValue.F]

/-- If an unstable profile is embedded into a nonempty larger profile, the
larger profile is unstable as well. -/
theorem modal_instability_preserved_by_superset
    {W : Type} [DecidableEq W]
    (small big : FiniteSet W) (value : W → FDEValue)
    (hBigNonempty : big ≠ [])
    (hSub : ∀ x, x ∈ small → x ∈ big)
    (hSmall : modalAccessibleValueStable small value = false) :
    modalAccessibleValueStable big value = false := by
  cases hBig : modalAccessibleValueStable big value with
  | false =>
      exact hBig
  | true =>
      rcases modal_constant_profile_of_stable_nonempty
          big value hBigNonempty hBig with ⟨v, hConstBig⟩
      have hConstSmall : ∀ x, x ∈ small → value x = v := by
        intro x hx
        exact hConstBig x (hSub x hx)
      have hSmallTrue : modalAccessibleValueStable small value = true :=
        modal_stability_of_constant_profile small value v hConstSmall
      rw [hSmall] at hSmallTrue
      cases hSmallTrue

/-- Under local transitivity plus local Euclideanness, every immediate successor
has exactly the same evidence-stable knowledge value as the source. Membership
of successor lists need only agree extensionally; literal list equality is not
assumed. -/
theorem modal_knowledge_value_equal_at_successor_of_transitive_euclidean
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w u : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hEuclid : ModalEuclideanAt m i w)
    (hu : u ∈ m.R i w) :
    evalModal m u (ModalFormula.know i phi) =
      evalModal m w (ModalFormula.know i phi) := by
  have hNonW : m.R i w ≠ [] := model_accessibility_nonempty m i w
  have hNonU : m.R i u ≠ [] := model_accessibility_nonempty m i u
  cases hStableW : modalAccessibleValueStable (m.R i w)
      (fun x => evalModal m x phi) with
  | false =>
      have hStableU : modalAccessibleValueStable (m.R i u)
          (fun x => evalModal m x phi) = false :=
        modal_instability_preserved_by_superset
          (m.R i w) (m.R i u) (fun x => evalModal m x phi)
          hNonU (fun x hx => hEuclid u hu x hx) hStableW
      calc
        evalModal m u (ModalFormula.know i phi) = FDEValue.F :=
          modal_knowledge_false_of_instability m i u phi hStableU
        _ = evalModal m w (ModalFormula.know i phi) := by
          symm
          exact modal_knowledge_false_of_instability m i w phi hStableW
  | true =>
      rcases modal_constant_profile_of_stable_nonempty
          (m.R i w) (fun x => evalModal m x phi) hNonW hStableW with
        ⟨v, hConstW⟩
      have hConstU : ∀ x, x ∈ m.R i u → evalModal m x phi = v := by
        intro x hx
        exact hConstW x (hTrans u hu x hx)
      calc
        evalModal m u (ModalFormula.know i phi) = v :=
          modal_knowledge_recovers_nonempty_constant_profile
            m i u phi v hNonU hConstU
        _ = evalModal m w (ModalFormula.know i phi) := by
          symm
          exact modal_knowledge_recovers_nonempty_constant_profile
            m i w phi v hNonW hConstW

/-- With transitivity and Euclideanness together, the complete value of knowledge
is idempotent for all four FDE values, not merely the positive `T/B` phase. -/
theorem modal_knowledge_value_idempotent_of_transitive_euclidean
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hEuclid : ModalEuclideanAt m i w) :
    evalModal m w (ModalFormula.know i (ModalFormula.know i phi)) =
      evalModal m w (ModalFormula.know i phi) := by
  have hConstK : ∀ u, u ∈ m.R i w →
      evalModal m u (ModalFormula.know i phi) =
        evalModal m w (ModalFormula.know i phi) := by
    intro u hu
    exact modal_knowledge_value_equal_at_successor_of_transitive_euclidean
      m i w u phi hTrans hEuclid hu
  exact modal_knowledge_recovers_nonempty_constant_profile
    m i w (ModalFormula.know i phi)
      (evalModal m w (ModalFormula.know i phi))
      (model_accessibility_nonempty m i w) hConstK

/-- The internally negated knowledge value is likewise recovered exactly under
transitivity plus Euclideanness. This is the full-value version of negative
introspection. -/
theorem modal_internal_negative_knowledge_value_idempotent_of_transitive_euclidean
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hEuclid : ModalEuclideanAt m i w) :
    evalModal m w
      (ModalFormula.know i (ModalFormula.not (ModalFormula.know i phi))) =
    evalModal m w (ModalFormula.not (ModalFormula.know i phi)) := by
  have hConstNotK : ∀ u, u ∈ m.R i w →
      evalModal m u (ModalFormula.not (ModalFormula.know i phi)) =
        evalModal m w (ModalFormula.not (ModalFormula.know i phi)) := by
    intro u hu
    change FDEValue.not (evalModal m u (ModalFormula.know i phi)) =
      FDEValue.not (evalModal m w (ModalFormula.know i phi))
    rw [modal_knowledge_value_equal_at_successor_of_transitive_euclidean
      m i w u phi hTrans hEuclid hu]
  exact modal_knowledge_recovers_nonempty_constant_profile
    m i w (ModalFormula.not (ModalFormula.know i phi))
      (evalModal m w (ModalFormula.not (ModalFormula.know i phi)))
      (model_accessibility_nonempty m i w) hConstNotK

/-- Positive internal negative introspection follows as a corollary: if
`not K phi` is positively supported, then it is positively known. -/
theorem modal_positive_internal_negative_introspection_of_transitive_euclidean
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hEuclid : ModalEuclideanAt m i w)
    (hNeg : (evalModal m w (ModalFormula.know i phi)).neg = true) :
    (evalModal m w
      (ModalFormula.know i (ModalFormula.not (ModalFormula.know i phi)))).pos = true := by
  have hEq :=
    modal_internal_negative_knowledge_value_idempotent_of_transitive_euclidean
      m i w phi hTrans hEuclid
  rw [hEq]
  change (evalModal m w (ModalFormula.know i phi)).neg = true
  exact hNeg

/-!
## Euclideanness alone does not suffice

The root sees `u` and `v`, both carrying `p = B`, so `K p = B` at the root.
Both source successors see `u` and `v`, hence the root is locally Euclidean.
But `v` additionally sees `extra`, where `p = T`. Therefore

  K p at u = B,
  K p at v = F.

Consequently `not K p` varies between `B` and `T` over the root successor set,
so the root does not positively know `not K p`.
-/

inductive NegativeIntroAtom where
  | p
deriving DecidableEq, Repr

inductive NegativeIntroAgent where
  | a
deriving DecidableEq, Repr

inductive NegativeIntroWorld where
  | root | u | v | extra
deriving DecidableEq, Repr

def negativeIntroR :
    NegativeIntroAgent → NegativeIntroWorld → FiniteSet NegativeIntroWorld
  | _, NegativeIntroWorld.root => [NegativeIntroWorld.u, NegativeIntroWorld.v]
  | _, NegativeIntroWorld.u => [NegativeIntroWorld.u, NegativeIntroWorld.v]
  | _, NegativeIntroWorld.v =>
      [NegativeIntroWorld.u, NegativeIntroWorld.v, NegativeIntroWorld.extra]
  | _, NegativeIntroWorld.extra => [NegativeIntroWorld.extra]

def negativeIntroVal : NegativeIntroWorld → NegativeIntroAtom → FDEValue
  | NegativeIntroWorld.root, _ => FDEValue.B
  | NegativeIntroWorld.u, _ => FDEValue.B
  | NegativeIntroWorld.v, _ => FDEValue.B
  | NegativeIntroWorld.extra, _ => FDEValue.T

def negativeIntroMu : NegativeIntroWorld → FiniteSet NegativeIntroWorld → Rat
  | NegativeIntroWorld.root, S =>
      let pu := if S.contains NegativeIntroWorld.u then (1 : Rat) / 2 else 0
      let pv := if S.contains NegativeIntroWorld.v then (1 : Rat) / 2 else 0
      pu + pv
  | NegativeIntroWorld.u, S =>
      let pu := if S.contains NegativeIntroWorld.u then (1 : Rat) / 2 else 0
      let pv := if S.contains NegativeIntroWorld.v then (1 : Rat) / 2 else 0
      pu + pv
  | NegativeIntroWorld.v, S =>
      let pu := if S.contains NegativeIntroWorld.u then (1 : Rat) / 3 else 0
      let pv := if S.contains NegativeIntroWorld.v then (1 : Rat) / 3 else 0
      let pe := if S.contains NegativeIntroWorld.extra then (1 : Rat) / 3 else 0
      pu + pv + pe
  | NegativeIntroWorld.extra, S =>
      if S.contains NegativeIntroWorld.extra then 1 else 0

def NegativeIntroModel :
    Model NegativeIntroWorld NegativeIntroAgent NegativeIntroAtom :=
  { worlds := [NegativeIntroWorld.root, NegativeIntroWorld.u,
      NegativeIntroWorld.v, NegativeIntroWorld.extra]
  , R := negativeIntroR
  , mu := fun _ w => negativeIntroMu w
  , val := negativeIntroVal
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

def negativeIntroP : ModalFormula NegativeIntroAtom NegativeIntroAgent :=
  ModalFormula.prop NegativeIntroAtom.p

/-- The root is locally Euclidean. -/
theorem negative_intro_root_is_euclidean :
    ModalEuclideanAt NegativeIntroModel NegativeIntroAgent.a
      NegativeIntroWorld.root := by
  intro u hu v hv
  cases u <;> cases v <;>
    simp [NegativeIntroModel, negativeIntroR] at hu hv ⊢

/-- Root knowledge is glutty. -/
theorem negative_intro_root_kp_is_glut :
    evalModal NegativeIntroModel NegativeIntroWorld.root
      (ModalFormula.know NegativeIntroAgent.a negativeIntroP) = FDEValue.B := by
  native_decide

/-- The first successor also has `K p = B`. -/
theorem negative_intro_u_kp_is_glut :
    evalModal NegativeIntroModel NegativeIntroWorld.u
      (ModalFormula.know NegativeIntroAgent.a negativeIntroP) = FDEValue.B := by
  native_decide

/-- The second successor has `K p = F` because its additional `T` successor
makes the `p` profile unstable. -/
theorem negative_intro_v_kp_is_false :
    evalModal NegativeIntroModel NegativeIntroWorld.v
      (ModalFormula.know NegativeIntroAgent.a negativeIntroP) = FDEValue.F := by
  native_decide

/-- Internal `not K p` is positively supported at the root. -/
theorem negative_intro_root_not_kp_is_glut :
    evalModal NegativeIntroModel NegativeIntroWorld.root
      (ModalFormula.not (ModalFormula.know NegativeIntroAgent.a negativeIntroP)) =
      FDEValue.B := by
  native_decide

/-- Nevertheless knowledge of internal `not K p` is strict `F`: the successor
values are `B` and `T`, hence unstable. -/
theorem negative_intro_root_knows_not_kp_is_false :
    evalModal NegativeIntroModel NegativeIntroWorld.root
      (ModalFormula.know NegativeIntroAgent.a
        (ModalFormula.not (ModalFormula.know NegativeIntroAgent.a negativeIntroP))) =
      FDEValue.F := by
  native_decide

/-- Hence local Euclideanness alone does not validate positive internal negative
introspection. -/
theorem modal_negative_introspection_fails_under_euclidean_alone :
    ModalEuclideanAt NegativeIntroModel NegativeIntroAgent.a
        NegativeIntroWorld.root ∧
    (evalModal NegativeIntroModel NegativeIntroWorld.root
      (ModalFormula.not (ModalFormula.know NegativeIntroAgent.a negativeIntroP))).pos = true ∧
    (evalModal NegativeIntroModel NegativeIntroWorld.root
      (ModalFormula.know NegativeIntroAgent.a
        (ModalFormula.not (ModalFormula.know NegativeIntroAgent.a negativeIntroP)))).pos = false := by
  constructor
  · exact negative_intro_root_is_euclidean
  constructor <;> native_decide

/-- The same witness fails transitivity exactly because `v` sees the extra world
while the root does not. -/
theorem negative_intro_root_not_transitive :
    ¬ ModalTransitiveAt NegativeIntroModel NegativeIntroAgent.a
      NegativeIntroWorld.root := by
  intro hTrans
  have hBad : NegativeIntroWorld.extra ∈
      NegativeIntroModel.R NegativeIntroAgent.a NegativeIntroWorld.root := by
    exact hTrans NegativeIntroWorld.v (by native_decide)
      NegativeIntroWorld.extra (by native_decide)
  simp [NegativeIntroModel, negativeIntroR] at hBad

/-!
## Interpretation

The modal boundary is now sharper than the classical slogan "Euclidean frames
validate axiom 5" suggests.

* Euclideanness alone lets successors inherit the source evidence region, but it
  does not exclude additional evidence. Those additions can make the complete
  `K phi` values differ across successors.
* Because outer evidence-stable knowledge requires full-value stability,
  positive internal negative introspection can therefore fail on a locally
  Euclidean frame.
* Transitivity removes the extra-successor escape route. Together with
  Euclideanness it makes successor neighborhoods extensionally coincide.
* In that combined phase, `K K phi = K phi` for all four values and
  `K (not K phi) = not K phi` exactly.

Thus the four-valued stability requirement strengthens the frame conditions
needed for the classical-looking negative-introspection law.
-/

end PEL4
