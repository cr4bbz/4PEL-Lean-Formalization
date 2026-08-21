import PEL4.ModalValidity

namespace PEL4

/-!
# First modal laws of evidence-stable knowledge

The Fitch development isolated several formula-level transport boundaries.  This
module begins a more systematic modal classification of the primitive
object-language knowledge operator.

The first questions are deliberately basic:

* does strict knowledge recover strict truth at reflexive points?
* does positive introspection `K+ phi -> K+ K phi` hold without frame
  assumptions?
* which transparent frame condition restores positive introspection?

Because evidence-stable knowledge depends on the complete accessible FDE
profile, classical frame slogans should not be imported silently.  We first use
a strong but explicit local cluster condition: every immediate successor sees
exactly the same successor list as the source point.
-/

/-- At a reflexive point, strict `T` knowledge is strictly factive. -/
theorem modal_strict_knowledge_factive_at_reflexive_point
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (href : w ∈ m.R i w)
    (hK : evalModal m w (ModalFormula.know i phi) = FDEValue.T) :
    evalModal m w phi = FDEValue.T := by
  have hKPos :
      (evalModal m w (ModalFormula.know i phi)).pos = true := by
    rw [hK]
    rfl
  have hKNeg :
      (evalModal m w (ModalFormula.know i phi)).neg = false := by
    rw [hK]
    rfl
  change ((m.R i w).all (fun w' => (evalModal m w' phi).pos) &&
      modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' phi)) = true at hKPos
  have hAllPos :
      (m.R i w).all (fun w' => (evalModal m w' phi).pos) = true := by
    cases ha : (m.R i w).all (fun w' => (evalModal m w' phi).pos) <;>
      cases hs : modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' phi) <;> simp_all
  change ((!modalAccessibleValueStable (m.R i w)
      (fun w' => evalModal m w' phi)) ||
      (m.R i w).any (fun w' => (evalModal m w' phi).neg)) = false at hKNeg
  have hAnyNeg :
      (m.R i w).any (fun w' => (evalModal m w' phi).neg) = false := by
    cases hs : modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' phi) <;>
      cases ha : (m.R i w).any (fun w' => (evalModal m w' phi).neg) <;>
      simp_all
  have hPosAt : (evalModal m w phi).pos = true := by
    simp only [List.all_eq_true] at hAllPos
    exact hAllPos w href
  have hNegAt : (evalModal m w phi).neg = false := by
    cases hn : (evalModal m w phi).neg with
    | false => rfl
    | true =>
        have hAnyTrue :
            (m.R i w).any (fun w' => (evalModal m w' phi).neg) = true := by
          simp only [List.any_eq_true]
          exact ⟨w, href, hn⟩
        rw [hAnyNeg] at hAnyTrue
        cases hAnyTrue
  cases hVal : evalModal m w phi with
  | mk pos neg =>
      cases pos <;> cases neg <;> simp_all [FDEValue.T]

/-- Local epistemic-cluster condition: every immediate successor has exactly the
same successor list as the source point. -/
def ModalConstantSuccessorNeighborhoodAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) : Prop :=
  ∀ u, u ∈ m.R i w → m.R i u = m.R i w

/-- Under a constant-successor epistemic cluster, positive knowledge is
positively introspective.  All immediate alternatives evaluate `K phi` exactly
as the source does, so the outer knowledge profile is homogeneous. -/
theorem modal_positive_introspection_of_constant_successor_neighborhood
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hCluster : ModalConstantSuccessorNeighborhoodAt m i w)
    (hK : (evalModal m w (ModalFormula.know i phi)).pos = true) :
    (evalModal m w
      (ModalFormula.know i (ModalFormula.know i phi))).pos = true := by
  have hEvalEq : ∀ u, u ∈ m.R i w →
      evalModal m u (ModalFormula.know i phi) =
        evalModal m w (ModalFormula.know i phi) := by
    intro u hu
    change modalKnowledgeValue m i u (fun x => evalModal m x phi) =
      modalKnowledgeValue m i w (fun x => evalModal m x phi)
    simp [modalKnowledgeValue, hCluster u hu]
  have hAll :
      (m.R i w).all
        (fun u => (evalModal m u (ModalFormula.know i phi)).pos) = true := by
    simp only [List.all_eq_true]
    intro u hu
    rw [hEvalEq u hu]
    exact hK
  have hStable :
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u (ModalFormula.know i phi)) = true := by
    cases hR : m.R i w with
    | nil =>
        rfl
    | cons first rest =>
        unfold modalAccessibleValueStable
        simp only [List.all_eq_true]
        intro u hu
        have hFirst : first ∈ m.R i w := by
          simp [hR]
        have hU : u ∈ m.R i w := by
          simp [hR, hu]
        simp [hEvalEq u hU, hEvalEq first hFirst]
  change ((m.R i w).all
      (fun u => (evalModal m u (ModalFormula.know i phi)).pos) &&
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u (ModalFormula.know i phi))) = true
  simp [hAll, hStable]

/-!
## Unrestricted positive introspection fails

The source sees a single middle world where `p = T`, hence `K p = T` at the
source.  The middle world itself sees two successors carrying `T` and `B`.
Their full values are heterogeneous, so `K p = F` at the middle world.  The
source therefore has `K p = T` but `K K p = F`.
-/

inductive IntrospectionAtom where
  | p
deriving DecidableEq, Repr

inductive IntrospectionAgent where
  | a
deriving DecidableEq, Repr

inductive IntrospectionWorld where
  | root | middle | left | right
deriving DecidableEq, Repr

def introspectionR :
    IntrospectionAgent → IntrospectionWorld → FiniteSet IntrospectionWorld
  | _, IntrospectionWorld.root => [IntrospectionWorld.middle]
  | _, IntrospectionWorld.middle =>
      [IntrospectionWorld.left, IntrospectionWorld.right]
  | _, IntrospectionWorld.left => [IntrospectionWorld.left]
  | _, IntrospectionWorld.right => [IntrospectionWorld.right]

def introspectionVal : IntrospectionWorld → IntrospectionAtom → FDEValue
  | IntrospectionWorld.root, _ => FDEValue.T
  | IntrospectionWorld.middle, _ => FDEValue.T
  | IntrospectionWorld.left, _ => FDEValue.T
  | IntrospectionWorld.right, _ => FDEValue.B

def introspectionMu : IntrospectionWorld → FiniteSet IntrospectionWorld → Rat
  | IntrospectionWorld.root, S =>
      if S.contains IntrospectionWorld.middle then 1 else 0
  | IntrospectionWorld.middle, S =>
      let pl := if S.contains IntrospectionWorld.left then (1 : Rat) / 2 else 0
      let pr := if S.contains IntrospectionWorld.right then (1 : Rat) / 2 else 0
      pl + pr
  | IntrospectionWorld.left, S =>
      if S.contains IntrospectionWorld.left then 1 else 0
  | IntrospectionWorld.right, S =>
      if S.contains IntrospectionWorld.right then 1 else 0

def IntrospectionModel :
    Model IntrospectionWorld IntrospectionAgent IntrospectionAtom :=
  { worlds := [IntrospectionWorld.root, IntrospectionWorld.middle,
      IntrospectionWorld.left, IntrospectionWorld.right]
  , R := introspectionR
  , mu := fun _ w => introspectionMu w
  , val := introspectionVal
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

def introspectionP : ModalFormula IntrospectionAtom IntrospectionAgent :=
  ModalFormula.prop IntrospectionAtom.p

/-- The source strictly knows `p`. -/
theorem introspection_root_knows_p_true :
    evalModal IntrospectionModel IntrospectionWorld.root
      (ModalFormula.know IntrospectionAgent.a introspectionP) = FDEValue.T := by
  native_decide

/-- At the middle successor, heterogeneous `T/B` evidence makes `K p = F`. -/
theorem introspection_middle_knows_p_false :
    evalModal IntrospectionModel IntrospectionWorld.middle
      (ModalFormula.know IntrospectionAgent.a introspectionP) = FDEValue.F := by
  native_decide

/-- Consequently positive axiom 4 fails without an additional frame condition:
`K+ p` at the source does not imply `K+ K p`. -/
theorem modal_positive_introspection_fails_without_frame_condition :
    (evalModal IntrospectionModel IntrospectionWorld.root
      (ModalFormula.know IntrospectionAgent.a introspectionP)).pos = true ∧
    (evalModal IntrospectionModel IntrospectionWorld.root
      (ModalFormula.know IntrospectionAgent.a
        (ModalFormula.know IntrospectionAgent.a introspectionP))).pos = false := by
  native_decide

/-!
## Interpretation

Evidence-stable knowledge already exhibits a recognizable but nonclassical modal
profile:

* reflexivity recovers strict factivity for strict knowledge;
* unrestricted positive introspection fails;
* a local cluster condition with identical successor neighborhoods restores
  positive introspection.

The next modal-law gate should ask whether ordinary transitivity is already
sufficient for positive introspection, whether Euclidean/symmetric conditions
control negative introspection, and how strict conjunction decomposition behaves
independently of frame structure.
-/

end PEL4
