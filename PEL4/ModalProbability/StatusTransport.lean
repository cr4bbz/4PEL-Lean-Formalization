import PEL4.ModalProbability.Refinement
import PEL4.PopulationAxiology.FiniteFineGrainedness

namespace PEL4.ModalProbability

/-!
# MPFG-1: modal status and projection loss

The predicates here are meta-level predicates of status, not new FDE-valued
connectives. `EssentialAt` is conditional and can hold vacuously when the
current status differs from the queried status. It is NOT the existing K.
No S5 frame assumptions are needed for transport through a projection.
-/

def NecessaryAt {W S : Type} (R : W → W → Prop) (v : W → S)
    (s : S) (w : W) : Prop := ∀ u, R w u → v u = s

def EssentialAt {W S : Type} (R : W → W → Prop) (v : W → S)
    (s : S) (w : W) : Prop := v w = s → NecessaryAt R v s w

def AccidentalAt {W S : Type} (R : W → W → Prop) (v : W → S)
    (s : S) (w : W) : Prop := v w = s ∧ ∃ u, R w u ∧ v u ≠ s

/-- Local status preservation from the current world, distinct from
homogeneity of a possibly nonreflexive accessible range. -/
def StableAt {W S : Type} (R : W → W → Prop) (v : W → S)
    (w : W) : Prop := NecessaryAt R v (v w) w

theorem accidental_iff_not_essential {W S : Type}
    (R : W → W → Prop) (v : W → S) (s : S) (w : W) :
    AccidentalAt R v s w ↔ ¬ EssentialAt R v s w := by
  classical
  simp only [AccidentalAt, EssentialAt, NecessaryAt, not_imp, not_forall]

theorem stable_iff_essential_current {W S : Type}
    (R : W → W → Prop) (v : W → S) (w : W) :
    StableAt R v w ↔ EssentialAt R v (v w) w := by
  constructor
  · intro h _; exact h
  · intro h; exact h rfl

theorem necessary_projects {W S C : Type}
    (R : W → W → Prop) (v : W → S) (forget : S → C)
    (s : S) (w : W) (h : NecessaryAt R v s w) :
    NecessaryAt R (fun u => forget (v u)) (forget s) w := by
  intro u hu
  exact congrArg forget (h u hu)

theorem stable_projects {W S C : Type}
    (R : W → W → Prop) (v : W → S) (forget : S → C)
    (w : W) (h : StableAt R v w) :
    StableAt R (fun u => forget (v u)) w :=
  necessary_projects R v forget (v w) w h

/-- Exact local criterion: coarse stability lifts iff the current coarse
fibre has no accessible fine variation. No global injectivity is assumed. -/
def FibreRigidAt {W S C : Type}
    (R : W → W → Prop) (v : W → S) (forget : S → C) (w : W) : Prop :=
  ∀ u, R w u → forget (v u) = forget (v w) → v u = v w

theorem stable_iff_coarse_and_fibre_rigid {W S C : Type}
    (R : W → W → Prop) (v : W → S) (forget : S → C) (w : W) :
    StableAt R v w ↔
      StableAt R (fun u => forget (v u)) w ∧ FibreRigidAt R v forget w := by
  constructor
  · intro h
    exact ⟨stable_projects R v forget w h, fun u hu _ => h u hu⟩
  · rintro ⟨hc, hf⟩ u hu
    exact hf u hu (hc u hu)

/-- A coarse change always witnesses a fine change, but not conversely. -/
theorem coarse_accident_lifts {W S C : Type}
    (R : W → W → Prop) (v : W → S) (forget : S → C) (w : W)
    (h : AccidentalAt R (fun u => forget (v u)) (forget (v w)) w) :
    AccidentalAt R v (v w) w := by
  rcases h with ⟨_, u, hu, hneq⟩
  exact ⟨rfl, u, hu, fun heq => hneq (congrArg forget heq)⟩

/-- For an existing four-cell evidence path, coarse projection changes none
of its raw threshold-status modalities. -/
theorem threshold_modalities_commute {W : Type} (R : W → W → Prop)
    (p : W → SixCellProbability) (c : Rat) (s : FDEValue) (w : W) :
    (EssentialAt R (fun u => (p u).thresholdValue c) s w ↔
      EssentialAt R (fun u => (p u).coarse.thresholdValue c) s w) ∧
    (AccidentalAt R (fun u => (p u).thresholdValue c) s w ↔
      AccidentalAt R (fun u => (p u).coarse.thresholdValue c) s w) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Direct bridge to the existing executable stability test used by K.
Reliability refinement is invisible when K is applied to raw belief status. -/
theorem existing_K_stability_commutes {W : Type} [DecidableEq W]
    (worlds : FiniteSet W) (p : W → SixCellProbability) (c : Rat) :
    modalAccessibleValueStable worlds (fun u => (p u).thresholdValue c) =
      modalAccessibleValueStable worlds (fun u => (p u).coarse.thresholdValue c) := rfl

theorem existing_K_value_commutes {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (p : W → SixCellProbability) (c : Rat) :
    modalKnowledgeValue m i w (fun u => (p u).thresholdValue c) =
      modalKnowledgeValue m i w (fun u => (p u).coarse.thresholdValue c) := rfl

/-- The old finite-chain machinery transports a status only if each edge
preserves that status. Graph connectivity alone is not such an invariant. -/
theorem finite_chain_preserves_threshold {W : Type}
    (step : W → W → Prop) (p : W → SixCellProbability) (c : Rat)
    (hStep : ∀ {x y}, step x y →
      (p x).coarse.thresholdValue c = (p y).coarse.thresholdValue c)
    {x y : W} (hxy : PopulationAxiology.FiniteStepChain step x y) :
    (p x).thresholdValue c = (p y).thresholdValue c :=
  hxy.preserves (fun w => (p w).coarse.thresholdValue c) hStep

/-! ## Finite witnesses on an S5 frame (the universal relation on Bool) -/

def everywhere (_ _ : Bool) : Prop := True

theorem everywhere_s5 :
    (∀ w, everywhere w w) ∧
    (∀ x y z, everywhere x y → everywhere y z → everywhere x z) ∧
    (∀ x y z, everywhere x y → everywhere x z → everywhere y z) :=
  ⟨fun _ => True.intro, fun _ _ _ _ _ => True.intro,
    fun _ _ _ _ _ => True.intro⟩

def reliabilityWorld : Bool → EvidenceCell
  | false => .t
  | true => .reliableT

theorem coarse_stable_fine_accidental :
    StableAt everywhere (fun w => (reliabilityWorld w).raw) false ∧
    AccidentalAt everywhere reliabilityWorld .t false := by
  constructor
  · intro u _; cases u <;> rfl
  · exact ⟨rfl, true, True.intro, by decide⟩

def reliabilityProfile : Bool → SixCellProbability
  | false => .pureT
  | true => .pureReliableT

theorem probability_profile_projection_hides_instability :
    StableAt everywhere (fun w => (reliabilityProfile w).coarse) false ∧
    ¬ StableAt everywhere reliabilityProfile false := by
  constructor
  · intro u _; cases u <;> rfl
  · intro h
    have heq := congrArg SixCellProbability.reliableMass (h true True.intro)
    exact (by decide : (1 : Rat) ≠ 0) heq

/-- Even raw threshold-status stability need not mean mass-profile stability:
both worlds are B at cutoff 3/5, while their glut masses differ. -/
def dilutedB : FourCellProbability :=
  { t := 0, b := 3 / 4, n := 1 / 4, f := 0
    t_nonnegative := by decide
    b_nonnegative := by decide
    n_nonnegative := by decide
    f_nonnegative := by decide
    normalized := by decide }

def glutProfile : Bool → FourCellProbability
  | false => .pureB
  | true => dilutedB

theorem stable_B_does_not_mean_constant_mass :
    StableAt everywhere (fun w => (glutProfile w).thresholdValue (3 / 5)) false ∧
    (glutProfile false).thresholdValue (3 / 5) = FDEValue.B ∧
    ¬ StableAt everywhere glutProfile false := by
  refine ⟨?_, by decide, ?_⟩
  · intro u _; cases u <;> decide
  · intro h
    have heq := congrArg FourCellProbability.b (h true True.intro)
    exact (by decide : (3 / 4 : Rat) ≠ 1) heq

/-- B remains a status, not a proof of Lean False; an unrelated profile is N. -/
theorem refinement_retains_B_and_N :
    (SixCellProbability.untagged FourCellProbability.pureB).thresholdValue 1 = .B ∧
    (SixCellProbability.untagged FourCellProbability.pureN).thresholdValue 1 = .N := by
  constructor <;> decide

end PEL4.ModalProbability
