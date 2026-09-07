import PEL4.TopologicalEvidenceAlexandrovNerve

namespace PEL4

/-!
# Gate 11b: universal finite realization of phase nerves

A downward-closed family of subsets of the four FDE values with at least one
vertex is realized exactly by a finite equivalence frame. Worlds are incidences
(allowed face, phase in that face); accessibility means having the same face.
The proof includes the empty face and absent vertices. No monotonicity condition
on valuations, probability model, or homotopy-equivalence claim is imposed.
-/

/-- A finite encoding of a subset of the four phase labels. -/
structure PhaseMask where
  t : Bool
  f : Bool
  b : Bool
  n : Bool
  deriving DecidableEq

def PhaseMask.region (m : PhaseMask) (q : FDEValue) : Prop :=
  (if q = FDEValue.T then m.t else
   if q = FDEValue.F then m.f else
   if q = FDEValue.B then m.b else m.n) = true

def phaseLabels : List FDEValue :=
  [FDEValue.T, FDEValue.F, FDEValue.B, FDEValue.N]

theorem mem_phaseLabels (q : FDEValue) : q ∈ phaseLabels := by
  rcases fde_value_four_cases q with rfl | rfl | rfl | rfl <;> simp [phaseLabels]

def phaseMasks : List PhaseMask :=
  [false, true].flatMap fun t =>
  [false, true].flatMap fun f =>
  [false, true].flatMap fun b =>
  [false, true].map fun n => ⟨t, f, b, n⟩

theorem mem_phaseMasks (m : PhaseMask) : m ∈ phaseMasks := by
  rcases m with ⟨t, f, b, n⟩
  cases t <;> cases f <;> cases b <;> cases n <;> decide

/-- Every proposition-valued phase family has a Boolean mask (classically). -/
noncomputable def phaseMaskOf (phases : FDEValue → Prop) : PhaseMask := by
  classical
  exact ⟨decide (phases FDEValue.T), decide (phases FDEValue.F),
    decide (phases FDEValue.B), decide (phases FDEValue.N)⟩

theorem phaseMaskOf_region (phases : FDEValue → Prop) :
    (phaseMaskOf phases).region = phases := by
  classical
  funext q
  apply propext
  rcases fde_value_four_cases q with rfl | rfl | rfl | rfl <;>
    simp [phaseMaskOf, PhaseMask.region, FDEValue.T, FDEValue.F,
      FDEValue.B, FDEValue.N]

/-- An abstract complex on the fixed ambient set of four phase labels.
Ghost vertices are allowed. Existence of a vertex is a separate hypothesis. -/
structure FDEPhaseComplex where
  face : (FDEValue → Prop) → Prop
  downward : ∀ {small large}, (∀ q, small q → large q) → face large → face small

def FDEPhaseComplex.HasVertex (K : FDEPhaseComplex) : Prop :=
  ∃ phases, K.face phases ∧ ∃ q, phases q

def phaseCandidates : List (PhaseMask × FDEValue) :=
  phaseMasks.flatMap fun m => phaseLabels.map fun q => (m, q)

theorem mem_phaseCandidates (c : PhaseMask × FDEValue) : c ∈ phaseCandidates := by
  exact List.mem_flatMap.mpr ⟨c.1, mem_phaseMasks c.1,
    List.mem_map.mpr ⟨c.2, mem_phaseLabels c.2, rfl⟩⟩

noncomputable def allowedPhaseCandidates (K : FDEPhaseComplex) :
    List (PhaseMask × FDEValue) := by
  classical
  exact phaseCandidates.filter fun c => decide (K.face c.1.region ∧ c.1.region c.2)

theorem mem_allowedPhaseCandidates (K : FDEPhaseComplex) (c : PhaseMask × FDEValue) :
    c ∈ allowedPhaseCandidates K ↔ K.face c.1.region ∧ c.1.region c.2 := by
  classical
  simp [allowedPhaseCandidates, mem_phaseCandidates]

/-- Worlds are the allowed face/vertex incidences; there are at most 64 candidates. -/
abbrev PhaseRealizationWorld (K : FDEPhaseComplex) :=
  {c : PhaseMask × FDEValue // c ∈ allowedPhaseCandidates K}

noncomputable def phaseRealizationWorlds (K : FDEPhaseComplex) :
    List (PhaseRealizationWorld K) := (allowedPhaseCandidates K).attach

theorem phaseRealizationWorlds_complete (K : FDEPhaseComplex)
    (w : PhaseRealizationWorld K) : w ∈ phaseRealizationWorlds K := by
  exact List.mem_attach _ _

theorem phaseRealizationWorlds_length_le (K : FDEPhaseComplex) :
    (phaseRealizationWorlds K).length ≤ 64 := by
  change ((allowedPhaseCandidates K).attach).length ≤ 64
  rw [List.length_attach]
  exact Nat.le_trans (List.length_filter_le _ _) (by decide : phaseCandidates.length ≤ 64)

noncomputable def phaseRealizationR (K : FDEPhaseComplex)
    (w : PhaseRealizationWorld K) : FiniteSet (PhaseRealizationWorld K) := by
  classical
  exact (phaseRealizationWorlds K).filter fun u => decide (u.val.1 = w.val.1)

def phaseRealizationValue (K : FDEPhaseComplex)
    (w : PhaseRealizationWorld K) : FDEValue := w.val.2

theorem mem_phaseRealizationR (K : FDEPhaseComplex)
    (w u : PhaseRealizationWorld K) :
    u ∈ phaseRealizationR K w ↔ u.val.1 = w.val.1 := by
  classical
  simp [phaseRealizationR, phaseRealizationWorlds_complete]

theorem phaseRealization_reflexive (K : FDEPhaseComplex) :
    SuccessorReflexive (phaseRealizationR K) := by
  intro w
  exact (mem_phaseRealizationR K w w).2 rfl

theorem phaseRealization_transitive (K : FDEPhaseComplex) :
    SuccessorTransitive (phaseRealizationR K) := by
  intro w u hu v hv
  exact (mem_phaseRealizationR K w v).2
    (((mem_phaseRealizationR K u v).1 hv).trans ((mem_phaseRealizationR K w u).1 hu))

/-- The construction actually gives an equivalence frame (hence an S5 frame). -/
theorem phaseRealization_symmetric (K : FDEPhaseComplex)
    (w u : PhaseRealizationWorld K) (hu : u ∈ phaseRealizationR K w) :
    w ∈ phaseRealizationR K u := by
  exact (mem_phaseRealizationR K u w).2 ((mem_phaseRealizationR K w u).1 hu).symm

def phaseRealizationSemantics (K : FDEPhaseComplex) :
    InteriorSemantics (PhaseRealizationWorld K) :=
  successorInteriorSemantics (phaseRealizationR K)
    (phaseRealization_reflexive K) (phaseRealization_transitive K)

/-- A world's reachable phase profile is exactly its face label. -/
theorem phaseRealization_reachable_iff (K : FDEPhaseComplex)
    (w : PhaseRealizationWorld K) (q : FDEValue) :
    ReachableFDEPhase (phaseRealizationR K) (phaseRealizationValue K) w q ↔
      w.val.1.region q := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hFace := (mem_phaseRealizationR K w u).1 hu
    have hValid := (mem_allowedPhaseCandidates K u.val).1 u.property
    change u.val.2 = q at hv
    rw [hFace, hv] at hValid
    exact hValid.2
  · intro hq
    have hK := ((mem_allowedPhaseCandidates K w.val).1 w.property).1
    let u : PhaseRealizationWorld K :=
      ⟨(w.val.1, q), (mem_allowedPhaseCandidates K (w.val.1, q)).2 ⟨hK, hq⟩⟩
    exact ⟨u, (mem_phaseRealizationR K w u).2 rfl, rfl⟩

theorem phaseRealization_has_world (K : FDEPhaseComplex) (h : K.HasVertex) :
    Nonempty (PhaseRealizationWorld K) := by
  rcases h with ⟨phases, hK, q, hq⟩
  have hMask := phaseMaskOf_region phases
  refine ⟨⟨(phaseMaskOf phases, q), ?_⟩⟩
  apply (mem_allowedPhaseCandidates K _).2
  change K.face (phaseMaskOf phases).region ∧ (phaseMaskOf phases).region q
  rw [hMask]
  exact ⟨hK, hq⟩

/-- Universal realization, including the empty face and any absent phase labels.
This is equality of nerves, not merely containment or graph equivalence. -/
theorem every_phase_complex_realized (K : FDEPhaseComplex) (hVertex : K.HasVertex)
    (phases : FDEValue → Prop) :
    FDEPhaseSimplex (phaseRealizationSemantics K) (phaseRealizationValue K) phases ↔
      K.face phases := by
  classical
  rw [alexandrov_phase_simplex_iff (phaseRealizationR K)
    (phaseRealization_reflexive K) (phaseRealization_transitive K)]
  constructor
  · rintro ⟨w, hw⟩
    exact K.downward
      (fun q hq => (phaseRealization_reachable_iff K w q).1 (hw q hq))
      (((mem_allowedPhaseCandidates K w.val).1 w.property).1)
  · intro hK
    by_cases hNonempty : ∃ q, phases q
    · rcases hNonempty with ⟨q, hq⟩
      have hMask := phaseMaskOf_region phases
      have hValid : K.face (phaseMaskOf phases).region ∧
          (phaseMaskOf phases).region q := by
        rw [hMask]
        exact ⟨hK, hq⟩
      let w : PhaseRealizationWorld K :=
        ⟨(phaseMaskOf phases, q), (mem_allowedPhaseCandidates K _).2 hValid⟩
      refine ⟨w, ?_⟩
      intro r hr
      apply (phaseRealization_reachable_iff K w r).2
      change (phaseMaskOf phases).region r
      rw [hMask]
      exact hr
    · rcases phaseRealization_has_world K hVertex with ⟨w⟩
      exact ⟨w, fun q hq => False.elim (hNonempty ⟨q, hq⟩)⟩

/-- The empty-face-only complex cannot be realized on a nonempty space under
the witness-based nerve convention; a world always witnesses its own vertex. -/
theorem phase_nerve_has_vertex_at_world {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue) (w : W) :
    FDEPhaseSimplex s value (fun q => q = value w) := by
  refine ⟨w, ?_⟩
  intro q hq
  subst q
  exact closure_superset s (fdeValueRegion value (value w)) w rfl

#print axioms every_phase_complex_realized
#print axioms phaseRealizationWorlds_length_le
#print axioms phaseRealization_symmetric

end PEL4
