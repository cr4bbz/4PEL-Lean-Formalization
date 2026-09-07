import PEL4.TopologicalEvidenceNerveRealization

namespace PEL4

/-!
# Gate 12: phase nerves under persistent evidence

Persistence means that neither evidence bit is lost along accessibility.
Unlike a truth order, this is the information order N <= T,F <= B.
It constrains the *chosen profile*, not automatically every formula of 4PEL.
On symmetric frames persistence collapses each component to a constant profile.
On S4 frames it forces N at any common T/F contact, but does not bound nerve
dimension below three: an antisymmetric persistent star realizes the tetrahedron.
-/

/-- Information growth: both positive and negative evidence are preserved. -/
def FDEInformationLE (a b : FDEValue) : Prop :=
  (a.pos = true → b.pos = true) ∧ (a.neg = true → b.neg = true)

theorem fde_information_le_refl (a : FDEValue) : FDEInformationLE a a :=
  ⟨fun h => h, fun h => h⟩

theorem fde_information_le_trans {a b c : FDEValue}
    (hab : FDEInformationLE a b) (hbc : FDEInformationLE b c) :
    FDEInformationLE a c :=
  ⟨fun h => hbc.1 (hab.1 h), fun h => hbc.2 (hab.2 h)⟩

theorem fde_information_le_antisymm {a b : FDEValue}
    (hab : FDEInformationLE a b) (hba : FDEInformationLE b a) : a = b := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;>
    simp_all [FDEInformationLE]

/-- The only common information lower bound of T and F is N. -/
theorem fde_information_below_T_F_iff (a : FDEValue) :
    (FDEInformationLE a FDEValue.T ∧ FDEInformationLE a FDEValue.F) ↔
      a = FDEValue.N := by
  rcases a with ⟨ap, an⟩
  cases ap <;> cases an <;>
    simp [FDEInformationLE, FDEValue.T, FDEValue.F, FDEValue.N]

def PersistentFDEProfile {W : Type} (R : W → FiniteSet W)
    (value : W → FDEValue) : Prop :=
  ∀ w u, u ∈ R w → FDEInformationLE (value w) (value u)

def SuccessorSymmetric {W : Type} (R : W → FiniteSet W) : Prop :=
  ∀ w u, u ∈ R w → w ∈ R u

theorem persistent_reachable_above {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value) (w : W) (q : FDEValue)
    (h : ReachableFDEPhase R value w q) : FDEInformationLE (value w) q := by
  rcases h with ⟨u, hu, hv⟩
  rw [← hv]
  exact hP w u hu

/-- Mutual accessibility turns two one-way information inequalities into equality. -/
theorem persistent_symmetric_edge_constant {W : Type}
    (R : W → FiniteSet W) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value) (hSym : SuccessorSymmetric R)
    (w u : W) (hu : u ∈ R w) : value u = value w := by
  exact fde_information_le_antisymm (hP u w (hSym w u hu)) (hP w u hu)

theorem persistent_symmetric_reachable_iff {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (value : W → FDEValue) (hP : PersistentFDEProfile R value)
    (hSym : SuccessorSymmetric R) (w : W) (q : FDEValue) :
    ReachableFDEPhase R value w q ↔ value w = q := by
  constructor
  · rintro ⟨u, hu, hv⟩
    exact (persistent_symmetric_edge_constant R value hP hSym w u hu).symm.trans hv
  · intro h
    exact ⟨w, hRefl w, h⟩

/-- Persistent S5 profiles are locally constant everywhere. -/
theorem persistent_s5_locally_constant {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (hSym : SuccessorSymmetric R)
    (value : W → FDEValue) (hP : PersistentFDEProfile R value) (w : W) :
    TopologicallyLocallyConstantAt
      (successorInteriorSemantics R hRefl hTrans) value w := by
  change ∀ u, u ∈ R w → value u = value w
  exact fun u hu => persistent_symmetric_edge_constant R value hP hSym w u hu

/-- Exact S5 classification: only subsets of a realized singleton can be faces. -/
theorem persistent_s5_simplex_iff {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (hSym : SuccessorSymmetric R)
    (value : W → FDEValue) (hP : PersistentFDEProfile R value)
    (phases : FDEValue → Prop) :
    FDEPhaseSimplex (successorInteriorSemantics R hRefl hTrans) value phases ↔
      ∃ w, ∀ q, phases q → value w = q := by
  rw [alexandrov_phase_simplex_iff R hRefl hTrans]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, fun q hq =>
      (persistent_symmetric_reachable_iff R hRefl value hP hSym w q).1 (hw q hq)⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, fun q hq =>
      (persistent_symmetric_reachable_iff R hRefl value hP hSym w q).2 (hw q hq)⟩

theorem persistent_s5_no_phase_edges {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (hSym : SuccessorSymmetric R)
    (value : W → FDEValue) (hP : PersistentFDEProfile R value) (q r : FDEValue) :
    ¬ FDEPhaseAdjacent (successorInteriorSemantics R hRefl hTrans) value q r := by
  rw [alexandrov_phase_adjacent_iff R hRefl hTrans]
  rintro ⟨hqr, w, hq, hr⟩
  have eqQ := (persistent_symmetric_reachable_iff R hRefl value hP hSym w q).1 hq
  have eqR := (persistent_symmetric_reachable_iff R hRefl value hP hSym w r).1 hr
  exact hqr (eqQ.symm.trans eqR)

/-- At a common T/F closure witness, persistent evidence must start at N. -/
theorem persistent_T_F_contact_is_N {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value) (w : W)
    (h : FDEPhaseContactAt (successorInteriorSemantics R hRefl hTrans)
      value FDEValue.T FDEValue.F w) : value w = FDEValue.N := by
  apply (fde_information_below_T_F_iff (value w)).1
  exact ⟨persistent_reachable_above R value hP w FDEValue.T
      ((alexandrov_phase_closure_iff_reachable_phase R hRefl hTrans value w _).1 h.1),
    persistent_reachable_above R value hP w FDEValue.F
      ((alexandrov_phase_closure_iff_reachable_phase R hRefl hTrans value w _).1 h.2)⟩

/-- Any simplex containing both T and F must admit adjoining N at the same witness. -/
theorem persistent_simplex_T_F_adjoin_N {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value) (phases : FDEValue → Prop)
    (hT : phases FDEValue.T) (hF : phases FDEValue.F)
    (h : FDEPhaseSimplex (successorInteriorSemantics R hRefl hTrans) value phases) :
    FDEPhaseSimplex (successorInteriorSemantics R hRefl hTrans)
      value (fun q => phases q ∨ q = FDEValue.N) := by
  rcases h with ⟨w, hw⟩
  have hN := persistent_T_F_contact_is_N R hRefl hTrans value hP w
    ⟨hw _ hT, hw _ hF⟩
  refine ⟨w, ?_⟩
  intro q hq
  rcases hq with hq | rfl
  · exact hw q hq
  · exact closure_superset _ (fdeValueRegion value FDEValue.N) w hN

theorem persistent_T_F_edge_forces_N_triangle {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value)
    (h : FDEPhaseAdjacent (successorInteriorSemantics R hRefl hTrans)
      value FDEValue.T FDEValue.F) :
    FDEPhaseTriangle (successorInteriorSemantics R hRefl hTrans)
      value FDEValue.N FDEValue.T FDEValue.F := by
  rcases h with ⟨_, w, hT, hF⟩
  have hN := persistent_T_F_contact_is_N R hRefl hTrans value hP w ⟨hT, hF⟩
  exact ⟨by decide, by decide, by decide, w,
    closure_superset _ (fdeValueRegion value FDEValue.N) w hN, hT, hF⟩

theorem persistent_T_F_B_triangle_forces_tetrahedron {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R) (value : W → FDEValue)
    (hP : PersistentFDEProfile R value)
    (h : FDEPhaseTriangle (successorInteriorSemantics R hRefl hTrans)
      value FDEValue.T FDEValue.F FDEValue.B) :
    FDEPhaseTetrahedron (successorInteriorSemantics R hRefl hTrans) value := by
  rcases h with ⟨_, _, _, w, hT, hF, hB⟩
  have hN := persistent_T_F_contact_is_N R hRefl hTrans value hP w ⟨hT, hF⟩
  exact ⟨w, hT, hF, hB, closure_superset _ (fdeValueRegion value FDEValue.N) w hN⟩

/-- A four-world star: N sees every world; other worlds see only themselves. -/
def persistentStarR (w : FDEValue) : FiniteSet FDEValue :=
  if w = FDEValue.N then phaseLabels else [w]

theorem persistentStar_reflexive : SuccessorReflexive persistentStarR := by
  intro w
  by_cases h : w = FDEValue.N
  · simp [persistentStarR, h, mem_phaseLabels]
  · simp [persistentStarR, h]

theorem persistentStar_transitive : SuccessorTransitive persistentStarR := by
  intro w u hu v hv
  by_cases h : w = FDEValue.N
  · simp [persistentStarR, h, mem_phaseLabels]
  · have huw : u = w := by simpa [persistentStarR, h] using hu
    subst u
    have hvw : v = w := by simpa [persistentStarR, h] using hv
    simpa [persistentStarR, h] using hvw

theorem persistentStar_antisymmetric (w u : FDEValue)
    (hu : u ∈ persistentStarR w) (hw : w ∈ persistentStarR u) : w = u := by
  by_cases h : w = FDEValue.N
  · by_cases h' : u = FDEValue.N
    · exact h.trans h'.symm
    · simpa [persistentStarR, h'] using hw
  · exact (show u = w from by simpa [persistentStarR, h] using hu).symm

theorem persistentStar_profile : PersistentFDEProfile persistentStarR id := by
  intro w u hu
  by_cases h : w = FDEValue.N
  · simp [h, FDEInformationLE, FDEValue.N]
  · have huw : u = w := by simpa [persistentStarR, h] using hu
    subst u
    exact fde_information_le_refl w

/-- Persistence does not lower the maximal S4 nerve dimension: the full
tetrahedron is realized even on an antisymmetric four-world frame. -/
theorem persistent_s4_full_tetrahedron :
    FDEPhaseTetrahedron
      (successorInteriorSemantics persistentStarR persistentStar_reflexive
        persistentStar_transitive) id := by
  rw [alexandrov_phase_tetrahedron_iff]
  refine ⟨FDEValue.N, ?_, ?_, ?_, ?_⟩
  all_goals
    refine ⟨_, ?_, rfl⟩
    simp [persistentStarR, mem_phaseLabels]

#print axioms persistent_s5_simplex_iff
#print axioms persistent_simplex_T_F_adjoin_N
#print axioms persistent_s4_full_tetrahedron

end PEL4
