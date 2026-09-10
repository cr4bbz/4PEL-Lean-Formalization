import PEL4.FiniteUpdateScopeBounds

namespace PEL4

/-!
# Gate 21: finite recovery-observation maps and stuttering

Gate 20 bounded strict evidence-scope shrinkage at one fixed agent/world site.
To prepare a bound for recovery changes, this gate compiles the finitely many
semantic observations that the recursive recovery certificate for a fixed
formula and finite root list actually inspects.

The compiler is deliberately exact rather than merely over-approximating:
atomic nodes and belief results contribute a classicality observation;
negation and conjunction recurse structurally; and modal operators recurse
over their finite accessibility lists.  Knowledge and possibility roots need
no extra observation because their recovery clauses require only recovery of
their accessible profiles.
-/

/-- A world/formula pair whose semantic classicality is inspected by the
recursive recovery certificate. -/
structure RecoveryObservationSite (W Ag Atom : Type) where
  world : W
  formula : ModalFormula Atom Ag

namespace RecoveryObservationSite

/-- The observation made at a compiled site in a particular model. -/
def IsClassicalIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (site : RecoveryObservationSite W Ag Atom) : Prop :=
  IsClassicalValue (evalModal m site.world site.formula)

/-- The non-atomic observations emitted by the compiler are precisely belief
results. -/
def IsBeliefObservation
    {W Ag Atom : Type}
    (site : RecoveryObservationSite W Ag Atom) : Prop :=
  ∃ i body, site.formula = ModalFormula.bel i body

end RecoveryObservationSite

/-- Compile the exact finite list of classicality observations needed for
`CompositionallyClassicalAt m w phi`.

Duplicates are retained intentionally: the output records the recursive
evaluation tree, not a quotient by syntactic or semantic equality. -/
def recoveryObservationSites
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) :
    W -> ModalFormula Atom Ag ->
      FiniteSet (RecoveryObservationSite W Ag Atom)
  | w, phi@(.prop _) => [{ world := w, formula := phi }]
  | w, .not phi => recoveryObservationSites m w phi
  | w, .and phi psi =>
      recoveryObservationSites m w phi ++
        recoveryObservationSites m w psi
  | w, phi@(.bel i body) =>
      { world := w, formula := phi } ::
        (m.R i w).flatMap (fun u => recoveryObservationSites m u body)
  | w, .know i body =>
      (m.R i w).flatMap (fun u => recoveryObservationSites m u body)
  | w, .poss i body =>
      (m.R i w).flatMap (fun u => recoveryObservationSites m u body)

/-- Compile all recovery observations reached from a finite list of roots. -/
def recoveryObservationSitesFrom
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    FiniteSet (RecoveryObservationSite W Ag Atom) :=
  roots.flatMap (fun w => recoveryObservationSites m w phi)

/-- Compositional recovery restricted to an explicit finite list of starting
worlds.  This is distinct from the repository's global predicate, which
quantifies over the whole ambient type `W`. -/
def ModalFormula.CompositionalRecoveryOn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : Prop :=
  forall w, w ∈ roots -> ModalFormula.CompositionalRecoveryAt m w phi

/-- Recursive semantic classicality restricted to finite starting roots. -/
def ModalFormula.CompositionallyClassicalOn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : Prop :=
  forall w, w ∈ roots -> ModalFormula.CompositionallyClassicalAt m w phi

/-- The compiler is exact: recursive semantic classicality at one root holds
iff every compiled recovery observation at that root is classical. -/
theorem compositionallyClassicalAt_iff_recoveryObservationSites
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    forall w,
      ModalFormula.CompositionallyClassicalAt m w phi ↔
        forall site, site ∈ recoveryObservationSites m w phi ->
          site.IsClassicalIn m := by
  induction phi with
  | prop p =>
      intro w
      simp [ModalFormula.CompositionallyClassicalAt,
        recoveryObservationSites, RecoveryObservationSite.IsClassicalIn,
        evalModal]
  | not phi ih =>
      intro w
      simpa [ModalFormula.CompositionallyClassicalAt,
        recoveryObservationSites] using ih w
  | and phi psi ihPhi ihPsi =>
      intro w
      constructor
      · rintro ⟨hPhi, hPsi⟩ site hs
        rcases List.mem_append.mp hs with hs | hs
        · exact (ihPhi w).1 hPhi site hs
        · exact (ihPsi w).1 hPsi site hs
      · intro h
        constructor
        · apply (ihPhi w).2
          intro site hs
          exact h site (List.mem_append_left _ hs)
        · apply (ihPsi w).2
          intro site hs
          exact h site (List.mem_append_right _ hs)
  | bel i body ih =>
      intro w
      constructor
      · rintro ⟨hBody, hRoot⟩ site hs
        rcases List.mem_cons.mp hs with hs | hs
        · subst site
          exact hRoot
        · obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
          exact (ih u).1 (hBody u hu) site hSite
      · intro h
        constructor
        · intro u hu
          apply (ih u).2
          intro site hSite
          apply h site
          exact List.mem_cons_of_mem _
            (List.mem_flatMap.mpr ⟨u, hu, hSite⟩)
        · apply h { world := w, formula := .bel i body }
          exact List.mem_cons_self
  | know i body ih =>
      intro w
      constructor
      · intro h site hs
        obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
        exact (ih u).1 (h u hu) site hSite
      · intro h u hu
        apply (ih u).2
        intro site hSite
        exact h site (List.mem_flatMap.mpr ⟨u, hu, hSite⟩)
  | poss i body ih =>
      intro w
      constructor
      · intro h site hs
        obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
        exact (ih u).1 (h u hu) site hSite
      · intro h u hu
        apply (ih u).2
        intro site hSite
        exact h site (List.mem_flatMap.mpr ⟨u, hu, hSite⟩)

/-- Every compiled observation is either atomic or a belief-result
observation. Negation, conjunction, knowledge, and possibility contribute only
through their recursively inspected children. -/
theorem recoveryObservationSites_atomic_or_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    ∀ w site, site ∈ recoveryObservationSites m w phi ->
      (∃ p, site.formula = ModalFormula.prop p) ∨
        site.IsBeliefObservation := by
  induction phi with
  | prop p =>
      intro w site hs
      simp only [recoveryObservationSites, List.mem_singleton] at hs
      subst site
      exact Or.inl ⟨p, rfl⟩
  | not phi ih =>
      intro w site hs
      exact ih w site hs
  | and phi psi ihPhi ihPsi =>
      intro w site hs
      rcases List.mem_append.mp hs with hs | hs
      · exact ihPhi w site hs
      · exact ihPsi w site hs
  | bel i body ih =>
      intro w site hs
      rcases List.mem_cons.mp hs with hs | hs
      · subst site
        exact Or.inr ⟨i, body, rfl⟩
      · obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
        exact ih u site hSite
  | know i body ih =>
      intro w site hs
      obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
      exact ih u site hSite
  | poss i body ih =>
      intro w site hs
      obtain ⟨u, hu, hSite⟩ := List.mem_flatMap.mp hs
      exact ih u site hSite

/-- Finite-root form of the compiler-shape theorem. -/
theorem recoveryObservationSitesFrom_atomic_or_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (site : RecoveryObservationSite W Ag Atom)
    (hs : site ∈ recoveryObservationSitesFrom m roots phi) :
    (∃ p, site.formula = ModalFormula.prop p) ∨
      site.IsBeliefObservation := by
  obtain ⟨w, hw, hSite⟩ := List.mem_flatMap.mp hs
  exact recoveryObservationSites_atomic_or_belief m phi w site hSite

/-- Finite-root form of the exact compiler theorem. -/
theorem compositionallyClassicalOn_iff_recoveryObservationSitesFrom
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionallyClassicalOn m roots phi ↔
      forall site, site ∈ recoveryObservationSitesFrom m roots phi ->
        site.IsClassicalIn m := by
  constructor
  · intro h site hs
    obtain ⟨w, hw, hSite⟩ := List.mem_flatMap.mp hs
    exact (compositionallyClassicalAt_iff_recoveryObservationSites
      m phi w).1 (h w hw) site hSite
  · intro h w hw
    apply (compositionallyClassicalAt_iff_recoveryObservationSites
      m phi w).2
    intro site hSite
    exact h site (List.mem_flatMap.mpr ⟨w, hw, hSite⟩)

/-- Under probability integrity, recovery on finite roots is characterized
exactly by classicality at all finitely compiled observations. -/
theorem compositionalRecoveryOn_iff_recoveryObservationSitesFrom
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecoveryOn m roots phi ↔
      forall site, site ∈ recoveryObservationSitesFrom m roots phi ->
        site.IsClassicalIn m := by
  rw [← compositionallyClassicalOn_iff_recoveryObservationSitesFrom]
  constructor <;> intro h w hw
  · exact (compositionalRecoveryAt_iff_compositionallyClassicalAt
      m hIntegrity phi w).1 (h w hw)
  · exact (compositionalRecoveryAt_iff_compositionallyClassicalAt
      m hIntegrity phi w).2 (h w hw)

/-- Conditionalization changes only the probability field, so the finite
recovery-observation map itself is invariant. -/
theorem recoveryObservationSites_conditionalize
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag) :
    forall w,
      recoveryObservationSites (conditionalize m E hAdm) w phi =
        recoveryObservationSites m w phi := by
  induction phi with
  | prop p => intro w; rfl
  | not phi ih => intro w; exact ih w
  | and phi psi ihPhi ihPsi =>
      intro w
      simp [recoveryObservationSites, ihPhi, ihPsi]
  | bel i body ih =>
      intro w
      change
        { world := w, formula := ModalFormula.bel i body } ::
            List.flatMap
              (fun u => recoveryObservationSites
                (conditionalize m E hAdm) u body) (m.R i w) =
          { world := w, formula := ModalFormula.bel i body } ::
            List.flatMap
              (fun u => recoveryObservationSites m u body) (m.R i w)
      rw [show
        (fun u => recoveryObservationSites
          (conditionalize m E hAdm) u body) =
        (fun u => recoveryObservationSites m u body) from funext ih]
  | know i body ih =>
      intro w
      change
        List.flatMap
            (fun u => recoveryObservationSites
              (conditionalize m E hAdm) u body) (m.R i w) =
          List.flatMap
            (fun u => recoveryObservationSites m u body) (m.R i w)
      rw [show
        (fun u => recoveryObservationSites
          (conditionalize m E hAdm) u body) =
        (fun u => recoveryObservationSites m u body) from funext ih]
  | poss i body ih =>
      intro w
      change
        List.flatMap
            (fun u => recoveryObservationSites
              (conditionalize m E hAdm) u body) (m.R i w) =
          List.flatMap
            (fun u => recoveryObservationSites m u body) (m.R i w)
      rw [show
        (fun u => recoveryObservationSites
          (conditionalize m E hAdm) u body) =
        (fun u => recoveryObservationSites m u body) from funext ih]

/-- The finite observation map from a root list is likewise invariant under
conditionalization. -/
theorem recoveryObservationSitesFrom_conditionalize
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    recoveryObservationSitesFrom (conditionalize m E hAdm) roots phi =
      recoveryObservationSitesFrom m roots phi := by
  simp [recoveryObservationSitesFrom,
    recoveryObservationSites_conditionalize]

/-- Atomic observations always stutter under probability-only
conditionalization because the valuation field is unchanged. -/
theorem atomicRecoveryObservation_stutters
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (w : W) (p : Atom) :
    RecoveryObservationSite.IsClassicalIn m
        { world := w, formula := ModalFormula.prop p } ↔
      RecoveryObservationSite.IsClassicalIn (conditionalize m E hAdm)
        { world := w, formula := ModalFormula.prop p } := by
  rfl

/-- All recovery-relevant observations retain their classical/nonclassical
status across one conditionalization step. -/
def RecoveryObservationsStutterOn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : Prop :=
  forall site, site ∈ recoveryObservationSitesFrom m roots phi ->
    (site.IsClassicalIn m ↔
      site.IsClassicalIn (conditionalize m E hAdm))

/-- Gate-21 stuttering theorem: if every finitely compiled observation keeps
its classical/nonclassical status, recovery on the finite roots cannot change.
-/
theorem compositionalRecoveryOn_conditionalize_iff_of_observationsStutter
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (hStutter : RecoveryObservationsStutterOn m E hAdm roots phi) :
    ModalFormula.CompositionalRecoveryOn m roots phi ↔
      ModalFormula.CompositionalRecoveryOn
        (conditionalize m E hAdm) roots phi := by
  rw [compositionalRecoveryOn_iff_recoveryObservationSitesFrom
      m hIntegrity roots phi,
    compositionalRecoveryOn_iff_recoveryObservationSitesFrom
      (conditionalize m E hAdm)
      (conditionalize_preserves_probabilityIntegrity
        m hIntegrity E hAdm) roots phi]
  rw [recoveryObservationSitesFrom_conditionalize]
  constructor <;> intro h site hs
  · exact (hStutter site hs).1 (h site hs)
  · exact (hStutter site hs).2 (h site hs)

/-- Contrapositive localization: every recovery change on finite roots has a
specific witness in the finite compiled observation list. -/
theorem recoveryOn_change_has_observation_change
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (hChange : ¬ (ModalFormula.CompositionalRecoveryOn m roots phi ↔
      ModalFormula.CompositionalRecoveryOn
        (conditionalize m E hAdm) roots phi)) :
    ∃ site, site ∈ recoveryObservationSitesFrom m roots phi ∧
      ¬ (site.IsClassicalIn m ↔
        site.IsClassicalIn (conditionalize m E hAdm)) := by
  apply Classical.byContradiction
  intro hNoWitness
  apply hChange
  apply compositionalRecoveryOn_conditionalize_iff_of_observationsStutter
    m hIntegrity E hAdm roots phi
  intro site hs
  apply Classical.byContradiction
  intro hDifferent
  apply hNoWitness
  exact ⟨site, hs, hDifferent⟩

/-- Sharpened localization: atomic observations cannot change under
conditionalization, so every recovery change on finite roots is witnessed by
a changed belief-result observation. -/
theorem recoveryOn_change_has_belief_observation_change
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (hChange : ¬ (ModalFormula.CompositionalRecoveryOn m roots phi ↔
      ModalFormula.CompositionalRecoveryOn
        (conditionalize m E hAdm) roots phi)) :
    ∃ site, site ∈ recoveryObservationSitesFrom m roots phi ∧
      site.IsBeliefObservation ∧
      ¬ (site.IsClassicalIn m ↔
        site.IsClassicalIn (conditionalize m E hAdm)) := by
  obtain ⟨site, hs, hDifferent⟩ :=
    recoveryOn_change_has_observation_change
      m hIntegrity E hAdm roots phi hChange
  rcases recoveryObservationSitesFrom_atomic_or_belief
      m roots phi site hs with hAtomic | hBelief
  · obtain ⟨p, hp⟩ := hAtomic
    rcases site with ⟨world, formula⟩
    dsimp at hp hDifferent
    subst formula
    exact (hDifferent
      (atomicRecoveryObservation_stutters m E hAdm world p)).elim
  · exact ⟨site, hs, hBelief, hDifferent⟩

/-- A finite root list covers the ambient world type.  The base `Model`
structure does not require its `worlds` list to satisfy this property. -/
def WorldListCovers {W : Type} (roots : FiniteSet W) : Prop :=
  forall w, w ∈ roots

/-- With an explicit coverage proof, recovery on a finite root list is exactly
the repository's globally quantified recovery predicate. -/
theorem compositionalRecoveryOn_iff_global_of_covers
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (hCovers : WorldListCovers roots) :
    ModalFormula.CompositionalRecoveryOn m roots phi ↔
      ModalFormula.CompositionalRecovery m phi := by
  constructor
  · intro h w
    exact h w (hCovers w)
  · intro h w _
    exact h w

/-- If the finite roots cover the ambient world type, every global recovery
change under conditionalization is witnessed by one entry of the finite
compiled observation map. -/
theorem globalRecovery_change_has_finite_observation_change_of_covers
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (hCovers : WorldListCovers roots)
    (phi : ModalFormula Atom Ag)
    (hChange : ¬ (ModalFormula.CompositionalRecovery m phi ↔
      ModalFormula.CompositionalRecovery
        (conditionalize m E hAdm) phi)) :
    ∃ site, site ∈ recoveryObservationSitesFrom m roots phi ∧
      site.IsBeliefObservation ∧
      ¬ (site.IsClassicalIn m ↔
        site.IsClassicalIn (conditionalize m E hAdm)) := by
  apply recoveryOn_change_has_belief_observation_change
    m hIntegrity E hAdm roots phi
  intro hOn
  apply hChange
  constructor
  · intro hBefore
    have hBeforeOn :=
      (compositionalRecoveryOn_iff_global_of_covers
        m roots phi hCovers).2 hBefore
    have hAfterOn := hOn.1 hBeforeOn
    exact (compositionalRecoveryOn_iff_global_of_covers
      (conditionalize m E hAdm) roots phi hCovers).1 hAfterOn
  · intro hAfter
    have hAfterOn :=
      (compositionalRecoveryOn_iff_global_of_covers
        (conditionalize m E hAdm) roots phi hCovers).2 hAfter
    have hBeforeOn := hOn.2 hAfterOn
    exact (compositionalRecoveryOn_iff_global_of_covers
      m roots phi hCovers).1 hBeforeOn

/-! ## Gate-19 finite-map instance -/

theorem gate21_gate19Support_covers : WorldListCovers gate19Support := by
  intro w
  cases w <;> decide +kernel

/-- For `B(p)` at all four Gate-19 roots, the exact recursive observation tree
contains four belief-result sites and sixteen accessible atomic sites. -/
theorem gate21_gate19_recoveryObservation_count :
    (recoveryObservationSitesFrom gate19StrongModel.toModel
      gate19Support gate19BelP).length = 20 := by
  decide +kernel

/-- The same twenty observation positions are retained after the first
conditionalization; only their evaluated statuses may change. -/
theorem gate21_gate19_observation_map_stable_afterQ :
    recoveryObservationSitesFrom gate19AfterQ.toModel
        gate19Support gate19BelP =
      recoveryObservationSitesFrom gate19StrongModel.toModel
        gate19Support gate19BelP := by
  exact recoveryObservationSitesFrom_conditionalize
    gate19StrongModel.toModel gate19EvidenceQ
    gate19EvidenceQ_admissible gate19Support gate19BelP

/-- One explicit entry of the finite map witnesses the first Gate-19 recovery
loss: `B(p)` is classical at world `a` before the update and nonclassical
after conditioning on `q`. -/
theorem gate21_gate19_first_loss_observation_witness :
    let site : RecoveryObservationSite Gate19World Unit Gate19Atom :=
      { world := Gate19World.a, formula := gate19BelP }
    site ∈ recoveryObservationSitesFrom gate19StrongModel.toModel
        gate19Support gate19BelP ∧
      site.IsClassicalIn gate19StrongModel.toModel ∧
      ¬ site.IsClassicalIn gate19AfterQ.toModel := by
  dsimp only
  constructor
  · simp [recoveryObservationSitesFrom, recoveryObservationSites,
      gate19Support, gate19BelP]
  constructor
  · change IsClassicalValue
      (evalModal gate19StrongModel.toModel Gate19World.a gate19BelP)
    rw [gate19_loss_return_profile.1 Gate19World.a]
    exact Or.inl rfl
  · change ¬ IsClassicalValue
      (evalModal gate19AfterQ.toModel Gate19World.a gate19BelP)
    rw [gate19_loss_return_profile.2.1 Gate19World.a]
    simp [IsClassicalValue, FDEValue.N, FDEValue.T, FDEValue.F]

end PEL4
