import PEL4.NeighbourhoodBelief

namespace PEL4

/-!
# The Santos bridge: relational evidence-knowledge versus Lockean belief

Santos, *A Four-Valued Dynamic Epistemic Logic* (JoLLI 2020), evaluates a box over
Belnap–Dunn valued Kripke models: `□φ` is supported iff `φ` is supported at every
accessible state, and refuted iff `φ` is refuted at some accessible state
(`¬□φ ≡ ◇¬φ`).  Belief is left there as future work.  This file relates that box to
the 4-PEL threshold belief on the same model:

* **sandwich** – in the truth order, `□φ ≤ Bφ`: a supported box forces supported
  belief, refuted belief forces a refuted box (legacy `Model` suffices);
* **limit `c = 1`** – on a regular measure (every accessible world has positive mass)
  the positive channels coincide, hence aggregation (C) returns for support;
* **strictness** – for `c < 1` the two operators can take opposite classical values,
  and even at `c = 1` the refutation channels differ (`all` versus `some`).

The clauses for `□` follow the standard Belnap–Dunn modal semantics that the visible
text of the paper states for `◇` and `¬◇`; they agree with `standardBoxPositive` /
`standardBoxNegative` of `KnowledgeSemantics`, here on semantic values.
-/

/-- Santos-style relational box on a four-valued proposition. -/
def santosBox {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) : FDEValue :=
  { pos := (m.R i w).all (fun u => (value u).pos)
  , neg := (m.R i w).any (fun u => (value u).neg) }

/-- Sandwich, support side: a supported box yields supported belief (any threshold). -/
theorem santosBox_pos_implies_belief_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue)
    (h : (santosBox m i w value).pos = true) :
    (belief m i w value).pos = true := by
  rw [belief_pos_iff_neighbourhood]
  have hall : ∀ u, u ∈ m.R i w → (value u).pos = true := by
    simpa [santosBox] using h
  have hEq : posExtension m i w value = m.R i w := by
    unfold posExtension filterWorlds
    exact List.filter_eq_self.mpr hall
  rw [hEq]
  exact neighbourhood_N m i w

/-- Sandwich, refutation side: refuted belief yields a refuted box (any threshold). -/
theorem belief_neg_implies_santosBox_neg
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue)
    (h : (belief m i w value).neg = true) :
    (santosBox m i w value).neg = true := by
  rw [belief_neg_iff_neighbourhood] at h
  cases hany : (santosBox m i w value).neg with
  | true => rfl
  | false =>
    have hnone : ∀ u, u ∈ m.R i w → (value u).neg = false := by
      simpa [santosBox] using hany
    have hEq : negExtension m i w value = [] := by
      unfold negExtension filterWorlds
      exact List.filter_eq_nil_iff.mpr (fun u hu => by simp [hnone u hu])
    rw [hEq] at h
    exact absurd h (neighbourhood_P m i w)

/-- Every accessible world carries positive mass. -/
def RegularAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) : Prop :=
  ∀ u, u ∈ m.R i w → 0 < m.mu i w [u]

/-- Limit `c = 1`: on a regular measure, supported belief forces a supported box. -/
theorem belief_pos_implies_santosBox_pos_of_certainty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (value : W → FDEValue) (hc : m.c i = 1) (hreg : RegularAt m i w)
    (hb : (belief m i w value).pos = true) :
    (santosBox m i w value).pos = true := by
  rw [belief_pos_iff_neighbourhood] at hb
  have hall : ∀ u, u ∈ m.R i w → (value u).pos = true := by
    intro u hu
    cases hv : (value u).pos with
    | true => rfl
    | false =>
      have hnd := (h i w).support_nodup
      have hPnd : (posExtension m i w value).Nodup := hnd.filter _
      have hPsub : FiniteEventSubset (posExtension m i w value) (m.R i w) :=
        fun x hx => (List.mem_filter.mp hx).1
      have hunot : u ∉ posExtension m i w value := by
        intro hx
        have := (List.mem_filter.mp hx).2
        simp [hv] at this
      have hund : [u].Nodup := by simp
      have husub : FiniteEventSubset [u] (m.R i w) := by
        intro x hx; rw [List.mem_singleton.mp hx]; exact hu
      have hdis : FiniteEventDisjoint (posExtension m i w value) [u] := by
        intro x hx hx'; rw [List.mem_singleton.mp hx'] at hx; exact hunot hx
      have hadd := (h i w).add_disjoint _ _ hPnd hund hPsub husub hdis
      have hnd' : (posExtension m i w value ++ [u]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hPnd, hund, fun a ha b hb hab => hdis a ha (hab ▸ hb)⟩
      have hsub' : FiniteEventSubset (posExtension m i w value ++ [u]) (m.R i w) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hPsub x hx
        · exact husub x hx
      have hmono := (h i w).monotone _ _ hnd' hnd hsub' (fun x hx => hx)
      have htot := (h i w).total
      have hpos := hreg u hu
      unfold BeliefNeighbourhood ThresholdNeighbourhood at hb
      grind
  simpa [santosBox] using hall

/-- At `c = 1` on a regular measure the support channels of `□` and `B` coincide. -/
theorem belief_pos_eq_santosBox_pos_of_certainty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (value : W → FDEValue) (hc : m.c i = 1) (hreg : RegularAt m i w) :
    (belief m i w value).pos = (santosBox m i w value).pos := by
  cases hb : (belief m i w value).pos with
  | true => exact (belief_pos_implies_santosBox_pos_of_certainty m h i w value hc hreg hb).symm
  | false =>
    cases hs : (santosBox m i w value).pos with
    | false => rfl
    | true => rw [santosBox_pos_implies_belief_pos m i w value hs] at hb; cases hb

/-- **C returns at certainty**: for `c = 1` on a regular measure, support of belief is
closed under conjunction. -/
theorem belief_pos_and_of_certainty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (v1 v2 : W → FDEValue) (hc : m.c i = 1) (hreg : RegularAt m i w)
    (h1 : (belief m i w v1).pos = true) (h2 : (belief m i w v2).pos = true) :
    (belief m i w (fun u => (v1 u).and (v2 u))).pos = true := by
  apply santosBox_pos_implies_belief_pos
  have a1 := belief_pos_implies_santosBox_pos_of_certainty m h i w v1 hc hreg h1
  have a2 := belief_pos_implies_santosBox_pos_of_certainty m h i w v2 hc hreg h2
  simp [santosBox, FDEValue.and] at a1 a2 ⊢
  exact fun u hu => ⟨a1 u hu, a2 u hu⟩

/-! ## Strictness: a finite witness below certainty -/

/-- Three equiprobable worlds, threshold `2/3`. -/
def santosGapModel : Model (Fin 3) Unit Unit :=
  { worlds := [0, 1, 2]
  , R := fun _ _ => [0, 1, 2]
  , mu := fun _ _ => uniform3
  , val := fun u _ => if u = 2 then FDEValue.F else FDEValue.T
  , c := fun _ => 2 / 3
  , mu_total := by intro _ _; simp [uniform3]; grind
  , mu_empty := by intro _ _; simp [uniform3]; grind
  , c_gt_half := by intro _; grind
  , c_le_one := by intro _; grind }

/-- Two of three worlds support `p`, one refutes it. -/
def santosGapValue : Fin 3 → FDEValue := fun u => santosGapModel.val u ()

/-- Below certainty the operators can disagree classically: Lockean belief is `T`
while the Santos box is `F`. -/
theorem belief_T_but_santosBox_F :
    belief santosGapModel () 0 santosGapValue = FDEValue.T ∧
    santosBox santosGapModel () 0 santosGapValue = FDEValue.F := by
  refine ⟨?_, ?_⟩
  · simp [belief, filterWorlds, santosGapValue, santosGapModel, uniform3, FDEValue.T,
      FDEValue.F]
    grind
  · simp [santosBox, santosGapValue, santosGapModel, FDEValue.T, FDEValue.F]

end PEL4
