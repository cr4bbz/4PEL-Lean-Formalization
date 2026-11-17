import PEL4.SantosBridge
import PEL4.Dynamics

namespace PEL4

/-!
# Santos bridge, dynamic part: a reduction law for Lockean belief

Santos' four-valued DEL reduces announcements to static formulas.  For threshold
belief the analogous update in 4-PEL is conditionalisation on the positive extension
of the evidence formula.  This file proves the basic reduction: belief after the
update is a *conditional* neighbourhood statement before the update,

  `X ∈ N_c^E(w)  ↔  μ_w(X ∩ E⁺) ≥ c · μ_w(E⁺)`,

for both channels, whenever the evidence has positive mass.  It also records the
static dual of the certainty theorem: at `c = 1` refutation of belief is *universal*
refutation (`□¬`), whereas the Santos box is refuted by a single world (`◇¬`).

The reduction is stated for a fixed semantic value `W → FDEValue`.  Whether the value
of a *formula* containing belief operators is itself invariant under the update is
the open part (see `docs/SANTOS_BRIDGE.md`).
-/

/-- Positive extension of the evidence formula inside the accessible range. -/
def evidenceExtension {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (E : Formula Atom Ag) : FiniteSet W :=
  filterWorlds (m.R i w) (fun u => (eval m u E).pos)

/-- Conditional Lockean neighbourhood: `X` has at least the fraction `c` of the
evidence mass. -/
def ConditionalNeighbourhood {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (E : Formula Atom Ag)
    (X : FiniteSet W) : Prop :=
  m.mu i w (intersectWorlds X (evidenceExtension m i w E)) ≥
    m.c i * conditionalizationEvidenceMass m i w E

private theorem rat_le_div_iff (x e c : Rat) (he : 0 < e) : c ≤ x / e ↔ c * e ≤ x := by
  constructor
  · intro h
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt he)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt he)] at this
    exact this
  · intro h
    have hi : 0 ≤ e⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr he)
    have := Rat.mul_le_mul_of_nonneg_right h hi
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt he), Rat.mul_one] at this
    rw [Rat.div_def]; exact this

/-- The updated measure is the conditional measure whenever the evidence has
positive mass. -/
theorem conditionalize_mu_ge_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (E : Formula Atom Ag)
    (hpos : 0 < conditionalizationEvidenceMass m i w E) (X : FiniteSet W) :
    conditionalize_mu m i w E X ≥ m.c i ↔ ConditionalNeighbourhood m i w E X := by
  have hne : conditionalizationEvidenceMass m i w E ≠ 0 := Rat.ne_of_gt hpos
  unfold conditionalizationEvidenceMass at hpos hne
  simp only [conditionalize_mu, ConditionalNeighbourhood, evidenceExtension,
    conditionalizationEvidenceMass, ge_iff_le]
  simp only [beq_iff_eq, hne, if_false]
  exact rat_le_div_iff _ _ _ hpos

/-- **Reduction, support channel**: belief after conditionalising on `E` is a
conditional neighbourhood statement in the original model. -/
theorem belief_conditionalize_pos_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (value : W → FDEValue)
    (hpos : 0 < conditionalizationEvidenceMass m i w E) :
    (belief (conditionalize m E h) i w value).pos = true ↔
      ConditionalNeighbourhood m i w E (posExtension m i w value) := by
  rw [← conditionalize_mu_ge_iff m i w E hpos]
  simp [belief, conditionalize, posExtension]

/-- **Reduction, refutation channel**. -/
theorem belief_conditionalize_neg_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (value : W → FDEValue)
    (hpos : 0 < conditionalizationEvidenceMass m i w E) :
    (belief (conditionalize m E h) i w value).neg = true ↔
      ConditionalNeighbourhood m i w E (negExtension m i w value) := by
  rw [← conditionalize_mu_ge_iff m i w E hpos]
  simp [belief, conditionalize, negExtension]

/-- Belief of the negated proposition swaps the two channels. -/
theorem belief_not_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (value : W → FDEValue) :
    (belief m i w (fun u => (value u).not)).pos = (belief m i w value).neg := by
  simp [belief, FDEValue.not]

/-- **Strong refutation at certainty**: for `c = 1` on a regular measure, belief is
refuted iff the proposition is refuted at *every* accessible world.  The Santos box
is already refuted by one such world, so the refutation channels differ even in the
limit where the support channels coincide. -/
theorem belief_neg_iff_all_neg_of_certainty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (value : W → FDEValue) (hc : m.c i = 1) (hreg : RegularAt m i w) :
    (belief m i w value).neg = true ↔ ∀ u, u ∈ m.R i w → (value u).neg = true := by
  rw [← belief_not_pos,
    belief_pos_eq_santosBox_pos_of_certainty m h i w _ hc hreg]
  simp [santosBox, FDEValue.not]

end PEL4
