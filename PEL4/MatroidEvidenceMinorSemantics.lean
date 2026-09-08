import PEL4.MatroidEvidenceMinors

namespace PEL4

/-!
# Gate 4 semantic consequences of genuine minors

Deletion and contraction are both structural matroid operations, but they have very
different epistemic readings at the coarse two-channel projection.  This file records
that difference without identifying contraction itself with belief revision.
-/

universe u

/-- Deleting an atom cannot affect a different polarity channel. -/
theorem supportsChannel_delete_otherPolarity_iff
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (x : α)
    (channel : EvidencePolarity)
    (hDifferent : polarity x ≠ channel) :
    supportsGroundChannel
        (EvidenceSet.diff ground (EvidenceSet.singleton x))
        polarity channel ↔
      supportsGroundChannel ground polarity channel := by
  constructor
  · intro h
    cases h with
    | intro e he => exact ⟨e, he.1.1, he.2⟩
  · intro h
    cases h with
    | intro e he =>
        have hex : e ≠ x := by
          intro hex
          subst e
          exact hDifferent he.2
        exact ⟨e, ⟨he.1, hex⟩, he.2⟩

/--
Deleting a unique channel representative removes exactly that support channel and
leaves every different channel unchanged.
-/
theorem delete_unique_channel_profile
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hUnique : UniqueChannelRepresentative ground polarity c) :
    (¬ supportsGroundChannel
        (EvidenceSet.diff ground (EvidenceSet.singleton c))
        polarity (polarity c)) ∧
      ∀ channel,
        polarity c ≠ channel →
        (supportsGroundChannel
            (EvidenceSet.diff ground (EvidenceSet.singleton c))
            polarity channel ↔
          supportsGroundChannel ground polarity channel) := by
  constructor
  · exact delete_unique_channel_not_supported ground polarity c hUnique
  · intro channel hDifferent
    exact supportsChannel_delete_otherPolarity_iff
      ground polarity c channel hDifferent

/-- The original finite channel matroid is loopless. -/
theorem finiteChannel_no_loops
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (e : α) :
    ¬ GroundMatroidClosure.IsLoop
      (finiteChannelMatroid G polarity).toGroundMatroidClosure e := by
  intro h
  cases h.2.2 with
  | intro a ha =>
      exact False.elim ha.2.1

/-- A polarity has active support when some nonloop ground atom realizes it. -/
def supportsNonloopChannel {α : Type u}
    (M : GroundMatroidClosure α)
    (polarity : α → EvidencePolarity)
    (channel : EvidencePolarity) : Prop :=
  ∃ e,
    M.ground e ∧
    ¬ GroundMatroidClosure.IsLoop M e ∧
    polarity e = channel

/-- Before taking minors, ordinary ground support and nonloop support coincide. -/
theorem finiteChannel_supportsNonloop_iff_supportsGround
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (channel : EvidencePolarity) :
    supportsNonloopChannel
        (finiteChannelMatroid G polarity).toGroundMatroidClosure
        polarity channel ↔
      supportsGroundChannel G.carrier polarity channel := by
  constructor
  · intro h
    cases h with
    | intro e he => exact ⟨e, he.1, he.2.2⟩
  · intro h
    cases h with
    | intro e he =>
        exact ⟨e, he.1, finiteChannel_no_loops G polarity e, he.2⟩

/--
After contracting `c`, no remaining atom of `c`'s polarity provides nonloop support:
all such atoms are loops relative to the accepted background direction.
-/
theorem finiteChannel_contract_sameChannel_no_nonloop
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hc : G.carrier c) :
    ¬ supportsNonloopChannel
      ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure
      polarity (polarity c) := by
  intro h
  cases h with
  | intro e he =>
      have hLoop :
          GroundMatroidClosure.IsLoop
            ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure e :=
        (finiteChannel_contractElem_isLoop_iff G polarity c e hc).2
          ⟨he.1.1, by
            intro hec
            exact he.1.2 hec, he.2.2.symm⟩
      exact he.2.1 hLoop

/-- Any loop created by contracting `c` must lie in `c`'s polarity class. -/
theorem finiteChannel_contract_opposite_not_loop
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c e : α)
    (hc : G.carrier c)
    (hDifferent : polarity c ≠ polarity e) :
    ¬ GroundMatroidClosure.IsLoop
      ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure e := by
  intro hLoop
  have hData := (finiteChannel_contractElem_isLoop_iff G polarity c e hc).1 hLoop
  exact hDifferent hData.2.2

/--
Contraction preserves nonloop support in every channel different from the contracted
one.  Thus one independent channel is quotiented out while the opposite channel stays
active whenever it was present before contraction.
-/
theorem finiteChannel_contract_otherChannel_supportsNonloop_iff
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hc : G.carrier c)
    (channel : EvidencePolarity)
    (hDifferent : polarity c ≠ channel) :
    supportsNonloopChannel
        ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure
        polarity channel ↔
      supportsGroundChannel G.carrier polarity channel := by
  constructor
  · intro h
    cases h with
    | intro e he => exact ⟨e, he.1.1, he.2.2⟩
  · intro h
    cases h with
    | intro e he =>
        have hec : e ≠ c := by
          intro hec
          subst e
          exact hDifferent he.2
        have hMinorGround :
            ((finiteChannelMatroid G polarity).contractElem c hc).ground e :=
          ⟨he.1, hec⟩
        have hNotLoop :=
          finiteChannel_contract_opposite_not_loop
            G polarity c e hc (by
              intro hce
              exact hDifferent (Eq.trans hce he.2))
        exact ⟨e, hMinorGround, hNotLoop, he.2⟩

end PEL4
