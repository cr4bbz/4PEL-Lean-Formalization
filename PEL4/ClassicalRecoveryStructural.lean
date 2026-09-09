import PEL4.ClassicalRecovery

namespace PEL4

/-!
# Gate 5B: structural classicality and residual information capacity

`ChannelRegular` is an occupancy notion: one coarse polarity is present and the
other is absent. Gate 4 showed that contraction can leave atoms in the ground
set while turning them into loops. This file therefore refines classical
recovery by measuring completeness through nonloop support, i.e. through
residual independent channel capacity.

Before minors the canonical finite channel matroid is loopless, so occupancy
regularity and nonloop regularity coincide. After contraction they can diverge.
This gives a precise structural meaning to the additional requirement that a
recovered classical state be informationally robust rather than merely
classically labelled at the coarse value level.
-/

universe u

/-- At least one polarity retains a nonloop representative. -/
def NonloopChannelComplete {α : Type u}
    (M : GroundMatroidClosure α)
    (polarity : α → EvidencePolarity) : Prop :=
  supportsNonloopChannel M polarity EvidencePolarity.positive ∨
  supportsNonloopChannel M polarity EvidencePolarity.negative

/-- The two polarities are not both independently active. -/
def NonloopChannelConsistent {α : Type u}
    (M : GroundMatroidClosure α)
    (polarity : α → EvidencePolarity) : Prop :=
  ¬ (supportsNonloopChannel M polarity EvidencePolarity.positive ∧
     supportsNonloopChannel M polarity EvidencePolarity.negative)

/-- Structural classicality measured by residual independent channel capacity. -/
def NonloopChannelRegular {α : Type u}
    (M : GroundMatroidClosure α)
    (polarity : α → EvidencePolarity) : Prop :=
  NonloopChannelComplete M polarity ∧ NonloopChannelConsistent M polarity

/-- In the original loopless channel matroid, nonloop completeness is exactly
ordinary channel completeness. -/
theorem finiteChannel_nonloopComplete_iff_channelComplete
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity) :
    NonloopChannelComplete
        (finiteChannelMatroid G polarity).toGroundMatroidClosure polarity ↔
      ChannelComplete polarity G.carrier := by
  change
    (supportsNonloopChannel
        (finiteChannelMatroid G polarity).toGroundMatroidClosure
        polarity EvidencePolarity.positive ∨
      supportsNonloopChannel
        (finiteChannelMatroid G polarity).toGroundMatroidClosure
        polarity EvidencePolarity.negative) ↔
    (supportsGroundChannel G.carrier polarity EvidencePolarity.positive ∨
      supportsGroundChannel G.carrier polarity EvidencePolarity.negative)
  rw [finiteChannel_supportsNonloop_iff_supportsGround
        G polarity EvidencePolarity.positive,
      finiteChannel_supportsNonloop_iff_supportsGround
        G polarity EvidencePolarity.negative]

/-- In the original loopless channel matroid, nonloop consistency is exactly
ordinary channel consistency. -/
theorem finiteChannel_nonloopConsistent_iff_channelConsistent
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity) :
    NonloopChannelConsistent
        (finiteChannelMatroid G polarity).toGroundMatroidClosure polarity ↔
      ChannelConsistent polarity G.carrier := by
  change
    (¬ (supportsNonloopChannel
          (finiteChannelMatroid G polarity).toGroundMatroidClosure
          polarity EvidencePolarity.positive ∧
        supportsNonloopChannel
          (finiteChannelMatroid G polarity).toGroundMatroidClosure
          polarity EvidencePolarity.negative)) ↔
    ¬ (supportsGroundChannel G.carrier polarity EvidencePolarity.positive ∧
       supportsGroundChannel G.carrier polarity EvidencePolarity.negative)
  rw [finiteChannel_supportsNonloop_iff_supportsGround
        G polarity EvidencePolarity.positive,
      finiteChannel_supportsNonloop_iff_supportsGround
        G polarity EvidencePolarity.negative]

/-- Before minors, value-level regularity and independent-capacity regularity
coincide for the canonical channel matroid. -/
theorem finiteChannel_nonloopRegular_iff_channelRegular
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity) :
    NonloopChannelRegular
        (finiteChannelMatroid G polarity).toGroundMatroidClosure polarity ↔
      ChannelRegular polarity G.carrier := by
  unfold NonloopChannelRegular ChannelRegular
  rw [finiteChannel_nonloopComplete_iff_channelComplete G polarity,
      finiteChannel_nonloopConsistent_iff_channelConsistent G polarity]

/-- Contracting any supported atom from channel-regular evidence exhausts all
nonloop channel completeness. The contracted polarity loses nonloop support by
Gate 4, while regularity excludes support for the opposite polarity. -/
theorem finiteChannel_contract_regular_not_nonloopComplete
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hc : G.carrier c)
    (hRegular : ChannelRegular polarity G.carrier) :
    ¬ NonloopChannelComplete
      ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure
      polarity := by
  intro hComplete
  have hConsistent := hRegular.2
  unfold ChannelConsistent at hConsistent
  change
    ¬ (supportsGroundChannel G.carrier polarity EvidencePolarity.positive ∧
       supportsGroundChannel G.carrier polarity EvidencePolarity.negative)
    at hConsistent
  unfold NonloopChannelComplete at hComplete
  cases hpc : polarity c with
  | positive =>
      rcases hComplete with hPos | hNeg
      · exact (finiteChannel_contract_sameChannel_no_nonloop G polarity c hc)
          (by simpa [hpc] using hPos)
      · have hNegGround :
            supportsGroundChannel G.carrier polarity EvidencePolarity.negative :=
          (finiteChannel_contract_otherChannel_supportsNonloop_iff
            G polarity c hc EvidencePolarity.negative (by simp [hpc])).1 hNeg
        have hPosGround :
            supportsGroundChannel G.carrier polarity EvidencePolarity.positive :=
          ⟨c, hc, hpc⟩
        exact hConsistent ⟨hPosGround, hNegGround⟩
  | negative =>
      rcases hComplete with hPos | hNeg
      · have hPosGround :
            supportsGroundChannel G.carrier polarity EvidencePolarity.positive :=
          (finiteChannel_contract_otherChannel_supportsNonloop_iff
            G polarity c hc EvidencePolarity.positive (by simp [hpc])).1 hPos
        have hNegGround :
            supportsGroundChannel G.carrier polarity EvidencePolarity.negative :=
          ⟨c, hc, hpc⟩
        exact hConsistent ⟨hPosGround, hNegGround⟩
      · exact (finiteChannel_contract_sameChannel_no_nonloop G polarity c hc)
          (by simpa [hpc] using hNeg)

/-- Hence contraction of a supported atom from regular evidence destroys
nonloop regularity, even though ordinary ground occupancy can remain. -/
theorem finiteChannel_contract_regular_not_nonloopRegular
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hc : G.carrier c)
    (hRegular : ChannelRegular polarity G.carrier) :
    ¬ NonloopChannelRegular
      ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure
      polarity := by
  intro hNonloopRegular
  exact (finiteChannel_contract_regular_not_nonloopComplete
    G polarity c hc hRegular) hNonloopRegular.1

/-- A parallel atom can remain as ordinary ground support after contraction even
though the entire contracted polarity has lost nonloop support. This is the
explicit occupancy/capacity divergence relevant to classical recovery. -/
theorem finiteChannel_contract_parallel_occupancy_without_nonloop
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c y : α)
    (hc : G.carrier c)
    (hy : G.carrier y)
    (hcy : c ≠ y)
    (hpol : polarity c = polarity y) :
    supportsGroundChannel
        ((finiteChannelMatroid G polarity).contractElem c hc).ground
        polarity (polarity c) ∧
      ¬ supportsNonloopChannel
        ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure
        polarity (polarity c) := by
  constructor
  · refine ⟨y, ?_, hpol.symm⟩
    change G.carrier y ∧ ¬ EvidenceSet.singleton c y
    exact ⟨hy, by
      intro hyc
      change y = c at hyc
      exact hcy hyc.symm⟩
  · exact finiteChannel_contract_sameChannel_no_nonloop G polarity c hc

end PEL4
