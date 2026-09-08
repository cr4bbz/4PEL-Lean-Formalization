import PEL4.MatroidEvidenceCircuits

namespace PEL4

/-!
# Gate 4: genuine matroid minors for coarse 4-PEL evidence

The previous gates used a deliberately lightweight closure presentation without an
explicit ground set.  This file adds a finite-ground certificate and defines deletion
and contraction as genuine closure minors.  The definitions mirror the standard
matroid closure formulas:

* deletion restricts both the ground set and closure to `E \ D`;
* contraction has ground set `E \ C` and closure
  `cl_{M/C}(A) = cl_M(A ∪ C) \ C`.

The layer remains independent of Mathlib.  Its purpose is to make the epistemic
difference between removing evidence and quotienting by accepted background evidence
precise without changing the repository's dependency footprint.
-/

universe u

namespace EvidenceSet

/-- Union of predicate-presented sets. -/
def union {α : Type u} (A B : EvidenceSet α) : EvidenceSet α :=
  fun x => A x ∨ B x

/-- Difference of predicate-presented sets. -/
def diff {α : Type u} (A B : EvidenceSet α) : EvidenceSet α :=
  fun x => A x ∧ ¬ B x

/-- Every set is included in its union with another set. -/
theorem subset_union_left {α : Type u} (A B : EvidenceSet α) :
    EvidenceSet.Subset A (EvidenceSet.union A B) := by
  intro x hx
  exact Or.inl hx

/-- The right operand is included in a union. -/
theorem subset_union_right {α : Type u} (A B : EvidenceSet α) :
    EvidenceSet.Subset B (EvidenceSet.union A B) := by
  intro x hx
  exact Or.inr hx

end EvidenceSet

/--
A closure presentation of a matroid with an explicit ground set.  The axioms are
required only for input sets contained in the ground set; the closure itself always
lands back in the ground set.
-/
structure GroundMatroidClosure (α : Type u) where
  ground : EvidenceSet α
  cl : EvidenceSet α → EvidenceSet α
  cl_ground : ∀ A, EvidenceSet.Subset (cl A) ground
  extensive : ∀ {A},
    EvidenceSet.Subset A ground → EvidenceSet.Subset A (cl A)
  monotone : ∀ {A B},
    EvidenceSet.Subset A B →
    EvidenceSet.Subset B ground →
    EvidenceSet.Subset (cl A) (cl B)
  idempotent : ∀ {A},
    EvidenceSet.Subset A ground →
    EvidenceSet.Subset (cl (cl A)) (cl A)
  exchange : ∀ {A} {x y : α},
    EvidenceSet.Subset A ground →
    ground x →
    ground y →
    cl (EvidenceSet.insert y A) x →
    ¬ cl A x →
    cl (EvidenceSet.insert x A) y

/--
Finite-ground certificate.  `support` need only cover the ground set; duplicates and
extra entries are harmless, so no decidable equality is required.
-/
structure FiniteGroundMatroidClosure (α : Type u) extends GroundMatroidClosure α where
  support : List α
  ground_listed : ∀ {x}, ground x → x ∈ support

namespace GroundMatroidClosure

/-- Genuine deletion minor. -/
def delete {α : Type u}
    (M : GroundMatroidClosure α)
    (D : EvidenceSet α) : GroundMatroidClosure α where
  ground := EvidenceSet.diff M.ground D
  cl := fun A x => M.cl A x ∧ ¬ D x
  cl_ground := by
    intro A x hx
    exact ⟨M.cl_ground A hx.1, hx.2⟩
  extensive := by
    intro A hA x hx
    have hAGround : EvidenceSet.Subset A M.ground := by
      intro z hz
      exact (hA hz).1
    exact ⟨M.extensive hAGround hx, (hA hx).2⟩
  monotone := by
    intro A B hAB hBGround x hx
    have hBOriginal : EvidenceSet.Subset B M.ground := by
      intro z hz
      exact (hBGround hz).1
    exact ⟨M.monotone hAB hBOriginal hx.1, hx.2⟩
  idempotent := by
    intro A hA x hx
    have hAGround : EvidenceSet.Subset A M.ground := by
      intro z hz
      exact (hA hz).1
    have hDeleteClSub :
        EvidenceSet.Subset
          (fun z => M.cl A z ∧ ¬ D z)
          (M.cl A) := by
      intro z hz
      exact hz.1
    have hClGround : EvidenceSet.Subset (M.cl A) M.ground :=
      M.cl_ground A
    have hStep : M.cl (M.cl A) x :=
      M.monotone hDeleteClSub hClGround hx.1
    exact ⟨M.idempotent hAGround hStep, hx.2⟩
  exchange := by
    intro A x y hA hxGround hyGround hInsert hxNot
    have hAOriginal : EvidenceSet.Subset A M.ground := by
      intro z hz
      exact (hA hz).1
    have hxNotOriginal : ¬ M.cl A x := by
      intro hxCl
      exact hxNot ⟨hxCl, hxGround.2⟩
    have hEx := M.exchange hAOriginal hxGround.1 hyGround.1 hInsert.1 hxNotOriginal
    exact ⟨hEx, hyGround.2⟩

/-- Genuine contraction minor, assuming the contracted set lies in the ground set. -/
def contract {α : Type u}
    (M : GroundMatroidClosure α)
    (C : EvidenceSet α)
    (hC : EvidenceSet.Subset C M.ground) : GroundMatroidClosure α where
  ground := EvidenceSet.diff M.ground C
  cl := fun A x => M.cl (EvidenceSet.union A C) x ∧ ¬ C x
  cl_ground := by
    intro A x hx
    exact ⟨M.cl_ground (EvidenceSet.union A C) hx.1, hx.2⟩
  extensive := by
    intro A hA x hx
    have hUnionGround :
        EvidenceSet.Subset (EvidenceSet.union A C) M.ground := by
      intro z hz
      cases hz with
      | inl hAz => exact (hA hAz).1
      | inr hCz => exact hC hCz
    have hxUnion : EvidenceSet.union A C x := Or.inl hx
    exact ⟨M.extensive hUnionGround hxUnion, (hA hx).2⟩
  monotone := by
    intro A B hAB hBGround x hx
    have hUnionSub :
        EvidenceSet.Subset
          (EvidenceSet.union A C)
          (EvidenceSet.union B C) := by
      intro z hz
      cases hz with
      | inl hAz => exact Or.inl (hAB hAz)
      | inr hCz => exact Or.inr hCz
    have hUnionBGround :
        EvidenceSet.Subset (EvidenceSet.union B C) M.ground := by
      intro z hz
      cases hz with
      | inl hBz => exact (hBGround hBz).1
      | inr hCz => exact hC hCz
    exact ⟨M.monotone hUnionSub hUnionBGround hx.1, hx.2⟩
  idempotent := by
    intro A hA x hx
    have hUnionGround :
        EvidenceSet.Subset (EvidenceSet.union A C) M.ground := by
      intro z hz
      cases hz with
      | inl hAz => exact (hA hAz).1
      | inr hCz => exact hC hCz
    have hInnerToOriginalClosure :
        EvidenceSet.Subset
          (EvidenceSet.union
            (fun z => M.cl (EvidenceSet.union A C) z ∧ ¬ C z)
            C)
          (M.cl (EvidenceSet.union A C)) := by
      intro z hz
      cases hz with
      | inl hClz => exact hClz.1
      | inr hCz =>
          exact M.extensive hUnionGround (Or.inr hCz)
    have hClosureGround :
        EvidenceSet.Subset
          (M.cl (EvidenceSet.union A C))
          M.ground :=
      M.cl_ground (EvidenceSet.union A C)
    have hStep :
        M.cl (M.cl (EvidenceSet.union A C)) x :=
      M.monotone hInnerToOriginalClosure hClosureGround hx.1
    exact ⟨M.idempotent hUnionGround hStep, hx.2⟩
  exchange := by
    intro A x y hA hxGround hyGround hInsert hxNot
    have hBaseGround :
        EvidenceSet.Subset (EvidenceSet.union A C) M.ground := by
      intro z hz
      cases hz with
      | inl hAz => exact (hA hAz).1
      | inr hCz => exact hC hCz
    have hInsertedGround :
        EvidenceSet.Subset
          (EvidenceSet.insert y (EvidenceSet.union A C))
          M.ground := by
      intro z hz
      cases hz with
      | inl hzy => simpa [hzy] using hyGround.1
      | inr hzBase => exact hBaseGround hzBase
    have hContractInsertSub :
        EvidenceSet.Subset
          (EvidenceSet.union (EvidenceSet.insert y A) C)
          (EvidenceSet.insert y (EvidenceSet.union A C)) := by
      intro z hz
      cases hz with
      | inl hIns =>
          cases hIns with
          | inl hzy => exact Or.inl hzy
          | inr hAz => exact Or.inr (Or.inl hAz)
      | inr hCz => exact Or.inr (Or.inr hCz)
    have hInsertOriginal :
        M.cl (EvidenceSet.insert y (EvidenceSet.union A C)) x :=
      M.monotone hContractInsertSub hInsertedGround hInsert.1
    have hxNotOriginal : ¬ M.cl (EvidenceSet.union A C) x := by
      intro hxCl
      exact hxNot ⟨hxCl, hxGround.2⟩
    have hExOriginal :
        M.cl (EvidenceSet.insert x (EvidenceSet.union A C)) y :=
      M.exchange hBaseGround hxGround.1 hyGround.1 hInsertOriginal hxNotOriginal
    have hOriginalInsertSub :
        EvidenceSet.Subset
          (EvidenceSet.insert x (EvidenceSet.union A C))
          (EvidenceSet.union (EvidenceSet.insert x A) C) := by
      intro z hz
      cases hz with
      | inl hzx => exact Or.inl (Or.inl hzx)
      | inr hzBase =>
          cases hzBase with
          | inl hAz => exact Or.inl (Or.inr hAz)
          | inr hCz => exact Or.inr hCz
    have hTargetGround :
        EvidenceSet.Subset
          (EvidenceSet.union (EvidenceSet.insert x A) C)
          M.ground := by
      intro z hz
      cases hz with
      | inl hIns =>
          cases hIns with
          | inl hzx => simpa [hzx] using hxGround.1
          | inr hAz => exact (hA hAz).1
      | inr hCz => exact hC hCz
    have hTargetOriginal :
        M.cl (EvidenceSet.union (EvidenceSet.insert x A) C) y :=
      M.monotone hOriginalInsertSub hTargetGround hExOriginal
    exact ⟨hTargetOriginal, hyGround.2⟩

/-- Deletion of a single ground atom. -/
def deleteElem {α : Type u}
    (M : GroundMatroidClosure α)
    (d : α) : GroundMatroidClosure α :=
  M.delete (EvidenceSet.singleton d)

/-- Contraction of a single ground atom. -/
def contractElem {α : Type u}
    (M : GroundMatroidClosure α)
    (c : α)
    (hc : M.ground c) : GroundMatroidClosure α :=
  M.contract (EvidenceSet.singleton c) (by
    intro x hx
    change x = c at hx
    subst x
    exact hc)

/-- A loop is a ground element generated by the empty set. -/
def IsLoop {α : Type u} (M : GroundMatroidClosure α) (e : α) : Prop :=
  M.ground e ∧ M.cl EvidenceSet.empty e

/-- Standard closure characterization of loops after contraction. -/
theorem contract_isLoop_iff_mem_closure
    {α : Type u}
    (M : GroundMatroidClosure α)
    (C : EvidenceSet α)
    (hC : EvidenceSet.Subset C M.ground)
    (e : α) :
    (M.contract C hC).IsLoop e ↔
      M.ground e ∧ ¬ C e ∧ M.cl C e := by
  constructor
  · intro h
    have hGround : M.ground e := h.1.1
    have hNotC : ¬ C e := h.1.2
    have hEmptyUnion :
        EvidenceSet.Subset (EvidenceSet.union EvidenceSet.empty C) C := by
      intro z hz
      cases hz with
      | inl hEmpty => exact False.elim hEmpty
      | inr hCz => exact hCz
    have hClosureC : M.cl C e :=
      M.monotone hEmptyUnion hC h.2.1
    exact ⟨hGround, hNotC, hClosureC⟩
  · intro h
    have hCToEmptyUnion :
        EvidenceSet.Subset C (EvidenceSet.union EvidenceSet.empty C) := by
      intro z hz
      exact Or.inr hz
    have hEmptyUnionGround :
        EvidenceSet.Subset (EvidenceSet.union EvidenceSet.empty C) M.ground := by
      intro z hz
      cases hz with
      | inl hEmpty => exact False.elim hEmpty
      | inr hCz => exact hC hCz
    have hClUnion :
        M.cl (EvidenceSet.union EvidenceSet.empty C) e :=
      M.monotone hCToEmptyUnion hEmptyUnionGround h.2.2
    exact ⟨⟨h.1, h.2.1⟩, ⟨hClUnion, h.2.1⟩⟩

end GroundMatroidClosure

namespace FiniteGroundMatroidClosure

/-- Finite-ground deletion preserves the same finite support certificate. -/
def delete {α : Type u}
    (M : FiniteGroundMatroidClosure α)
    (D : EvidenceSet α) : FiniteGroundMatroidClosure α where
  toGroundMatroidClosure := M.toGroundMatroidClosure.delete D
  support := M.support
  ground_listed := by
    intro x hx
    exact M.ground_listed hx.1

/-- Finite-ground contraction preserves the same finite support certificate. -/
def contract {α : Type u}
    (M : FiniteGroundMatroidClosure α)
    (C : EvidenceSet α)
    (hC : EvidenceSet.Subset C M.ground) : FiniteGroundMatroidClosure α where
  toGroundMatroidClosure := M.toGroundMatroidClosure.contract C hC
  support := M.support
  ground_listed := by
    intro x hx
    exact M.ground_listed hx.1

/-- Finite-ground deletion of one atom. -/
def deleteElem {α : Type u}
    (M : FiniteGroundMatroidClosure α)
    (d : α) : FiniteGroundMatroidClosure α :=
  M.delete (EvidenceSet.singleton d)

/-- Finite-ground contraction of one ground atom. -/
def contractElem {α : Type u}
    (M : FiniteGroundMatroidClosure α)
    (c : α)
    (hc : M.ground c) : FiniteGroundMatroidClosure α :=
  M.contract (EvidenceSet.singleton c) (by
    intro x hx
    change x = c at hx
    subst x
    exact hc)

end FiniteGroundMatroidClosure

/-- Coarse channel closure restricted to an explicit ground set. -/
def channelClosureOn {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (A : EvidenceSet α) : EvidenceSet α :=
  fun e =>
    ground e ∧
      ∃ a, ground a ∧ A a ∧ polarity a = polarity e

/-- A finite carrier certificate for evidence atoms. -/
structure FiniteEvidenceGround (α : Type u) where
  carrier : EvidenceSet α
  support : List α
  carrier_listed : ∀ {x}, carrier x → x ∈ support

/--
The finite coarse positive/negative channel structure is a genuine explicit-ground
matroid closure.
-/
def finiteChannelMatroid {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity) : FiniteGroundMatroidClosure α where
  ground := G.carrier
  cl := channelClosureOn G.carrier polarity
  cl_ground := by
    intro A x hx
    exact hx.1
  extensive := by
    intro A hA x hx
    exact ⟨hA hx, ⟨x, hA hx, hx, rfl⟩⟩
  monotone := by
    intro A B hAB hBGround x hx
    cases hx.2 with
    | intro a ha =>
        exact ⟨hx.1, ⟨a, ha.1, hAB ha.2.1, ha.2.2⟩⟩
  idempotent := by
    intro A hA x hx
    cases hx.2 with
    | intro a ha =>
        have hInner := ha.2.1
        cases hInner.2 with
        | intro b hb =>
            exact ⟨hx.1, ⟨b, hb.1, hb.2.1, Eq.trans hb.2.2 ha.2.2⟩⟩
  exchange := by
    intro A x y hA hxGround hyGround hInsert hxNot
    cases hInsert.2 with
    | intro a ha =>
        cases ha.2.1 with
        | inl hay =>
            have hPolYX : polarity y = polarity x := by
              simpa [hay] using ha.2.2
            exact ⟨hyGround, ⟨x, hxGround, Or.inl rfl, hPolYX.symm⟩⟩
        | inr hAa =>
            exact False.elim (hxNot ⟨hxGround, ⟨a, ha.1, hAa, ha.2.2⟩⟩)
  support := G.support
  ground_listed := G.carrier_listed

/-- Singleton closure in the explicit-ground channel matroid. -/
theorem channelClosureOn_singleton_iff
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (c e : α) :
    channelClosureOn ground polarity (EvidenceSet.singleton c) e ↔
      ground e ∧ ground c ∧ polarity c = polarity e := by
  constructor
  · intro h
    cases h.2 with
    | intro a ha =>
        have hac : a = c := ha.2.1
        subst a
        exact ⟨h.1, ha.1, ha.2.2⟩
  · intro h
    exact ⟨h.1, ⟨c, h.2.1, rfl, h.2.2⟩⟩

/--
Contracting one channel atom makes exactly its remaining same-polarity partners
loops in the contracted channel matroid.
-/
theorem finiteChannel_contractElem_isLoop_iff
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c e : α)
    (hc : G.carrier c) :
    GroundMatroidClosure.IsLoop
      ((finiteChannelMatroid G polarity).contractElem c hc).toGroundMatroidClosure e ↔
      G.carrier e ∧ e ≠ c ∧ polarity c = polarity e := by
  have hGeneric :=
    GroundMatroidClosure.contract_isLoop_iff_mem_closure
      (finiteChannelMatroid G polarity).toGroundMatroidClosure
      (EvidenceSet.singleton c)
      (by
        intro x hx
        change x = c at hx
        subst x
        exact hc)
      e
  constructor
  · intro h
    have hData := hGeneric.1 h
    have hClosure :=
      (channelClosureOn_singleton_iff G.carrier polarity c e).1 hData.2.2
    exact ⟨hData.1, by
      intro hec
      exact hData.2.1 hec, hClosure.2.2⟩
  · intro h
    apply hGeneric.2
    exact ⟨h.1, by
      intro hec
      exact h.2.1 hec, (channelClosureOn_singleton_iff G.carrier polarity c e).2
        ⟨h.1, hc, h.2.2⟩⟩

/-- Support of one polarity by a ground set. -/
def supportsGroundChannel {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (channel : EvidencePolarity) : Prop :=
  ∃ e, ground e ∧ polarity e = channel

/-- A chosen atom is the unique ground representative of its polarity. -/
def UniqueChannelRepresentative {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (c : α) : Prop :=
  ground c ∧
  ∀ e, ground e → polarity e = polarity c → e = c

/-- Deleting one member of a same-polarity pair preserves every coarse support bit. -/
theorem supportsChannel_delete_parallel_iff
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    {x y : α}
    (hy : ground y)
    (hxy : x ≠ y)
    (hpol : polarity x = polarity y)
    (channel : EvidencePolarity) :
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
        by_cases hex : e = x
        · subst e
          exact ⟨y, ⟨hy, by
            intro hyx
            exact hxy hyx.symm⟩, Eq.trans hpol.symm he.2⟩
        · exact ⟨e, ⟨he.1, hex⟩, he.2⟩

/-- Deleting one member of a coarse circuit preserves the realized FDE value. -/
theorem realizesFDE_delete_parallel_iff
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    {x y : α}
    (hy : ground y)
    (hxy : x ≠ y)
    (hpol : polarity x = polarity y)
    (v : FDEValue) :
    RealizesFDE polarity
        (EvidenceSet.diff ground (EvidenceSet.singleton x)) v ↔
      RealizesFDE polarity ground v := by
  have hPos :=
    supportsChannel_delete_parallel_iff ground polarity hy hxy hpol
      EvidencePolarity.positive
  have hNeg :=
    supportsChannel_delete_parallel_iff ground polarity hy hxy hpol
      EvidencePolarity.negative
  constructor
  · intro h
    constructor
    · constructor
      · intro hv
        exact hPos.1 (h.1.1 hv)
      · intro hs
        exact h.1.2 (hPos.2 hs)
    · constructor
      · intro hv
        exact hNeg.1 (h.2.1 hv)
      · intro hs
        exact h.2.2 (hNeg.2 hs)
  · intro h
    constructor
    · constructor
      · intro hv
        exact hPos.2 (h.1.1 hv)
      · intro hs
        exact h.1.2 (hPos.1 hs)
    · constructor
      · intro hv
        exact hNeg.2 (h.2.1 hv)
      · intro hs
        exact h.2.2 (hNeg.1 hs)

/-- Deleting a unique representative removes that polarity from the remaining ground. -/
theorem delete_unique_channel_not_supported
    {α : Type u}
    (ground : EvidenceSet α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hUnique : UniqueChannelRepresentative ground polarity c) :
    ¬ supportsGroundChannel
      (EvidenceSet.diff ground (EvidenceSet.singleton c))
      polarity (polarity c) := by
  intro h
  cases h with
  | intro e he =>
      have hec : e = c := hUnique.2 e he.1.1 he.2
      exact he.1.2 hec

/-- Genuine contraction removes the contracted atom itself from the minor ground set. -/
theorem contractElem_excludes_contracted_atom
    {α : Type u}
    (M : GroundMatroidClosure α)
    (c : α)
    (hc : M.ground c) :
    ¬ (M.contractElem c hc).ground c := by
  intro h
  exact h.2 rfl

/--
If the contracted atom was the unique representative of its polarity, the contracted
ground no longer carries that polarity.  This marks the boundary between structural
contraction and an epistemic state update that remembers accepted background evidence.
-/
theorem finiteChannel_contract_unique_channel_not_supported
    {α : Type u}
    (G : FiniteEvidenceGround α)
    (polarity : α → EvidencePolarity)
    (c : α)
    (hUnique : UniqueChannelRepresentative G.carrier polarity c) :
    ¬ supportsGroundChannel
      ((finiteChannelMatroid G polarity).contractElem c hUnique.1).ground
      polarity (polarity c) := by
  intro h
  cases h with
  | intro e he =>
      have heGround : G.carrier e := he.1.1
      have heNotC : e ≠ c := by
        intro hec
        exact he.1.2 hec
      have hec : e = c := hUnique.2 e heGround he.2
      exact heNotC hec

end PEL4
