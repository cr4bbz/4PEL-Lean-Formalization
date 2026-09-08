import PEL4.MatroidEvidence
import PEL4.TopologicalEvidenceFixedPoints

namespace PEL4

/-!
# Gate 2: the topological boundary of matroidal evidence

The topological evidence development and the coarse matroidal evidence layer
both use closure operators, but they impose different structure. Topological
closure preserves finite unions; matroid closure adds the Mac Lane--Steinitz
exchange condition.

For a topological closure the finite-union law makes exchange local: it is
completely determined by singleton closures. In an ordinary topological space,
`x ∈ closure {y}` is the specialization relation. Hence the symmetry condition
below is the algebraic form of the R0 separation property.
-/

/-- Empty predicate-presented evidence region. -/
def emptyEvidenceSet {W : Type} : EvidenceSet W :=
  fun _ => False

/-- `insert` is exactly union with a singleton in the topological region presentation. -/
theorem evidenceSet_insert_eq_regionUnion_singleton
    {W : Type} (x : W) (A : EvidenceSet W) :
    EvidenceSet.insert x A = regionUnion (EvidenceSet.singleton x) A := by
  rfl

/-- Singleton-closure specialization relation induced by the topological semantics. -/
def topologicalSpecializes {W : Type}
    (s : InteriorSemantics W) (x y : W) : Prop :=
  s.closure (EvidenceSet.singleton y) x

/--
R0-like symmetry stated without importing a separate point-set-topology layer.
For genuine topological spaces this is symmetry of the specialization preorder.
-/
def TopologicalR0Like {W : Type} (s : InteriorSemantics W) : Prop :=
  ∀ x y, topologicalSpecializes s x y → topologicalSpecializes s y x

/-- Exchange for the topological closure, in the same orientation as `MatroidClosure.exchange`. -/
def TopologicalClosureExchange {W : Type} (s : InteriorSemantics W) : Prop :=
  ∀ {A : EvidenceSet W} {x y : W},
    s.closure (EvidenceSet.insert y A) x →
    ¬ s.closure A x →
    s.closure (EvidenceSet.insert x A) y

/-- The closure of the empty region is empty. -/
theorem closure_empty_not_mem
    {W : Type} (s : InteriorSemantics W) (w : W) :
    ¬ s.closure (emptyEvidenceSet : EvidenceSet W) w := by
  intro hClosure
  apply hClosure
  have hCompl :
      regionCompl (emptyEvidenceSet : EvidenceRegion W) =
        (fun _ => True) := by
    funext u
    apply propext
    simp [regionCompl, emptyEvidenceSet]
  rw [hCompl]
  exact s.interior_top w

/--
Topological exchange is equivalent to symmetry of singleton specialization.

The forward implication applies exchange over the empty base. The reverse
implication uses finite-union preservation to show that any genuinely new point
introduced by inserting `y` must already lie in `closure {y}`.
-/
theorem topologicalClosureExchange_iff_r0Like
    {W : Type} (s : InteriorSemantics W) :
    TopologicalClosureExchange s ↔ TopologicalR0Like s := by
  classical
  constructor
  · intro hExchange x y hxy
    have hInsert :
        s.closure (EvidenceSet.insert y emptyEvidenceSet) x := by
      rw [evidenceSet_insert_eq_regionUnion_singleton]
      exact (closure_union_at s (EvidenceSet.singleton y) emptyEvidenceSet x).2
        (Or.inl hxy)
    have hResult := hExchange hInsert (closure_empty_not_mem s x)
    rw [evidenceSet_insert_eq_regionUnion_singleton] at hResult
    have hSplit :=
      (closure_union_at s (EvidenceSet.singleton x) emptyEvidenceSet y).1
        hResult
    cases hSplit with
    | inl hSingleton =>
        exact hSingleton
    | inr hEmpty =>
        exact False.elim ((closure_empty_not_mem s y) hEmpty)
  · intro hR0 A x y hInsert hx
    rw [evidenceSet_insert_eq_regionUnion_singleton] at hInsert
    have hSplit :=
      (closure_union_at s (EvidenceSet.singleton y) A x).1 hInsert
    cases hSplit with
    | inl hSingleton =>
        have hReverse : s.closure (EvidenceSet.singleton x) y :=
          hR0 x y hSingleton
        have hUnionReverse :
            s.closure (regionUnion (EvidenceSet.singleton x) A) y :=
          (closure_union_at s (EvidenceSet.singleton x) A y).2
            (Or.inl hReverse)
        rw [← evidenceSet_insert_eq_regionUnion_singleton] at hUnionReverse
        exact hUnionReverse
    | inr hA =>
        exact False.elim (hx hA)

/-- An R0-like topological closure therefore yields the repository's closure-form matroid. -/
def topologicalMatroidClosure
    {W : Type} (s : InteriorSemantics W)
    (hR0 : TopologicalR0Like s) : MatroidClosure W where
  cl := s.closure
  extensive := by
    intro A x hx
    exact closure_superset s A x hx
  monotone := by
    intro A B hAB x hx
    exact closure_monotone s hAB x hx
  idempotent := by
    intro A x hx
    exact (closure_idempotent_at s A x).1 hx
  exchange := by
    intro A x y hxy hx
    exact (topologicalClosureExchange_iff_r0Like s).2 hR0 hxy hx

/-!
## The Gate-1 channel matroid is topological

The positive/negative coarse partition from Gate 1 has a canonical partition
interior: a point is interior to `A` exactly when its whole polarity class lies
inside `A`. The dual closure is exactly `channelClosure`.
-/

/-- Interior generated by the two polarity equivalence classes. -/
def channelInterior {α : Type}
    (polarity : α → EvidencePolarity)
    (A : EvidenceRegion α) : EvidenceRegion α :=
  fun e => ∀ a, polarity a = polarity e → A a

/-- The polarity partition defines an `InteriorSemantics`. -/
def channelInteriorSemantics {α : Type}
    (polarity : α → EvidencePolarity) : InteriorSemantics α where
  interior := channelInterior polarity
  interior_subset := by
    intro A e h
    exact h e rfl
  interior_monotone := by
    intro A B hAB e hInterior a ha
    exact hAB a (hInterior a ha)
  interior_idempotent := by
    intro A e
    constructor
    · intro h a hae
      exact (h a hae) a rfl
    · intro h a hae b hba
      exact h b (Eq.trans hba hae)
  interior_top := by
    intro e a ha
    exact True.intro
  interior_intersection := by
    intro A B e
    constructor
    · intro h
      constructor
      · intro a ha
        exact (h a ha).1
      · intro a ha
        exact (h a ha).2
    · rintro ⟨hA, hB⟩ a ha
      exact ⟨hA a ha, hB a ha⟩

/-- The topological closure of the polarity-partition topology is exactly Gate 1's channel closure. -/
theorem channelInteriorSemantics_closure_iff_channelClosure
    {α : Type} (polarity : α → EvidencePolarity)
    (A : EvidenceSet α) (e : α) :
    (channelInteriorSemantics polarity).closure A e ↔
      channelClosure polarity A e := by
  classical
  change (¬ ∀ a, polarity a = polarity e → ¬ A a) ↔
    ∃ a, A a ∧ polarity a = polarity e
  constructor
  · intro hNotAll
    by_cases hWitness : ∃ a, A a ∧ polarity a = polarity e
    · exact hWitness
    · exact False.elim (hNotAll (by
        intro a ha hA
        exact hWitness ⟨a, hA, ha⟩))
  · intro hWitness hAll
    cases hWitness with
    | intro a ha =>
        exact hAll a ha.2 ha.1

/-- Singleton specialization in the channel topology is symmetric. -/
theorem channelInteriorSemantics_r0Like
    {α : Type} (polarity : α → EvidencePolarity) :
    TopologicalR0Like (channelInteriorSemantics polarity) := by
  intro x y hxy
  have hxyChannel :
      channelClosure polarity (EvidenceSet.singleton y) x :=
    (channelInteriorSemantics_closure_iff_channelClosure
      polarity (EvidenceSet.singleton y) x).1 hxy
  have hPol : polarity y = polarity x :=
    (samePolarity_iff_mem_singletonClosure polarity y x).1 hxyChannel
  have hyxChannel :
      channelClosure polarity (EvidenceSet.singleton x) y :=
    (samePolarity_iff_mem_singletonClosure polarity x y).2 hPol.symm
  exact (channelInteriorSemantics_closure_iff_channelClosure
    polarity (EvidenceSet.singleton x) y).2 hyxChannel

/-- Gate 1's coarse channel topology satisfies exchange. -/
theorem channelInteriorSemantics_exchange
    {α : Type} (polarity : α → EvidencePolarity) :
    TopologicalClosureExchange (channelInteriorSemantics polarity) :=
  (topologicalClosureExchange_iff_r0Like
    (channelInteriorSemantics polarity)).2
      (channelInteriorSemantics_r0Like polarity)

end PEL4
