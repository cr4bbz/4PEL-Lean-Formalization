import PEL4.ProductUpdate
import PEL4.RegenerativeRecoveryBudget

namespace PEL4

/-!
# Gate 35: Growing Ontology / Product Update

Gate 34 allows Recovery resource to be regenerated, but leaves the source of
that resource abstract. Gate 35 connects the accounting theory to a concrete
structural effect already present in 4PEL Product Update: the world type changes
from `W` to `W × Act`, and the surviving product worlds are obtained by
filtering the Cartesian product by positive event preconditions.

The gate deliberately separates three claims:

1. Product Update has a finite geometric capacity bounded by
   `|W| * |Act|`.
2. The number of genuinely surviving product states can exceed the number of
   prior worlds; this is ontology growth.
3. Recovery regeneration is *not identified* with ontology growth. Instead we
   prove a bridge theorem: whenever a Recovery path's regeneration is funded by
   a proved Product-Update growth budget, Gate 34 yields the corresponding
   Recovery-flip bound.

This keeps the result independent of the still-prototypical `product_mu`
implementation. Only the verified finite product/filter geometry is used.
-/

/-- Exact length of the list-level Cartesian product used by Product Update. -/
theorem gate35_listProduct_length {A B : Type}
    (la : List A) (lb : List B) :
    (listProduct la lb).length = la.length * lb.length := by
  induction la with
  | nil => simp [listProduct]
  | cons a rest ih =>
      simp [listProduct, ih, Nat.add_mul]

/-- Filtering a Boolean list predicate never creates new list entries. -/
theorem gate35_filter_length_le {A : Type}
    (xs : List A) (p : A -> Bool) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      cases hp : p x with
      | false =>
          simpa [List.filter, hp] using
            (Nat.le_trans ih (Nat.le_succ rest.length))
      | true =>
          simpa [List.filter, hp] using Nat.succ_le_succ ih

/-- Number of worlds that actually survive a 4PEL Product Update. -/
def productWorldCount {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Nat :=
  (filterProductWorlds m a).length

/-- Maximum number of world-event pairs before precondition filtering. -/
def productWorldCapacity {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Nat :=
  m.worlds.length * a.events.length

/-- Product Update cannot contain more surviving states than the full Cartesian
product from which it is filtered. -/
theorem productWorldCount_le_capacity {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) :
    productWorldCount m a ≤ productWorldCapacity m a := by
  calc
    productWorldCount m a
        ≤ (listProduct m.worlds a.events).length := by
          unfold productWorldCount filterProductWorlds
          exact gate35_filter_length_le _ _
    _ = productWorldCapacity m a := by
          simp [productWorldCapacity, gate35_listProduct_length]

/-- Net increase in represented worlds produced by one Product Update. Natural
subtraction deliberately records zero when the update contracts the ontology. -/
def productOntologyGrowth {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Nat :=
  productWorldCount m a - m.worlds.length

/-- Net ontology growth is bounded by the raw Product-Update capacity. -/
theorem productOntologyGrowth_le_capacity {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) :
    productOntologyGrowth m a ≤ productWorldCapacity m a := by
  unfold productOntologyGrowth
  exact Nat.le_trans (Nat.sub_le _ _) (productWorldCount_le_capacity m a)

/-- Structural condition saying that every raw world-event pair survives the
4-valued precondition filter. This is intentionally stated extensionally, so the
Gate-35 counting theorems remain independent of probability axioms. -/
def ProductUpdateKeepsAllPairs {W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Prop :=
  filterProductWorlds m a = listProduct m.worlds a.events

/-- If all raw pairs survive, the Product Update attains the full Cartesian
capacity exactly. -/
theorem productWorldCount_eq_capacity_of_keepsAllPairs
    {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hAll : ProductUpdateKeepsAllPairs m a) :
    productWorldCount m a = productWorldCapacity m a := by
  unfold ProductUpdateKeepsAllPairs at hAll
  unfold productWorldCount productWorldCapacity
  rw [hAll, gate35_listProduct_length]

/-- Sharp minimal growth schema: one prior world and two surviving events create
exactly one net new represented state. -/
theorem productOntologyGrowth_eq_one_of_singleton_twoEvents
    {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hAll : ProductUpdateKeepsAllPairs m a)
    (hWorlds : m.worlds.length = 1)
    (hEvents : a.events.length = 2) :
    productOntologyGrowth m a = 1 := by
  have hCount := productWorldCount_eq_capacity_of_keepsAllPairs m a hAll
  unfold productOntologyGrowth
  rw [hCount]
  simp [productWorldCapacity, hWorlds, hEvents]

/-- A Recovery path is Product-growth funded when its total Gate-34
regeneration does not exceed the net ontology growth supplied by one Product
Update. This is the explicit bridge assumption; ontology growth and Recovery
resource are not definitionally identified. -/
def ProductGrowthFundsRecoveryPath
    {State W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State)
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Prop :=
  recoveryRegenerationTotalFrom sys start successors ≤
    productOntologyGrowth m a

/-- Gate 34 with a concrete Product-Update growth cap. -/
theorem recoveryRegenerative_changeCount_le_initial_add_productGrowth
    {State W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State)
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hFollows : recoveryRegenerativeFollows sys start successors)
    (hFunded : ProductGrowthFundsRecoveryPath sys start successors m a) :
    recoveryRegenerativeChangeCountFrom sys start successors ≤
      sys.potential start + productOntologyGrowth m a := by
  exact recoveryRegenerative_changeCount_le_initial_add_budget
    sys start successors (productOntologyGrowth m a) hFollows hFunded

/-- A coarser but assumption-light bound: every Product-growth-funded Recovery
path is bounded by initial potential plus the full raw world-event capacity. -/
theorem recoveryRegenerative_changeCount_le_initial_add_productCapacity
    {State W Act Ag Atom : Type}
    [DecidableEq W] [DecidableEq Act]
    (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State)
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hFollows : recoveryRegenerativeFollows sys start successors)
    (hFunded : ProductGrowthFundsRecoveryPath sys start successors m a) :
    recoveryRegenerativeChangeCountFrom sys start successors ≤
      sys.potential start + productWorldCapacity m a := by
  have hGrowth := recoveryRegenerative_changeCount_le_initial_add_productGrowth
    sys start successors m a hFollows hFunded
  exact Nat.le_trans hGrowth
    (Nat.add_le_add_left (productOntologyGrowth_le_capacity m a) _)

/-! ## Sharp one-unit Product-growth witness for the budget bridge -/

inductive Gate35RecoveryState where
  | before
  | after
  deriving DecidableEq, Repr

/-- One unit of regenerated resource funds one Recovery-status change. The
following theorems identify that one unit with the exact ontology growth of the
singleton/two-event Product-Update schema above. -/
def gate35GrowthFundedSystem : RecoveryRegenerativeSystem Gate35RecoveryState where
  status
    | .before => true
    | .after => false
  potential := fun _ => 0
  regeneration s t :=
    if s = .before ∧ t = .after then 1 else 0
  Step := fun s t => s = .before ∧ t = .after
  step_budget := by
    intro s t hStep
    rcases hStep with ⟨rfl, rfl⟩
    decide

 theorem gate35_growth_path_follows :
    recoveryRegenerativeFollows gate35GrowthFundedSystem
      Gate35RecoveryState.before [Gate35RecoveryState.after] := by
  simp [recoveryRegenerativeFollows, gate35GrowthFundedSystem]

 theorem gate35_growth_path_changeCount_is_one :
    recoveryRegenerativeChangeCountFrom gate35GrowthFundedSystem
      Gate35RecoveryState.before [Gate35RecoveryState.after] = 1 := by
  decide +kernel

 theorem gate35_growth_path_regeneration_is_one :
    recoveryRegenerationTotalFrom gate35GrowthFundedSystem
      Gate35RecoveryState.before [Gate35RecoveryState.after] = 1 := by
  decide +kernel

/-- In the minimal growing-ontology schema, the exact Product-Update growth,
the exact regenerated resource, and the exact Recovery-change count all equal
one. This demonstrates compatibility, not identity, between ontology growth and
Recovery regeneration. -/
theorem gate35_singleton_twoEvent_growth_exactly_funds_one_flip
    {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hAll : ProductUpdateKeepsAllPairs m a)
    (hWorlds : m.worlds.length = 1)
    (hEvents : a.events.length = 2) :
    recoveryRegenerationTotalFrom gate35GrowthFundedSystem
          Gate35RecoveryState.before [Gate35RecoveryState.after] =
        productOntologyGrowth m a ∧
      recoveryRegenerativeChangeCountFrom gate35GrowthFundedSystem
          Gate35RecoveryState.before [Gate35RecoveryState.after] =
        productOntologyGrowth m a := by
  have hGrowth := productOntologyGrowth_eq_one_of_singleton_twoEvents
    m a hAll hWorlds hEvents
  constructor
  · rw [gate35_growth_path_regeneration_is_one, hGrowth]
  · rw [gate35_growth_path_changeCount_is_one, hGrowth]

/-- The Gate-34/Product-Growth bound is sharp on the minimal schema:
`1 = 0 + 1`. -/
theorem gate35_productGrowth_bound_is_sharp
    {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
    (m : Model W Ag Atom) (a : ActionModel Act Ag Atom)
    (hAll : ProductUpdateKeepsAllPairs m a)
    (hWorlds : m.worlds.length = 1)
    (hEvents : a.events.length = 2) :
    recoveryRegenerativeChangeCountFrom gate35GrowthFundedSystem
        Gate35RecoveryState.before [Gate35RecoveryState.after] =
      gate35GrowthFundedSystem.potential Gate35RecoveryState.before +
        productOntologyGrowth m a := by
  have hGrowth := productOntologyGrowth_eq_one_of_singleton_twoEvents
    m a hAll hWorlds hEvents
  rw [gate35_growth_path_changeCount_is_one, hGrowth]
  decide

/-- Pure capacity envelope for a sequence of ontology-expanding stages. The
heterogeneous world types of repeated Product Updates are intentionally erased
here to cardinalities; a later gate can package type-changing update chains. -/
def iteratedProductCapacity : Nat -> List Nat -> Nat
  | worlds, [] => worlds
  | worlds, events :: rest => iteratedProductCapacity (worlds * events) rest

/-- Three binary event expansions can raise a one-world capacity to eight. -/
theorem gate35_three_binary_expansions_capacity :
    iteratedProductCapacity 1 [2, 2, 2] = 8 := by
  decide

end PEL4
