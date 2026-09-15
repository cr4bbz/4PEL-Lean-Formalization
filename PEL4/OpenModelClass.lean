import PEL4.SelfCorrectingPolicy

namespace PEL4

/-!
# Gate 97: open model class

A self-correcting agent must be able to represent the possibility that neither of
its familiar models is right. Gate 97 adds an explicit omitted balanced model and
shows that expanding the hypothesis class can turn universal misfit into an exact
fit.
-/

inductive Gate97OpenModel where
  | low
  | high
  | balancedUnknown
  deriving DecidableEq, Repr

def gate97PredictedPositive : Gate97OpenModel → Rat
  | .low => (1 : Rat) / 10
  | .high => (9 : Rat) / 10
  | .balancedUnknown => (1 : Rat) / 2

def gate97ObservedPositive : Rat := (1 : Rat) / 2

def gate97SquaredDiscrepancy (model : Gate97OpenModel) : Rat :=
  let d := gate97ObservedPositive - gate97PredictedPositive model
  d * d

def gate97Tolerance : Rat := (1 : Rat) / 10

def gate97Fits (model : Gate97OpenModel) : Bool :=
  gate97SquaredDiscrepancy model ≤ gate97Tolerance

theorem gate97_old_models_miss :
    gate97SquaredDiscrepancy .low = (4 : Rat) / 25 ∧
    gate97SquaredDiscrepancy .high = (4 : Rat) / 25 ∧
    gate97Fits .low = false ∧
    gate97Fits .high = false := by
  native_decide

/-- The omitted balanced hypothesis explains the observation exactly. -/
theorem gate97_unknown_model_exact_fit :
    gate97SquaredDiscrepancy .balancedUnknown = 0 ∧
    gate97Fits .balancedUnknown = true := by
  native_decide

/-- The expanded model class therefore contains an empirically adequate member. -/
theorem gate97_expansion_repairs_adequacy :
    gate97Fits .low = false ∧
    gate97Fits .high = false ∧
    gate97Fits .balancedUnknown = true := by
  native_decide

/-- Main Gate-97 theorem: model-class expansion can explain evidence that every
member of the original closed class misses. -/
theorem gate97_open_model_class_witness :
    gate97SquaredDiscrepancy .low > gate97Tolerance ∧
    gate97SquaredDiscrepancy .high > gate97Tolerance ∧
    gate97SquaredDiscrepancy .balancedUnknown = 0 ∧
    gate97Fits .balancedUnknown = true := by
  native_decide

/-!
## Boundary

The new model is supplied explicitly. Gate 97 establishes representational value
of an open class; it does not solve automatic model discovery.
-/

end PEL4
