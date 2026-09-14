import PEL4.ActiveContradictionResolution

namespace PEL4

/-!
# Gate 78: model uncertainty witness

Gate 77 assumed that the resolving sensor model was known. Gate 78 opens the
second-order uncertainty problem: the same probe can be excellent under one
sensor model and misleading under another.
-/

inductive Gate78SensorModel where
  | reliable
  | degraded
  deriving DecidableEq, Repr

inductive Gate78Probe where
  | fragile
  | safe
  deriving DecidableEq, Repr

/-- Decision value of a probe under a candidate sensor model. -/
def gate78ProbeValue (model : Gate78SensorModel) (probe : Gate78Probe) : Rat :=
  match model, probe with
  | .reliable, .fragile => (9 : Rat) / 10
  | .degraded, .fragile => (1 : Rat) / 10
  | _, .safe => (3 : Rat) / 5

/-- Under the trusted model the high-ceiling fragile probe wins. -/
theorem gate78_reliable_prefers_fragile :
    gate78ProbeValue .reliable .fragile > gate78ProbeValue .reliable .safe := by
  native_decide

/-- Under the degraded model the same probe loses to the safe probe. -/
theorem gate78_degraded_prefers_safe :
    gate78ProbeValue .degraded .fragile < gate78ProbeValue .degraded .safe := by
  native_decide

/-- Main Gate-78 theorem: uncertainty about the observation model can reverse
an experiment ranking even when the hidden-world question is unchanged. -/
theorem gate78_model_uncertainty_reverses_ranking :
    gate78ProbeValue .reliable .fragile > gate78ProbeValue .reliable .safe ∧
    gate78ProbeValue .degraded .fragile < gate78ProbeValue .degraded .safe := by
  exact ⟨gate78_reliable_prefers_fragile, gate78_degraded_prefers_safe⟩

/-!
## Gate-78 boundary

This is a finite two-model witness, not yet a probability distribution over
models. It establishes the structural problem needed by later robust-control
gates: a policy optimal under one assumed sensor law need not remain optimal
when that law itself is uncertain.
-/

end PEL4
