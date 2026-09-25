import PEL4.JevBridge

namespace PEL4

/-!
# Gate J2: JevBridge falsification panel

J2 is intentionally adversarial. It establishes a deterministic control panel
for the four expected epistemic regimes and exhibits a concrete information
loss under a one-dimensional scalar collapse.

Passing this file proves that the bridge can represent the target distinctions.
It does NOT constitute empirical evidence that real Jev outputs make those
distinctions. The companion Python harness is the empirical gate.
-/

def gateJ2Threshold : Rat := (3 : Rat) / 4

def gateJ2True : JevFDEDistribution where
  t := (4 : Rat) / 5
  f := (1 : Rat) / 20
  b := (1 : Rat) / 10
  n := (1 : Rat) / 20
  t_nonnegative := by native_decide
  f_nonnegative := by native_decide
  b_nonnegative := by native_decide
  n_nonnegative := by native_decide
  total := by native_decide

def gateJ2False : JevFDEDistribution where
  t := (1 : Rat) / 20
  f := (4 : Rat) / 5
  b := (1 : Rat) / 10
  n := (1 : Rat) / 20
  t_nonnegative := by native_decide
  f_nonnegative := by native_decide
  b_nonnegative := by native_decide
  n_nonnegative := by native_decide
  total := by native_decide

def gateJ2Glut : JevFDEDistribution where
  t := (1 : Rat) / 10
  f := (1 : Rat) / 10
  b := (7 : Rat) / 10
  n := (1 : Rat) / 10
  t_nonnegative := by native_decide
  f_nonnegative := by native_decide
  b_nonnegative := by native_decide
  n_nonnegative := by native_decide
  total := by native_decide

def gateJ2Gap : JevFDEDistribution where
  t := (1 : Rat) / 10
  f := (1 : Rat) / 10
  b := (1 : Rat) / 10
  n := (7 : Rat) / 10
  t_nonnegative := by native_decide
  f_nonnegative := by native_decide
  b_nonnegative := by native_decide
  n_nonnegative := by native_decide
  total := by native_decide

/-- All four controlled regimes project to the intended FDE cell. -/
theorem gateJ2_control_panel :
    jevProject gateJ2True gateJ2Threshold = FDEValue.T ∧
    jevProject gateJ2False gateJ2Threshold = FDEValue.F ∧
    jevProject gateJ2Glut gateJ2Threshold = FDEValue.B ∧
    jevProject gateJ2Gap gateJ2Threshold = FDEValue.N := by
  native_decide

/-- A deliberately lossy binary scalar: positive support relative to all
positive-or-negative support. It erases support magnitude. -/
def jevScalarBalance (d : JevFDEDistribution) : Rat :=
  jevPosMass d / (jevPosMass d + jevNegMass d)

/-- The controlled glut and gap become exactly indistinguishable under this
one-dimensional collapse, despite remaining distinct under the 4PEL bridge. -/
theorem gateJ2_scalar_aliases_glut_and_gap :
    jevScalarBalance gateJ2Glut = (1 : Rat) / 2 ∧
    jevScalarBalance gateJ2Gap = (1 : Rat) / 2 := by
  native_decide

theorem gateJ2_bridge_separates_scalar_alias :
    jevScalarBalance gateJ2Glut = jevScalarBalance gateJ2Gap ∧
    jevProject gateJ2Glut gateJ2Threshold ≠
      jevProject gateJ2Gap gateJ2Threshold := by
  constructor
  · native_decide
  · native_decide

/-- Controlled evidence intervention path:
gap -> positive support -> contradiction -> negative support. -/
def gateJ2InterventionPath : List FDEValue :=
  [ jevProject gateJ2Gap gateJ2Threshold
  , jevProject gateJ2True gateJ2Threshold
  , jevProject gateJ2Glut gateJ2Threshold
  , jevProject gateJ2False gateJ2Threshold ]

theorem gateJ2_intervention_path :
    gateJ2InterventionPath =
      [FDEValue.N, FDEValue.T, FDEValue.B, FDEValue.F] := by
  native_decide

/-- Formal acceptance bundle for J2. This is only the deterministic control
panel; empirical acceptance is delegated to the external harness. -/
theorem gateJ2_formal_acceptance :
    (jevProject gateJ2True gateJ2Threshold = FDEValue.T ∧
      jevProject gateJ2False gateJ2Threshold = FDEValue.F ∧
      jevProject gateJ2Glut gateJ2Threshold = FDEValue.B ∧
      jevProject gateJ2Gap gateJ2Threshold = FDEValue.N) ∧
    (jevScalarBalance gateJ2Glut = jevScalarBalance gateJ2Gap) ∧
    (jevProject gateJ2Glut gateJ2Threshold ≠
      jevProject gateJ2Gap gateJ2Threshold) ∧
    gateJ2InterventionPath =
      [FDEValue.N, FDEValue.T, FDEValue.B, FDEValue.F] := by
  exact ⟨gateJ2_control_panel,
    gateJ2_bridge_separates_scalar_alias.1,
    gateJ2_bridge_separates_scalar_alias.2,
    gateJ2_intervention_path⟩

#eval! gateJ2InterventionPath

/-!
## Gate J2 boundary

A successful Lean build verifies only structural capacity and the designed
counterexample to scalar collapse. Empirical success requires real Jev outputs
on pre-labelled T/F/B/N cases. The external harness therefore distinguishes
fixture mode from real-data mode and refuses to call fixture data an empirical
pass.
-/

end PEL4
