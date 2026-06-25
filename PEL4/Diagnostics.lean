import PEL4.Syntax
import PEL4.Evidence

namespace PEL4

/-!
Object-level diagnostics for four-valued evidence states.

The existing object language remains unchanged.  Diagnostics are a lightweight
extension layer that lets Lean inspect whether an already evaluated formula is
glutty, gappy, consistent, contradictory, determined, or undetermined.
-/

inductive Diagnostic where
  | glut
  | gap
  | consistent
  | contradictory
  | determined
  | undetermined
deriving DecidableEq, Repr

def diagnose (d : Diagnostic) (v : FDEValue) : Bool :=
  match d with
  | Diagnostic.glut => isGlut v
  | Diagnostic.gap => isGap v
  | Diagnostic.consistent => isConsistent v
  | Diagnostic.contradictory => isContradictory v
  | Diagnostic.determined => isDetermined v
  | Diagnostic.undetermined => isGap v

def diagnosticValue (d : Diagnostic) (v : FDEValue) : FDEValue :=
  FDEValue.ofBool (diagnose d v)

inductive DiagnosticFormula (Atom Ag : Type) where
  | base : Formula Atom Ag -> DiagnosticFormula Atom Ag
  | check : Diagnostic -> Formula Atom Ag -> DiagnosticFormula Atom Ag

def evalDiagnosticFormula {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) : DiagnosticFormula Atom Ag -> FDEValue
  | DiagnosticFormula.base phi => eval m w phi
  | DiagnosticFormula.check d phi => diagnosticValue d (eval m w phi)

#eval! diagnose Diagnostic.glut FDEValue.B
#eval! diagnose Diagnostic.gap FDEValue.N
#eval! diagnosticValue Diagnostic.consistent FDEValue.B

end PEL4
