import PEL4.JevBridgeFalsification

namespace PEL4

/-!
# Gate J3: preregistered empirical JevBridge contract

J1 established the mathematical bridge and J2 established a deterministic
falsification harness. J3 deliberately does not prove an empirical result in
Lean. Instead it freezes the acceptance contract that a real Jev run must meet
before the integration is described as empirically useful.

The corresponding Python runner joins blinded API outputs with the frozen labels
only during evaluation. A later result gate may import a generated certificate.
-/

structure JevJ3Metrics where
  tCount : Nat
  fCount : Nat
  bCount : Nat
  nCount : Nat
  overallAccuracy : Rat
  bnAccuracy : Rat
  bnFalseCertainty : Rat
  paraphraseStabilityMean : Rat
  paraphraseStabilityMin : Rat
  bnSeparation4 : Rat
  bnSeparationScalar : Rat
  deriving Repr

def gateJ3RequiredPerClass : Nat := 25
def gateJ3MinOverallAccuracy : Rat := (9 : Rat) / 10
def gateJ3MinBNAccuracy : Rat := (9 : Rat) / 10
def gateJ3MaxBNFalseCertainty : Rat := (1 : Rat) / 20
def gateJ3MinParaphraseStabilityMean : Rat := (9 : Rat) / 10
def gateJ3MinParaphraseStabilityMin : Rat := (4 : Rat) / 5

/-- Preregistered J3 acceptance criterion.

The last inequality is deliberately comparative rather than absolute:
four-valued B/N separation must exceed the scalar Noul baseline on the same
states. -/
def gateJ3Accepted (m : JevJ3Metrics) : Prop :=
  gateJ3RequiredPerClass ≤ m.tCount ∧
  gateJ3RequiredPerClass ≤ m.fCount ∧
  gateJ3RequiredPerClass ≤ m.bCount ∧
  gateJ3RequiredPerClass ≤ m.nCount ∧
  gateJ3MinOverallAccuracy ≤ m.overallAccuracy ∧
  gateJ3MinBNAccuracy ≤ m.bnAccuracy ∧
  m.bnFalseCertainty ≤ gateJ3MaxBNFalseCertainty ∧
  gateJ3MinParaphraseStabilityMean ≤ m.paraphraseStabilityMean ∧
  gateJ3MinParaphraseStabilityMin ≤ m.paraphraseStabilityMin ∧
  m.bnSeparationScalar < m.bnSeparation4

/-- A J3 acceptance certificate necessarily includes a strict empirical
advantage over the scalar B/N separation baseline. -/
theorem gateJ3_acceptance_requires_bn_separation_advantage
    (m : JevJ3Metrics)
    (h : gateJ3Accepted m) :
    m.bnSeparationScalar < m.bnSeparation4 := by
  exact h.2.2.2.2.2.2.2.2.2

/-- The empirical claim cannot be obtained from the J1/J2 fixture alone:
an explicit J3 metrics witness is required. -/
theorem gateJ3_acceptance_requires_bn_accuracy
    (m : JevJ3Metrics)
    (h : gateJ3Accepted m) :
    gateJ3MinBNAccuracy ≤ m.bnAccuracy := by
  exact h.2.2.2.2.2.1

end PEL4
