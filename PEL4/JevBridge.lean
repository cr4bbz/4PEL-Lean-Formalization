import PEL4.ProbabilisticEvidence
import PEL4.WeightGeneratedProbability
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Gate J1: Jev -> 4PEL semantic bridge

This gate deliberately separates a model-produced categorical distribution from
4PEL's own probability semantics.

A Jev-style four-way classifier is represented only after it satisfies the
finite simplex contract: nonnegative masses on T/F/B/N with total mass one.
From that distribution, 4PEL derives positive and negative evidence masses by

  P+ = pT + pB
  P- = pF + pB.

The Lockean threshold is applied only after this interpretation step.

The gate also constructs a canonical four-world 4PEL model realizing the
distribution as finite world weights. This proves representability, not that the
model's internal probabilities are semantically identical to Jev's uncertainty.
-/

/-- Validated four-way Jev output. The fields are intentionally named after the
four FDE cells rather than 4PEL world probabilities. -/
structure JevFDEDistribution where
  t : Rat
  f : Rat
  b : Rat
  n : Rat
  t_nonnegative : 0 ≤ t
  f_nonnegative : 0 ≤ f
  b_nonnegative : 0 ≤ b
  n_nonnegative : 0 ≤ n
  total : t + f + b + n = 1

/-- Positive-evidence mass induced by a four-way Jev distribution. -/
def jevPosMass (d : JevFDEDistribution) : Rat :=
  d.t + d.b

/-- Negative-evidence mass induced by a four-way Jev distribution. -/
def jevNegMass (d : JevFDEDistribution) : Rat :=
  d.f + d.b

/-- Glut mass is the classifier mass assigned to the B cell. -/
def jevGlutMass (d : JevFDEDistribution) : Rat :=
  d.b

/-- Gap mass is the classifier mass assigned to the N cell. -/
def jevGapMass (d : JevFDEDistribution) : Rat :=
  d.n

/-- Fundamental four-cell balance identity.

Equivalent to P+ + P- = 1 + PB - PN, but stated without subtraction so that the
proof depends only on associativity, commutativity, and normalization. -/
theorem jev_mass_balance (d : JevFDEDistribution) :
    jevPosMass d + jevNegMass d + jevGapMass d =
      1 + jevGlutMass d := by
  unfold jevPosMass jevNegMass jevGapMass jevGlutMass
  calc
    (d.t + d.b) + (d.f + d.b) + d.n =
        (d.t + d.f + d.b + d.n) + d.b := by
          ac_rfl
    _ = 1 + d.b := by rw [d.total]

/-- 4PEL interprets the Jev distribution through independent Lockean thresholds.
Jev supplies masses; 4PEL supplies the epistemic projection. -/
def jevProject (d : JevFDEDistribution) (c : Rat) : FDEValue :=
  { pos := decide (c ≤ jevPosMass d)
    neg := decide (c ≤ jevNegMass d) }

theorem jevProject_eq_T_of
    (d : JevFDEDistribution) (c : Rat)
    (hPos : c ≤ jevPosMass d)
    (hNeg : ¬ c ≤ jevNegMass d) :
    jevProject d c = FDEValue.T := by
  simp [jevProject, FDEValue.T, hPos, hNeg]

theorem jevProject_eq_F_of
    (d : JevFDEDistribution) (c : Rat)
    (hPos : ¬ c ≤ jevPosMass d)
    (hNeg : c ≤ jevNegMass d) :
    jevProject d c = FDEValue.F := by
  simp [jevProject, FDEValue.F, hPos, hNeg]

theorem jevProject_eq_B_of
    (d : JevFDEDistribution) (c : Rat)
    (hPos : c ≤ jevPosMass d)
    (hNeg : c ≤ jevNegMass d) :
    jevProject d c = FDEValue.B := by
  simp [jevProject, FDEValue.B, hPos, hNeg]

theorem jevProject_eq_N_of
    (d : JevFDEDistribution) (c : Rat)
    (hPos : ¬ c ≤ jevPosMass d)
    (hNeg : ¬ c ≤ jevNegMass d) :
    jevProject d c = FDEValue.N := by
  simp [jevProject, FDEValue.N, hPos, hNeg]

/-! ## Canonical four-world realization -/

/-- One canonical world for each FDE cell. -/
inductive JevCell where
  | t
  | f
  | b
  | n
  deriving DecidableEq, Repr

def jevSupport : FiniteSet JevCell :=
  [.t, .f, .b, .n]

def jevWeight (d : JevFDEDistribution) : JevCell → Rat
  | .t => d.t
  | .f => d.f
  | .b => d.b
  | .n => d.n

theorem jevSupport_nodup :
    jevSupport.Nodup := by
  native_decide

theorem jevWeight_nonnegative
    (d : JevFDEDistribution) :
    ∀ x, x ∈ jevSupport → 0 ≤ jevWeight d x := by
  intro x _
  cases x with
  | t => exact d.t_nonnegative
  | f => exact d.f_nonnegative
  | b => exact d.b_nonnegative
  | n => exact d.n_nonnegative

theorem jevWeight_total
    (d : JevFDEDistribution) :
    weightedEventMass jevSupport (jevWeight d) jevSupport = 1 := by
  simpa [jevSupport, jevWeight, weightedEventMass, Rat.add_assoc] using d.total

theorem jevWeight_is_distribution
    (d : JevFDEDistribution) :
    FiniteWeightDistribution jevSupport (jevWeight d) := by
  exact
    { support_nodup := jevSupport_nodup
      nonnegative := jevWeight_nonnegative d
      total := jevWeight_total d }

/-- Canonical finite measure realizing the four classifier cells as world
weights. -/
def jevCanonicalMeasure (d : JevFDEDistribution) : ProbMeasure JevCell :=
  weightGeneratedMeasure jevSupport (jevWeight d)

theorem jevCanonicalMeasure_integrity
    (d : JevFDEDistribution) :
    FiniteProbabilityIntegrity (jevCanonicalMeasure d) jevSupport := by
  exact weightGeneratedMeasure_integrity
    jevSupport (jevWeight d) (jevWeight_is_distribution d)

def jevPositiveEvent : FiniteSet JevCell := [.t, .b]
def jevNegativeEvent : FiniteSet JevCell := [.f, .b]
def jevGlutEvent : FiniteSet JevCell := [.b]
def jevGapEvent : FiniteSet JevCell := [.n]

theorem jevCanonical_positive_mass
    (d : JevFDEDistribution) :
    jevCanonicalMeasure d jevPositiveEvent = jevPosMass d := by
  simp [jevCanonicalMeasure, weightGeneratedMeasure, weightedEventMass,
    jevSupport, jevWeight, jevPositiveEvent, jevPosMass]

theorem jevCanonical_negative_mass
    (d : JevFDEDistribution) :
    jevCanonicalMeasure d jevNegativeEvent = jevNegMass d := by
  simp [jevCanonicalMeasure, weightGeneratedMeasure, weightedEventMass,
    jevSupport, jevWeight, jevNegativeEvent, jevNegMass]

theorem jevCanonical_glut_mass
    (d : JevFDEDistribution) :
    jevCanonicalMeasure d jevGlutEvent = jevGlutMass d := by
  simp [jevCanonicalMeasure, weightGeneratedMeasure, weightedEventMass,
    jevSupport, jevWeight, jevGlutEvent, jevGlutMass]

theorem jevCanonical_gap_mass
    (d : JevFDEDistribution) :
    jevCanonicalMeasure d jevGapEvent = jevGapMass d := by
  simp [jevCanonicalMeasure, weightGeneratedMeasure, weightedEventMass,
    jevSupport, jevWeight, jevGapEvent, jevGapMass]

def jevCellValue : JevCell → FDEValue
  | .t => FDEValue.T
  | .f => FDEValue.F
  | .b => FDEValue.B
  | .n => FDEValue.N

/-- A complete canonical 4PEL model whose accessible-world weights realize the
validated four-way distribution. The threshold is fixed to 3/4 only to satisfy
the existing model contract; callers may still use any threshold with
`jevProject`. -/
def jevCanonicalModel (d : JevFDEDistribution) :
    Model JevCell Unit Unit where
  worlds := jevSupport
  R := fun _ _ => jevSupport
  mu := fun _ _ => jevCanonicalMeasure d
  val := fun w _ => jevCellValue w
  c := fun _ => (3 : Rat) / 4
  mu_total := by
    intro _ _
    exact jevWeight_total d
  mu_empty := by
    intro _ _
    exact weightedEventMass_empty jevSupport (jevWeight d)
  c_gt_half := by
    intro _
    native_decide
  c_le_one := by
    intro _
    native_decide

/-- Gate J1 acceptance theorem: every validated Jev four-cell distribution has
an integrity-certified canonical finite realization preserving all four masses. -/
theorem gateJ1_canonical_realization
    (d : JevFDEDistribution) :
    FiniteProbabilityIntegrity (jevCanonicalMeasure d) jevSupport ∧
    jevCanonicalMeasure d jevPositiveEvent = jevPosMass d ∧
    jevCanonicalMeasure d jevNegativeEvent = jevNegMass d ∧
    jevCanonicalMeasure d jevGlutEvent = jevGlutMass d ∧
    jevCanonicalMeasure d jevGapEvent = jevGapMass d := by
  exact ⟨jevCanonicalMeasure_integrity d,
    jevCanonical_positive_mass d,
    jevCanonical_negative_mass d,
    jevCanonical_glut_mass d,
    jevCanonical_gap_mass d⟩

/-!
## Gate J1 boundary

This gate proves representability and preservation of the four-cell algebra.
It does not identify Jev's classifier uncertainty with an objective or
agent-relative 4PEL world measure. That stronger identification requires an
additional semantic/calibration hypothesis and is intentionally left open.
-/

end PEL4
