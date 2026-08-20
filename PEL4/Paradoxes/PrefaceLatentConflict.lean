import Std.Tactic.Omega
import PEL4.FDE
import PEL4.Evidence

namespace PEL4.Paradoxes

/-!
# Latent conflict carrier theorem

For a conjunction to be glutty in FDE, every conjunct must have positive
support while at least one conjunct has negative support. Therefore at least
one conjunct is itself glutty at that world.

This pointwise fact combines with the strict-majority overlap bound to show:
if belief in a conjunction is globally B at threshold k/m, then at least
2k-m of the probability mass must lie on worlds carrying a local glut in one
or more conjuncts. The local gluts need not themselves cross the belief
threshold.
-/

/-- Three-conjunct FDE conjunction, matching the Preface control cases. -/
def and3 (v1 v2 v3 : FDEValue) : FDEValue :=
  FDEValue.and v1 (FDEValue.and v2 v3)

/-- A world carries latent local conflict when at least one conjunct is B. -/
def someLocalGlut3 (v1 v2 v3 : FDEValue) : Bool :=
  isGlut v1 || isGlut v2 || isGlut v3

/-- A glut in the conjunction cannot appear from nowhere: at least one local
conjunct is glutty in the same world. -/
theorem and3_glut_implies_some_local_glut
    (v1 v2 v3 : FDEValue)
    (h : isGlut (and3 v1 v2 v3) = true) :
    someLocalGlut3 v1 v2 v3 = true := by
  cases v1 with
  | mk p1 n1 =>
    cases p1 <;> cases n1 <;>
    cases v2 with
    | mk p2 n2 =>
      cases p2 <;> cases n2 <;>
      cases v3 with
      | mk p3 n3 =>
        cases p3 <;> cases n3 <;>
        simp [and3, someLocalGlut3, FDEValue.and, isGlut] at h ⊢

/-- One finite epistemic world, recording the three Preface conjuncts. -/
structure SignedPrefaceTriple where
  p1 : FDEValue
  p2 : FDEValue
  p3 : FDEValue

namespace SignedPrefaceTriple

def joint (w : SignedPrefaceTriple) : FDEValue := and3 w.p1 w.p2 w.p3

def jointPositive (w : SignedPrefaceTriple) : Bool := (joint w).pos
def jointNegative (w : SignedPrefaceTriple) : Bool := (joint w).neg
def jointGlut (w : SignedPrefaceTriple) : Bool := isGlut (joint w)
def localCarrier (w : SignedPrefaceTriple) : Bool := someLocalGlut3 w.p1 w.p2 w.p3

def p1Glut (w : SignedPrefaceTriple) : Bool := isGlut w.p1
def p2Glut (w : SignedPrefaceTriple) : Bool := isGlut w.p2
def p3Glut (w : SignedPrefaceTriple) : Bool := isGlut w.p3

/-- Pointwise carrier inclusion. -/
theorem jointGlut_implies_localCarrier
    (w : SignedPrefaceTriple)
    (h : jointGlut w = true) :
    localCarrier w = true :=
  and3_glut_implies_some_local_glut w.p1 w.p2 w.p3 h

end SignedPrefaceTriple

/-- Count worlds satisfying a Boolean predicate. -/
def countWhere {α : Type} (p : α → Bool) : List α → Nat
| [] => 0
| x :: xs => (if p x then 1 else 0) + countWhere p xs

/-- Pointwise implication of predicates yields an inequality between their
finite counts. -/
theorem countWhere_mono {α : Type}
    (p q : α → Bool)
    (himp : ∀ x, p x = true → q x = true)
    (xs : List α) :
    countWhere p xs ≤ countWhere q xs := by
  induction xs with
  | nil => simp [countWhere]
  | cons x xs ih =>
      simp [countWhere]
      by_cases hp : p x = true
      · have hq := himp x hp
        simp [hp, hq]
        exact ih
      · have hpfalse : p x = false := by
          cases hx : p x <;> simp_all
        simp [hpfalse]
        omega

/-- The conjunction-glut mass is bounded by the mass of worlds carrying at
least one local glut. -/
theorem joint_glut_count_le_local_carrier
    (ws : List SignedPrefaceTriple) :
    countWhere SignedPrefaceTriple.jointGlut ws ≤
      countWhere SignedPrefaceTriple.localCarrier ws := by
  apply countWhere_mono
  intro w hw
  exact SignedPrefaceTriple.jointGlut_implies_localCarrier w hw

/-- For every world, positive and negative conjunction indicators can jointly
contribute two only when that world is itself a conjunction glut. -/
theorem joint_indicator_bound (w : SignedPrefaceTriple) :
    (if SignedPrefaceTriple.jointPositive w then 1 else 0) +
      (if SignedPrefaceTriple.jointNegative w then 1 else 0) ≤
    1 + (if SignedPrefaceTriple.jointGlut w then 1 else 0) := by
  cases hpos : SignedPrefaceTriple.jointPositive w <;>
  cases hneg : SignedPrefaceTriple.jointNegative w <;>
  simp [hpos, hneg, SignedPrefaceTriple.jointGlut,
    SignedPrefaceTriple.jointPositive, SignedPrefaceTriple.jointNegative,
    isGlut]

/-- Finite inclusion-exclusion bound for the conjunction evidence counts. -/
theorem joint_pos_neg_count_bound (ws : List SignedPrefaceTriple) :
    countWhere SignedPrefaceTriple.jointPositive ws +
      countWhere SignedPrefaceTriple.jointNegative ws ≤
    ws.length + countWhere SignedPrefaceTriple.jointGlut ws := by
  induction ws with
  | nil => simp [countWhere]
  | cons w ws ih =>
      simp [countWhere]
      have hw := joint_indicator_bound w
      omega

/--
Latent Conflict Carrier Theorem, three-claim form.

If the conjunction crosses both the positive and negative thresholds k in a
uniform finite model of m worlds, then the mass of worlds carrying at least one
local glut satisfies the conflict budget 2k ≤ m + carrier.

Normalized, carrier/m ≥ 2(k/m)-1.
-/
theorem latent_conflict_carrier_bound
    (ws : List SignedPrefaceTriple)
    (m k : Nat)
    (hlen : ws.length = m)
    (hpos : k ≤ countWhere SignedPrefaceTriple.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceTriple.jointNegative ws) :
    2 * k ≤ m + countWhere SignedPrefaceTriple.localCarrier ws := by
  have hpn := joint_pos_neg_count_bound ws
  have hcarrier := joint_glut_count_le_local_carrier ws
  omega

/-- At a strict-majority threshold, global B for the conjunction forces a
non-empty local conflict carrier, even though no local belief need be B. -/
theorem strict_majority_global_glut_has_local_carrier
    (ws : List SignedPrefaceTriple)
    (m k : Nat)
    (hlen : ws.length = m)
    (hmajority : m < 2 * k)
    (hpos : k ≤ countWhere SignedPrefaceTriple.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceTriple.jointNegative ws) :
    0 < countWhere SignedPrefaceTriple.localCarrier ws := by
  have hbound := latent_conflict_carrier_bound ws m k hlen hpos hneg
  omega

/-- A carrier world contributes at least one unit to the sum of the three
local glut indicators. -/
theorem local_carrier_indicator_le_glut_sum (w : SignedPrefaceTriple) :
    (if SignedPrefaceTriple.localCarrier w then 1 else 0) ≤
      (if SignedPrefaceTriple.p1Glut w then 1 else 0) +
      (if SignedPrefaceTriple.p2Glut w then 1 else 0) +
      (if SignedPrefaceTriple.p3Glut w then 1 else 0) := by
  cases h1 : SignedPrefaceTriple.p1Glut w <;>
  cases h2 : SignedPrefaceTriple.p2Glut w <;>
  cases h3 : SignedPrefaceTriple.p3Glut w <;>
  simp [SignedPrefaceTriple.localCarrier, someLocalGlut3,
    SignedPrefaceTriple.p1Glut, SignedPrefaceTriple.p2Glut,
    SignedPrefaceTriple.p3Glut, h1, h2, h3]

/-- The union mass of local conflict carriers is bounded by the sum of the
individual local glut masses. -/
theorem local_carrier_count_le_glut_sum (ws : List SignedPrefaceTriple) :
    countWhere SignedPrefaceTriple.localCarrier ws ≤
      countWhere SignedPrefaceTriple.p1Glut ws +
      countWhere SignedPrefaceTriple.p2Glut ws +
      countWhere SignedPrefaceTriple.p3Glut ws := by
  induction ws with
  | nil => simp [countWhere]
  | cons w ws ih =>
      simp [countWhere]
      have hw := local_carrier_indicator_le_glut_sum w
      omega

/--
Local Glut Budget Corollary.

Global B for the conjunction forces the summed local object-level glut mass to
pay at least the same strict-majority conflict budget. Normalized:

  P_B(p1) + P_B(p2) + P_B(p3) ≥ 2c - 1.
-/
theorem local_glut_sum_budget
    (ws : List SignedPrefaceTriple)
    (m k : Nat)
    (hlen : ws.length = m)
    (hpos : k ≤ countWhere SignedPrefaceTriple.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceTriple.jointNegative ws) :
    2 * k ≤ m +
      countWhere SignedPrefaceTriple.p1Glut ws +
      countWhere SignedPrefaceTriple.p2Glut ws +
      countWhere SignedPrefaceTriple.p3Glut ws := by
  have hcarrier := latent_conflict_carrier_bound ws m k hlen hpos hneg
  have hsum := local_carrier_count_le_glut_sum ws
  omega

/--
Three-way pigeonhole consequence.

At least one proposition must individually carry one third of the required
latent conflict budget (up to integer rounding). In normalized notation, for
some i:

  P_B(pi) ≥ (2c - 1) / 3.
-/
theorem some_local_glut_carries_third_budget
    (ws : List SignedPrefaceTriple)
    (m k : Nat)
    (hlen : ws.length = m)
    (hpos : k ≤ countWhere SignedPrefaceTriple.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceTriple.jointNegative ws) :
    (2 * k ≤ m + 3 * countWhere SignedPrefaceTriple.p1Glut ws) ∨
    (2 * k ≤ m + 3 * countWhere SignedPrefaceTriple.p2Glut ws) ∨
    (2 * k ≤ m + 3 * countWhere SignedPrefaceTriple.p3Glut ws) := by
  have hsum := local_glut_sum_budget ws m k hlen hpos hneg
  omega

end PEL4.Paradoxes
