import Std.Tactic.Omega
import PEL4.Paradoxes.PrefaceLatentConflict

namespace PEL4.Paradoxes

/-!
# N-claim latent conflict descent

This module generalizes the strongest P3a result from three conjuncts to an
arbitrary finite conjunction. The key fact is purely FDE-structural:
if a finite conjunction is B at a world, then at least one conjunct is B at
that same world.
-/

/-- Finite conjunction with T as the empty identity. -/
def andList : List FDEValue → FDEValue
| [] => FDEValue.T
| v :: vs => FDEValue.and v (andList vs)

/-- Whether at least one conjunct is object-level B. -/
def anyLocalGlut : List FDEValue → Bool
| [] => false
| v :: vs => isGlut v || anyLocalGlut vs

/-- Binary descent: a glut in a conjunction must be inherited from at least one
side, because conjunction positivity requires both positive supports while
conjunction negativity requires negative support on at least one side. -/
theorem and_glut_implies_left_or_right_glut
    (v w : FDEValue)
    (h : isGlut (FDEValue.and v w) = true) :
    isGlut v = true ∨ isGlut w = true := by
  cases v with
  | mk vp vn =>
    cases vp <;> cases vn <;>
    cases w with
    | mk wp wn =>
      cases wp <;> cases wn <;>
      simp [FDEValue.and, isGlut] at h ⊢

/-- Arbitrary finite descent of conjunction glut into a local conjunct. -/
theorem andList_glut_implies_anyLocalGlut :
    ∀ vs : List FDEValue,
      isGlut (andList vs) = true → anyLocalGlut vs = true
| [] => by
    simp [andList, anyLocalGlut, isGlut, FDEValue.T]
| v :: vs => by
    intro h
    have hsplit := and_glut_implies_left_or_right_glut v (andList vs) h
    rcases hsplit with hv | htail
    · simp [anyLocalGlut, hv]
    · have ih := andList_glut_implies_anyLocalGlut vs htail
      simp [anyLocalGlut, ih]

/-- One epistemic world with an arbitrary finite vector of conjunct values. -/
structure SignedPrefaceNWorld where
  values : List FDEValue

namespace SignedPrefaceNWorld

def joint (w : SignedPrefaceNWorld) : FDEValue := andList w.values

def jointPositive (w : SignedPrefaceNWorld) : Bool := (joint w).pos
def jointNegative (w : SignedPrefaceNWorld) : Bool := (joint w).neg
def jointGlut (w : SignedPrefaceNWorld) : Bool := isGlut (joint w)
def localCarrier (w : SignedPrefaceNWorld) : Bool := anyLocalGlut w.values

/-- Pointwise n-claim carrier inclusion. -/
theorem jointGlut_implies_localCarrier
    (w : SignedPrefaceNWorld)
    (h : jointGlut w = true) :
    localCarrier w = true :=
  andList_glut_implies_anyLocalGlut w.values h

end SignedPrefaceNWorld

/-- N-claim conjunction-glut mass is bounded by the local carrier mass. -/
theorem joint_glut_count_le_local_carrier_n
    (ws : List SignedPrefaceNWorld) :
    countWhere SignedPrefaceNWorld.jointGlut ws ≤
      countWhere SignedPrefaceNWorld.localCarrier ws := by
  apply countWhere_mono
  intro w hw
  exact SignedPrefaceNWorld.jointGlut_implies_localCarrier w hw

/-- Per-world inclusion-exclusion bound for arbitrary finite conjunctions. -/
theorem joint_indicator_bound_n (w : SignedPrefaceNWorld) :
    (if SignedPrefaceNWorld.jointPositive w then 1 else 0) +
      (if SignedPrefaceNWorld.jointNegative w then 1 else 0) ≤
    1 + (if SignedPrefaceNWorld.jointGlut w then 1 else 0) := by
  cases hpos : SignedPrefaceNWorld.jointPositive w <;>
  cases hneg : SignedPrefaceNWorld.jointNegative w <;>
  simp [hpos, hneg, SignedPrefaceNWorld.jointGlut,
    SignedPrefaceNWorld.jointPositive, SignedPrefaceNWorld.jointNegative,
    isGlut]

/-- Finite positive/negative overlap bound for arbitrary finite conjunctions. -/
theorem joint_pos_neg_count_bound_n (ws : List SignedPrefaceNWorld) :
    countWhere SignedPrefaceNWorld.jointPositive ws +
      countWhere SignedPrefaceNWorld.jointNegative ws ≤
    ws.length + countWhere SignedPrefaceNWorld.jointGlut ws := by
  induction ws with
  | nil => simp [countWhere]
  | cons w ws ih =>
      simp [countWhere]
      have hw := joint_indicator_bound_n w
      omega

/--
N-Claim Latent Conflict Carrier Theorem.

For any finite conjunction length, if its positive and negative supports both
cross threshold k in a uniform model of m worlds, then:

  2k ≤ m + localCarrier.

Normalized:

  P(exists i : pi = B) ≥ 2c - 1.

The lower bound is independent of the number of conjuncts.
-/
theorem latent_conflict_carrier_bound_n
    (ws : List SignedPrefaceNWorld)
    (m k : Nat)
    (hlen : ws.length = m)
    (hpos : k ≤ countWhere SignedPrefaceNWorld.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceNWorld.jointNegative ws) :
    2 * k ≤ m + countWhere SignedPrefaceNWorld.localCarrier ws := by
  have hpn := joint_pos_neg_count_bound_n ws
  have hcarrier := joint_glut_count_le_local_carrier_n ws
  omega

/-- At any strict-majority threshold, an n-claim global conjunction glut
requires a nonempty local object-level conflict carrier. -/
theorem strict_majority_global_glut_has_local_carrier_n
    (ws : List SignedPrefaceNWorld)
    (m k : Nat)
    (hlen : ws.length = m)
    (hmajority : m < 2 * k)
    (hpos : k ≤ countWhere SignedPrefaceNWorld.jointPositive ws)
    (hneg : k ≤ countWhere SignedPrefaceNWorld.jointNegative ws) :
    0 < countWhere SignedPrefaceNWorld.localCarrier ws := by
  have hbound := latent_conflict_carrier_bound_n ws m k hlen hpos hneg
  omega

end PEL4.Paradoxes
