import PEL4.PopulationAxiology.FourCellKernel
import PEL4.ConvexProbabilitySimplex
import PEL4.ReliableEvidence

namespace PEL4.ModalProbability

open PopulationAxiology

/-!
# MPFG-1: conservative reliability refinement

This is a probability/refinement layer, NOT a six-valued truth-functional logic.
The six cells split T and F into untagged and reliability-tagged evidence.
The tags are supplied data, not proofs of real-world truth. In particular this
module does not implement the LET_K+ connectives or classicality calculus.
The existing unrestricted `EvidenceStatus` has more than six possibilities;
the embedding below selects six particular statuses without changing that type.
-/

inductive EvidenceCell where
  | t | b | n | f | reliableT | reliableF
  deriving DecidableEq, Repr

def EvidenceCell.raw : EvidenceCell → FDEValue
  | .t | .reliableT => .T
  | .b => .B
  | .n => .N
  | .f | .reliableF => .F

def EvidenceCell.toEvidenceStatus (s : EvidenceCell) : EvidenceStatus :=
  { raw := s.raw
    reliablePos := decide (s = .reliableT)
    reliableNeg := decide (s = .reliableF) }

theorem evidenceStatus_raw (s : EvidenceCell) :
    s.toEvidenceStatus.raw = s.raw := rfl

/-- Six nonnegative rational cell masses, with normalization grouped by the
four coarse cells. This is a rational simplex, not a new truth-value algebra. -/
structure SixCellProbability where
  t : Rat
  b : Rat
  n : Rat
  f : Rat
  reliableT : Rat
  reliableF : Rat
  t_nonnegative : 0 ≤ t
  b_nonnegative : 0 ≤ b
  n_nonnegative : 0 ≤ n
  f_nonnegative : 0 ≤ f
  reliableT_nonnegative : 0 ≤ reliableT
  reliableF_nonnegative : 0 ≤ reliableF
  normalized : (t + reliableT) + b + n + (f + reliableF) = 1

namespace SixCellProbability

/-- Forget reliability tags by summing within each coarse fibre. -/
def coarse (p : SixCellProbability) : FourCellProbability :=
  { t := p.t + p.reliableT, b := p.b, n := p.n, f := p.f + p.reliableF
    t_nonnegative := Rat.add_nonneg p.t_nonnegative p.reliableT_nonnegative
    b_nonnegative := p.b_nonnegative
    n_nonnegative := p.n_nonnegative
    f_nonnegative := Rat.add_nonneg p.f_nonnegative p.reliableF_nonnegative
    normalized := p.normalized }

/-- A canonical section: add no reliability assertions to a coarse profile. -/
def untagged (p : FourCellProbability) : SixCellProbability :=
  { t := p.t, b := p.b, n := p.n, f := p.f, reliableT := 0, reliableF := 0
    t_nonnegative := p.t_nonnegative
    b_nonnegative := p.b_nonnegative
    n_nonnegative := p.n_nonnegative
    f_nonnegative := p.f_nonnegative
    reliableT_nonnegative := by decide
    reliableF_nonnegative := by decide
    normalized := by simpa only [Rat.add_zero] using p.normalized }

theorem coarse_untagged (p : FourCellProbability) :
    (untagged p).coarse = p := by
  cases p
  simp [untagged, coarse, Rat.add_zero]

def positive (p : SixCellProbability) : Rat := (p.t + p.reliableT) + p.b
def negative (p : SixCellProbability) : Rat := (p.f + p.reliableF) + p.b

def thresholdValue (c : Rat) (p : SixCellProbability) : FDEValue :=
  supportThresholdState c p.positive p.negative

theorem coarse_positive (p : SixCellProbability) :
    p.coarse.positive = p.positive := rfl

theorem coarse_negative (p : SixCellProbability) :
    p.coarse.negative = p.negative := rfl

/-- Raw threshold belief cannot observe a redistribution inside a fibre. -/
theorem threshold_coarse (c : Rat) (p : SixCellProbability) :
    p.coarse.thresholdValue c = p.thresholdValue c := rfl

theorem same_coarse_same_belief (c : Rat) (p q : SixCellProbability)
    (h : p.coarse = q.coarse) : p.thresholdValue c = q.thresholdValue c :=
  congrArg (FourCellProbability.thresholdValue c) h

/-- Probability of belonging to a reliability-tagged cell; not itself a
classicality operator or an empirical calibration guarantee. -/
def reliableMass (p : SixCellProbability) : Rat := p.reliableT + p.reliableF

def pureT : SixCellProbability :=
  { t := 1, b := 0, n := 0, f := 0, reliableT := 0, reliableF := 0
    t_nonnegative := by decide
    b_nonnegative := by decide
    n_nonnegative := by decide
    f_nonnegative := by decide
    reliableT_nonnegative := by decide
    reliableF_nonnegative := by decide
    normalized := by decide }

def pureReliableT : SixCellProbability :=
  { t := 0, b := 0, n := 0, f := 0, reliableT := 1, reliableF := 0
    t_nonnegative := by decide
    b_nonnegative := by decide
    n_nonnegative := by decide
    f_nonnegative := by decide
    reliableT_nonnegative := by decide
    reliableF_nonnegative := by decide
    normalized := by decide }

theorem reliability_not_determined_by_coarse :
    pureT.coarse = pureReliableT.coarse ∧
    pureT.reliableMass = 0 ∧ pureReliableT.reliableMass = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem no_reliability_reconstruction :
    ¬ ∃ recover : FourCellProbability → Rat,
      ∀ p : SixCellProbability, recover p.coarse = p.reliableMass := by
  rintro ⟨recover, h⟩
  have h0 := h pureT
  have h1 := h pureReliableT
  rw [← reliability_not_determined_by_coarse.1] at h1
  have bad : (0 : Rat) = 1 := h0.symm.trans h1
  exact (by decide : (0 : Rat) ≠ 1) bad

end SixCellProbability

/-- Rational convex combination used for both simplexes. -/
def mix (a x y : Rat) : Rat := (1 - a) * x + a * y

theorem mix_nonnegative (a x y : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ mix a x y :=
  convexWeight_nonnegative a (fun _ : Unit => x) (fun _ => y)
    ha0 ha1 () hx hy

theorem mix_add (a x y z v : Rat) :
    mix a x y + mix a z v = mix a (x + z) (y + v) := by
  simp only [mix, Rat.mul_add]
  simp only [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem mix_one (a : Rat) : mix a 1 1 = 1 := by
  simp only [mix, Rat.mul_one]
  exact Rat.sub_add_cancel

def mixFour (a : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : FourCellProbability) : FourCellProbability :=
  { t := mix a p.t q.t, b := mix a p.b q.b
    n := mix a p.n q.n, f := mix a p.f q.f
    t_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.t_nonnegative q.t_nonnegative
    b_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.b_nonnegative q.b_nonnegative
    n_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.n_nonnegative q.n_nonnegative
    f_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.f_nonnegative q.f_nonnegative
    normalized := by rw [mix_add, mix_add, mix_add, p.normalized, q.normalized, mix_one] }

def mixSix (a : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : SixCellProbability) : SixCellProbability :=
  { t := mix a p.t q.t, b := mix a p.b q.b
    n := mix a p.n q.n, f := mix a p.f q.f
    reliableT := mix a p.reliableT q.reliableT
    reliableF := mix a p.reliableF q.reliableF
    t_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.t_nonnegative q.t_nonnegative
    b_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.b_nonnegative q.b_nonnegative
    n_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.n_nonnegative q.n_nonnegative
    f_nonnegative := mix_nonnegative a _ _ ha0 ha1 p.f_nonnegative q.f_nonnegative
    reliableT_nonnegative := mix_nonnegative a _ _ ha0 ha1
      p.reliableT_nonnegative q.reliableT_nonnegative
    reliableF_nonnegative := mix_nonnegative a _ _ ha0 ha1
      p.reliableF_nonnegative q.reliableF_nonnegative
    normalized := by
      rw [mix_add, mix_add, mix_add, mix_add, mix_add,
        p.normalized, q.normalized, mix_one] }

/-- The projection from the rational six-simplex to the four-simplex is affine. -/
theorem coarse_mix (a : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : SixCellProbability) :
    (mixSix a ha0 ha1 p q).coarse = mixFour a ha0 ha1 p.coarse q.coarse := by
  simp only [mixSix, mixFour, SixCellProbability.coarse, mix_add]

/-- Belief commutes with forgetting after mixing. This does NOT say that
thresholding itself is affine. -/
theorem mixture_belief_commutes (a c : Rat) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : SixCellProbability) :
    (mixSix a ha0 ha1 p q).thresholdValue c =
      (mixFour a ha0 ha1 p.coarse q.coarse).thresholdValue c := by
  rw [← SixCellProbability.threshold_coarse, coarse_mix]

end PEL4.ModalProbability
