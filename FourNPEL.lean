import Mathlib.Tactic.Linarith

/-!
# 4-NPEL: 4-Valued Neighborhood Probabilistic Epistemic Logic
Standalone Formalization based on PMF and Computable Validity.
-/

namespace FourNPEL

/-- 4-valued state as a bi-dimensional boolean pair (Positive Support, Negative Support). -/
structure Val4 where
  pos : Bool
  neg : Bool
  deriving Repr, DecidableEq

namespace Val4

def T : Val4 := ⟨true, false⟩
def B : Val4 := ⟨true, true⟩
def N : Val4 := ⟨false, false⟩
def F : Val4 := ⟨false, true⟩

/-- Logical AND (Minimum) -/
def and (a b : Val4) : Val4 := ⟨a.pos && b.pos, a.neg || b.neg⟩

/-- Logical OR (Maximum) -/
def or (a b : Val4) : Val4 := ⟨a.pos || b.pos, a.neg && b.neg⟩

/-- Logical NOT (Inversion) -/
def not (a : Val4) : Val4 := ⟨a.neg, a.pos⟩

end Val4

infixl:65 " ⊓ " => Val4.and
infixl:60 " ⊔ " => Val4.or
prefix:75 "∼" => Val4.not

/-- Finite Probability Mass Function over the 4 ontological regions. -/
structure Model where
  PT : ℚ
  PB : ℚ
  PN : ℚ
  PF : ℚ
  sum_one : PT + PB + PN + PF = 1
  nonneg_T : 0 ≤ PT
  nonneg_B : 0 ≤ PB
  nonneg_N : 0 ≤ PN
  nonneg_F : 0 ≤ PF

/-- A proposition evaluates to a specific 4-value in each of the 4 regions. -/
structure PropVal where
  vT : Val4
  vB : Val4
  vN : Val4
  vF : Val4

namespace PropVal

def and (a b : PropVal) : PropVal :=
  ⟨Val4.and a.vT b.vT, Val4.and a.vB b.vB, Val4.and a.vN b.vN, Val4.and a.vF b.vF⟩

def or (a b : PropVal) : PropVal :=
  ⟨Val4.or a.vT b.vT, Val4.or a.vB b.vB, Val4.or a.vN b.vN, Val4.or a.vF b.vF⟩

def not (a : PropVal) : PropVal :=
  ⟨Val4.not a.vT, Val4.not a.vB, Val4.not a.vN, Val4.not a.vF⟩

end PropVal

infixl:65 " ⊓ " => PropVal.and
infixl:60 " ⊔ " => PropVal.or
prefix:75 "∼" => PropVal.not

/-- Base variable p -/
def p_var : PropVal := ⟨Val4.T, Val4.B, Val4.N, Val4.F⟩

/--
  Belief operator: Sums the probability mass of regions where the proposition is supported.
  Returns a constant PropVal (the same Val4 in all 4 regions).
-/
def Belief (M : Model) (c : ℚ) (P : PropVal) : PropVal :=
  let pos_mass :=
    (if P.vT.pos then M.PT else 0) +
    (if P.vB.pos then M.PB else 0) +
    (if P.vN.pos then M.PN else 0) +
    (if P.vF.pos then M.PF else 0)
  let neg_mass :=
    (if P.vT.neg then M.PT else 0) +
    (if P.vB.neg then M.PB else 0) +
    (if P.vN.neg then M.PN else 0) +
    (if P.vF.neg then M.PF else 0)
  let val : Val4 := ⟨decide (pos_mass ≥ c), decide (neg_mass ≥ c)⟩
  ⟨val, val, val, val⟩

-- Helpers for the theorem
def pos_mass (M : Model) (P : PropVal) : ℚ :=
  (if P.vT.pos then M.PT else 0) +
  (if P.vB.pos then M.PB else 0) +
  (if P.vN.pos then M.PN else 0) +
  (if P.vF.pos then M.PF else 0)

def neg_mass (M : Model) (P : PropVal) : ℚ :=
  (if P.vT.neg then M.PT else 0) +
  (if P.vB.neg then M.PB else 0) +
  (if P.vN.neg then M.PN else 0) +
  (if P.vF.neg then M.PF else 0)

def glut_mass (M : Model) (P : PropVal) : ℚ :=
  (if (P.vT.pos && P.vT.neg) then M.PT else 0) +
  (if (P.vB.pos && P.vB.neg) then M.PB else 0) +
  (if (P.vN.pos && P.vN.neg) then M.PN else 0) +
  (if (P.vF.pos && P.vF.neg) then M.PF else 0)

/--
  The Core Theorem of 4-NPEL:
  An Epistemic Glut (believing P and believing ~P) requires
  a high probability of Ontological Gluts for P.
  Specifically: P(Gluts) >= 2c - 1
-/
theorem epistemic_glut_requires_ontological_glut
    (M : Model) (c : ℚ) (P : PropVal)
    (h_pos : pos_mass M P ≥ c)
    (h_neg : neg_mass M P ≥ c) :
    glut_mass M P ≥ 2 * c - 1 := by
  have h1 := M.sum_one
  have h2 := M.nonneg_T
  have h3 := M.nonneg_B
  have h4 := M.nonneg_N
  have h5 := M.nonneg_F
  unfold pos_mass neg_mass glut_mass at *
  revert h_pos h_neg
  cases P.vT.pos <;> cases P.vT.neg <;>
  cases P.vB.pos <;> cases P.vB.neg <;>
  cases P.vN.pos <;> cases P.vN.neg <;>
  cases P.vF.pos <;> cases P.vF.neg <;>
  simp <;> intros <;> linarith

/-- Validitäts-Standard ST (Strict-to-Tolerant): 1 -> {1, b} -/
def isValid_ST (premise conclusion : Val4) : Bool :=
  not (premise == Val4.T && conclusion == Val4.F)

/-- Validitäts-Standard LP (Tolerant-to-Tolerant): {1, b} -> {1, b} -/
def isValid_LP (premise conclusion : Val4) : Bool :=
  not (premise.pos && not conclusion.pos)

/-- Validitäts-Standard SS (Strict-to-Strict): 1 -> 1 -/
def isValid_SS (premise conclusion : Val4) : Bool :=
  not (premise == Val4.T && conclusion != Val4.T)

/--
  Globale Gültigkeit prüft, ob die Inferenz in ALLEN Regionen gültig ist.
-/
def isGloballyValid_LP (premise conclusion : PropVal) : Bool :=
  isValid_LP premise.vT conclusion.vT &&
  isValid_LP premise.vB conclusion.vB &&
  isValid_LP premise.vN conclusion.vN &&
  isValid_LP premise.vF conclusion.vF

def isGloballyValid_ST (premise conclusion : PropVal) : Bool :=
  isValid_ST premise.vT conclusion.vT &&
  isValid_ST premise.vB conclusion.vB &&
  isValid_ST premise.vN conclusion.vN &&
  isValid_ST premise.vF conclusion.vF

def isGloballyValid_SS (premise conclusion : PropVal) : Bool :=
  isValid_SS premise.vT conclusion.vT &&
  isValid_SS premise.vB conclusion.vB &&
  isValid_SS premise.vN conclusion.vN &&
  isValid_SS premise.vF conclusion.vF

-- --- SIMULATION / TESTS ---
-- Wir definieren ein konkretes Modell, um Paradoxien zu testen.
def M_paradox : Model := {
  PT := 0.4
  PB := 0.3 -- Hoher Anteil an Gluts!
  PN := 0.2
  PF := 0.1
  sum_one := by norm_num
  nonneg_T := by norm_num
  nonneg_B := by norm_num
  nonneg_N := by norm_num
  nonneg_F := by norm_num
}

def c_thresh : ℚ := 4/5 -- 0.8

-- Belief Consistency: B(p) => ~B(~p)
-- Prämisse: B(p)
def prem1 := Belief M_paradox c_thresh p_var
-- Konklusion: ~B(~p)
def conc1 := ∼(Belief M_paradox c_thresh (∼p_var))

#eval isGloballyValid_LP prem1 conc1
#eval isGloballyValid_ST prem1 conc1
#eval isGloballyValid_SS prem1 conc1

end FourNPEL
