import PEL4.ModalKnowledgeBeliefUpgrade

namespace PEL4

/-!
# Complete four-valued knowledge/belief classification

The preceding gates established two facts:

* stable accessible profiles make evidence-stable knowledge `K` and threshold
  belief `B` coincide exactly;
* unstable profiles force `K` to strict `F`.

This module packages those facts into a complete value-level classification.
The three non-`F` values `T`, `B`, and `N` can occur as knowledge values only on
stable profiles, where they coincide with probabilistic belief.  The value `F`
is exceptional because it is also the absorbing output of epistemic
instability.
-/

/-- Any non-`F` knowledge value is equivalent to stability plus the same
probabilistic belief value. -/
theorem modal_knowledge_nonfalse_value_iff_stable_and_belief_value
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (v : FDEValue) (hv : v ≠ FDEValue.F) :
    evalModal m w (ModalFormula.know i phi) = v ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true ∧
      evalModal m w (ModalFormula.bel i phi) = v := by
  constructor
  · intro hK
    have hStable : modalAccessibleValueStable (m.R i w)
        (fun x => evalModal m x phi) = true := by
      cases hS : modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) with
      | true =>
          exact hS
      | false =>
          have hKF := modal_knowledge_false_of_instability
            m i w phi hS
          have hVF : v = FDEValue.F := by
            calc
              v = evalModal m w (ModalFormula.know i phi) := hK.symm
              _ = FDEValue.F := hKF
          exact (hv hVF).elim
    have hEq := modal_knowledge_equals_belief_of_stable
      m i w phi hStable
    refine ⟨hStable, ?_⟩
    calc
      evalModal m w (ModalFormula.bel i phi) =
          evalModal m w (ModalFormula.know i phi) := hEq.symm
      _ = v := hK
  · rintro ⟨hStable, hB⟩
    have hEq := modal_knowledge_equals_belief_of_stable
      m i w phi hStable
    calc
      evalModal m w (ModalFormula.know i phi) =
          evalModal m w (ModalFormula.bel i phi) := hEq
      _ = v := hB

/-- Strict false knowledge is the unique exceptional phase: it arises either
from instability itself or from stable evidence whose threshold belief is also
strict `F`. -/
theorem modal_knowledge_false_iff_unstable_or_belief_false
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.F ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = false ∨
      evalModal m w (ModalFormula.bel i phi) = FDEValue.F := by
  constructor
  · intro hK
    cases hS : modalAccessibleValueStable (m.R i w)
        (fun x => evalModal m x phi) with
    | false =>
        exact Or.inl hS
    | true =>
        right
        have hEq := modal_knowledge_equals_belief_of_stable
          m i w phi hS
        calc
          evalModal m w (ModalFormula.bel i phi) =
              evalModal m w (ModalFormula.know i phi) := hEq.symm
          _ = FDEValue.F := hK
  · intro h
    rcases h with hUnstable | hBFalse
    · exact modal_knowledge_false_of_instability m i w phi hUnstable
    · cases hS : modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) with
      | false =>
          exact modal_knowledge_false_of_instability m i w phi hS
      | true =>
          have hEq := modal_knowledge_equals_belief_of_stable
            m i w phi hS
          calc
            evalModal m w (ModalFormula.know i phi) =
                evalModal m w (ModalFormula.bel i phi) := hEq
            _ = FDEValue.F := hBFalse

/-- Exact `T` phase. -/
theorem modal_knowledge_true_iff_stable_and_belief_true
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.T ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true ∧
      evalModal m w (ModalFormula.bel i phi) = FDEValue.T := by
  exact modal_knowledge_nonfalse_value_iff_stable_and_belief_value
    m i w phi FDEValue.T (by native_decide)

/-- Exact glutty `B` phase. -/
theorem modal_knowledge_both_iff_stable_and_belief_both
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.B ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true ∧
      evalModal m w (ModalFormula.bel i phi) = FDEValue.B := by
  exact modal_knowledge_nonfalse_value_iff_stable_and_belief_value
    m i w phi FDEValue.B (by native_decide)

/-- Exact gappy `N` phase. -/
theorem modal_knowledge_neither_iff_stable_and_belief_neither
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.N ↔
      modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true ∧
      evalModal m w (ModalFormula.bel i phi) = FDEValue.N := by
  exact modal_knowledge_nonfalse_value_iff_stable_and_belief_value
    m i w phi FDEValue.N (by native_decide)

/-!
## Interpretation

The complete `K`/`B` relation is asymmetric only at `F`:

```text
K = T  iff Stable and B = T
K = B  iff Stable and B = B
K = N  iff Stable and B = N
K = F  iff Unstable or B = F
```

Thus `F` is an instability absorber for evidence-stable knowledge.  The other
three values are transparent: once stability holds, knowledge simply inherits
the probabilistic belief value.

This makes the role of stability sharper than the positive upgrade theorem.
Stability is not merely an extra condition for designated knowledge; it is the
exact gate through which every non-false four-valued belief status becomes a
knowledge status.
-/

end PEL4
