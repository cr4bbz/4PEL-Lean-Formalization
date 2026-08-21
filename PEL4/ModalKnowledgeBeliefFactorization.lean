import PEL4.ModalKnowledgeBeliefValueClassification

namespace PEL4

/-!
# Knowledge as stability-filtered probabilistic belief

The complete four-valued classification of `K` relative to threshold belief `B`
can be compressed into one extensional factorization theorem.

On a stable accessible FDE profile, primitive knowledge and probabilistic belief
have the same complete value. On an unstable profile, primitive knowledge is
forced to strict `F` regardless of the probabilistic belief value.

Thus the knowledge operator is exactly threshold belief passed through a
qualitative stability gate.
-/

/-- Exact factorization of evidence-stable knowledge through probabilistic
threshold belief and the accessible-profile stability test. -/
theorem modal_knowledge_as_stability_filtered_belief
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.know i phi) =
      if modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) = true then
        evalModal m w (ModalFormula.bel i phi)
      else
        FDEValue.F := by
  by_cases hStable : modalAccessibleValueStable (m.R i w)
      (fun x => evalModal m x phi) = true
  · have hEq := modal_knowledge_equals_belief_of_stable
      m i w phi hStable
    simp [hStable, hEq]
  · have hUnstable : modalAccessibleValueStable (m.R i w)
        (fun x => evalModal m x phi) = false := by
      cases hValue : modalAccessibleValueStable (m.R i w)
          (fun x => evalModal m x phi) <;> simp_all
    have hKFalse := modal_knowledge_false_of_instability
      m i w phi hUnstable
    simp [hStable, hKFalse]

/-- Stable evidence makes the stability filter transparent. -/
theorem modal_knowledge_factorization_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hStable : modalAccessibleValueStable (m.R i w)
      (fun x => evalModal m x phi) = true) :
    evalModal m w (ModalFormula.know i phi) =
      evalModal m w (ModalFormula.bel i phi) := by
  exact modal_knowledge_equals_belief_of_stable m i w phi hStable

/-- Unstable evidence makes the stability filter absorb every belief value into
strict `F` knowledge. -/
theorem modal_knowledge_factorization_unstable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hUnstable : modalAccessibleValueStable (m.R i w)
      (fun x => evalModal m x phi) = false) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.F := by
  exact modal_knowledge_false_of_instability m i w phi hUnstable

/-!
## Interpretation

The verified operator equation is:

```text
K(phi) = if Stable(phi) then B(phi) else F.
```

This is the most compact form of the current knowledge/belief theory. It shows
that the difference between the two operators is not another probability
threshold. The extra epistemic operation performed by `K` is a qualitative
invariance test on the complete four-valued evidence profile.

In particular, instability is not merely low confidence. It is a distinct
structural failure mode that overrides the probabilistic output and sends
knowledge to strict `F`.
-/

end PEL4
