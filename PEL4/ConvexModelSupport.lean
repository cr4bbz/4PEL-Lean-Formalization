import PEL4.ConvexModelPath
import PEL4.ModalDynamicsStability
import PEL4.ModalDynamicsRobustness
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Probability-free support events along convex strong model paths

C17D constructs complete strong 4-PEL models along a rational convex path and
proves affine mass for every fixed event.  The remaining formula-level issue is
that a modal formula can itself change value as probability changes, so its
positive and negative support events need not be fixed.

This module isolates a large safe fragment.  `ModalProbabilityFree` formulas
contain no `bel`, although they may contain arbitrarily nested knowledge and raw
possibility. Their semantics depends only on accessibility and atomic valuation.
Consequently two models with the same `R` and `val` agree on every
probability-free formula.  Along `convexStrongModelAt`, both fields are fixed,
so the positive and negative support events of every probability-free formula
are fixed as well.

Combining that event invariance with `convexStrongModelAt_eventMass` yields the
first genuine formula-level affine support theorem on a path of complete strong
models.
-/

/-- Probability-free modal evaluation depends only on accessibility and atomic
valuation, not on the probability field or threshold. -/
theorem evalModal_probabilityFree_of_same_skeleton
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom)
    (hR : n.R = m.R)
    (hVal : n.val = m.val)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    ∀ w, evalModal n w phi = evalModal m w phi := by
  induction hFree with
  | prop p =>
      intro w
      change n.val w p = m.val w p
      rw [hVal]
  | neg hPhi ih =>
      intro w
      change FDEValue.not (evalModal n w _) =
        FDEValue.not (evalModal m w _)
      rw [ih w]
  | conj hPhi hPsi ihPhi ihPsi =>
      intro w
      change FDEValue.and (evalModal n w _) (evalModal n w _) =
        FDEValue.and (evalModal m w _) (evalModal m w _)
      rw [ihPhi w, ihPsi w]
  | @know i phi hPhi ih =>
      intro w
      change modalKnowledgeValue n i w (fun u => evalModal n u phi) =
        modalKnowledgeValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal n u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalKnowledgeValue_congr
        m n i w
        (fun u => evalModal m u phi)
        (fun u => evalModal n u phi)
        (by simpa using congrArg (fun r => r i w) hR)
        hValues
  | @poss i phi hPhi ih =>
      intro w
      change modalRawPossibilityValue n i w (fun u => evalModal n u phi) =
        modalRawPossibilityValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal n u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalRawPossibilityValue_congr
        m n i w
        (fun u => evalModal m u phi)
        (fun u => evalModal n u phi)
        (by simpa using congrArg (fun r => r i w) hR)
        hValues

/-- Positive support events of a probability-free formula agree between models
with the same accessibility and atomic valuation. -/
theorem positiveSupportEvent_probabilityFree_of_same_skeleton
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom)
    (hR : n.R = m.R)
    (hVal : n.val = m.val)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    filterWorlds (n.R i w) (fun u => (evalModal n u phi).pos) =
      filterWorlds (m.R i w) (fun u => (evalModal m u phi).pos) := by
  have hRi : n.R i w = m.R i w := by
    simpa using congrArg (fun r => r i w) hR
  have hPred :
      (fun u => (evalModal n u phi).pos) =
        (fun u => (evalModal m u phi).pos) := by
    funext u
    exact congrArg FDEValue.pos
      (evalModal_probabilityFree_of_same_skeleton m n hR hVal hFree u)
  rw [hRi, hPred]

/-- Negative support events satisfy the symmetric invariance theorem. -/
theorem negativeSupportEvent_probabilityFree_of_same_skeleton
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom)
    (hR : n.R = m.R)
    (hVal : n.val = m.val)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    filterWorlds (n.R i w) (fun u => (evalModal n u phi).neg) =
      filterWorlds (m.R i w) (fun u => (evalModal m u phi).neg) := by
  have hRi : n.R i w = m.R i w := by
    simpa using congrArg (fun r => r i w) hR
  have hPred :
      (fun u => (evalModal n u phi).neg) =
        (fun u => (evalModal m u phi).neg) := by
    funext u
    exact congrArg FDEValue.neg
      (evalModal_probabilityFree_of_same_skeleton m n hR hVal hFree u)
  rw [hRi, hPred]

/-- Positive belief-support mass of every probability-free formula is affine
along the complete convex strong model path. -/
theorem convexStrongModelAt_positiveBeliefMass_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    modalPositiveBeliefMass
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel i w phi =
      (1 - t) * modalPositiveBeliefMass
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi +
      t * modalPositiveBeliefMass
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi := by
  let m0 := weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne
  let m1 := weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne
  let mt :=
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel
  have hT0 : mt.R = m0.R := by
    rfl
  have hV0 : mt.val = m0.val := by
    rfl
  have h10 : m1.R = m0.R := by
    rfl
  have hV10 : m1.val = m0.val := by
    rfl
  have hEventT :=
    positiveSupportEvent_probabilityFree_of_same_skeleton
      m0 mt hT0 hV0 i w hFree
  have hEvent1 :=
    positiveSupportEvent_probabilityFree_of_same_skeleton
      m0 m1 h10 hV10 i w hFree
  have hEventTR :
      filterWorlds (R i w) (fun u => (evalModal mt u phi).pos) =
        filterWorlds (R i w) (fun u => (evalModal m0 u phi).pos) := by
    change
      filterWorlds (mt.R i w) (fun u => (evalModal mt u phi).pos) =
        filterWorlds (m0.R i w) (fun u => (evalModal m0 u phi).pos)
    exact hEventT
  have hEvent1R :
      filterWorlds (R i w) (fun u => (evalModal m1 u phi).pos) =
        filterWorlds (R i w) (fun u => (evalModal m0 u phi).pos) := by
    change
      filterWorlds (m1.R i w) (fun u => (evalModal m1 u phi).pos) =
        filterWorlds (m0.R i w) (fun u => (evalModal m0 u phi).pos)
    exact hEvent1
  unfold modalPositiveBeliefMass
  change
    weightedEventMass (R i w) (convexWeight t (q0 i w) (q1 i w))
        (filterWorlds (R i w) (fun u => (evalModal mt u phi).pos)) =
      (1 - t) *
          weightedEventMass (R i w) (q0 i w)
            (filterWorlds (R i w) (fun u => (evalModal m0 u phi).pos)) +
        t * weightedEventMass (R i w) (q1 i w)
            (filterWorlds (R i w) (fun u => (evalModal m1 u phi).pos))
  rw [hEventTR, hEvent1R]
  exact weightedEventMass_convex
    (R i w) (q0 i w) (q1 i w)
    (filterWorlds (R i w) (fun u => (evalModal m0 u phi).pos)) t

/-- Negative belief-support mass is affine along the same model path. -/
theorem convexStrongModelAt_negativeBeliefMass_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    modalNegativeBeliefMass
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel i w phi =
      (1 - t) * modalNegativeBeliefMass
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi +
      t * modalNegativeBeliefMass
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi := by
  let m0 := weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne
  let m1 := weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne
  let mt :=
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel
  have hT0 : mt.R = m0.R := by
    rfl
  have hV0 : mt.val = m0.val := by
    rfl
  have h10 : m1.R = m0.R := by
    rfl
  have hV10 : m1.val = m0.val := by
    rfl
  have hEventT :=
    negativeSupportEvent_probabilityFree_of_same_skeleton
      m0 mt hT0 hV0 i w hFree
  have hEvent1 :=
    negativeSupportEvent_probabilityFree_of_same_skeleton
      m0 m1 h10 hV10 i w hFree
  have hEventTR :
      filterWorlds (R i w) (fun u => (evalModal mt u phi).neg) =
        filterWorlds (R i w) (fun u => (evalModal m0 u phi).neg) := by
    change
      filterWorlds (mt.R i w) (fun u => (evalModal mt u phi).neg) =
        filterWorlds (m0.R i w) (fun u => (evalModal m0 u phi).neg)
    exact hEventT
  have hEvent1R :
      filterWorlds (R i w) (fun u => (evalModal m1 u phi).neg) =
        filterWorlds (R i w) (fun u => (evalModal m0 u phi).neg) := by
    change
      filterWorlds (m1.R i w) (fun u => (evalModal m1 u phi).neg) =
        filterWorlds (m0.R i w) (fun u => (evalModal m0 u phi).neg)
    exact hEvent1
  unfold modalNegativeBeliefMass
  change
    weightedEventMass (R i w) (convexWeight t (q0 i w) (q1 i w))
        (filterWorlds (R i w) (fun u => (evalModal mt u phi).neg)) =
      (1 - t) *
          weightedEventMass (R i w) (q0 i w)
            (filterWorlds (R i w) (fun u => (evalModal m0 u phi).neg)) +
        t * weightedEventMass (R i w) (q1 i w)
            (filterWorlds (R i w) (fun u => (evalModal m1 u phi).neg))
  rw [hEventTR, hEvent1R]
  exact weightedEventMass_convex
    (R i w) (q0 i w) (q1 i w)
    (filterWorlds (R i w) (fun u => (evalModal m0 u phi).neg)) t

/-!
## Research consequence

If this gate compiles, the previous support-plane geometry is no longer merely
compatible with a model-valued probability path.  For every probability-free
modal formula, the signed support coordinates themselves are Lean-verified
affine functions along a path of complete strong models.

The next theorem layer can therefore reuse the existing threshold-straddling,
crossing-order, and intermediate-phase results directly at model level for this
fragment.  Formulas containing `bel` remain a separate problem because their
support events may move with probability.
-/

end PEL4
