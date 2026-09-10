import PEL4.ConditionalizationProbabilityIntegrity
import PEL4.RecoveryConsequenceTransfer

namespace PEL4

/-!
# Gate 14: recursive LEM/EFQ profile

Gate 9 separates the two classical-law boundaries at one formula value:
tolerant excluded middle removes gaps and universal LP explosion removes gluts.
Gate 14 lifts their conjunction to every syntactically and modally relevant
node of a `ModalFormula`.

The result is exact and does not need probability integrity: the recursive
law profile is equivalent to Gate 13's recursive semantic classicality.
Probability integrity is needed only when that semantic condition is related
back to the threshold-completeness recovery certificate.
-/

/-- Classical disjunction inside the modal language. -/
def ModalFormula.or {Atom Ag : Type}
    (phi psi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.not
    (ModalFormula.and (ModalFormula.not phi) (ModalFormula.not psi))

/-- Modal excluded middle. -/
def ModalFormula.excludedMiddle {Atom Ag : Type}
    (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.or phi (ModalFormula.not phi)

/-- Modal direct contradiction. -/
def ModalFormula.contradiction {Atom Ag : Type}
    (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.and phi (ModalFormula.not phi)

theorem evalModal_or
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi psi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.or phi psi) =
      FDEValue.or (evalModal m w phi) (evalModal m w psi) := by
  rfl

theorem evalModal_excludedMiddle
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.excludedMiddle phi) =
      excludedMiddleValue (evalModal m w phi) := by
  rfl

theorem evalModal_contradiction
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.contradiction phi) =
      contradictionValue (evalModal m w phi) := by
  rfl

/-- Tolerant excluded middle at one modal formula node. -/
def ModalFormula.TolerantLEMAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.excludedMiddle phi)).pos = true

/-- Universal LP explosion at one modal formula node. -/
def ModalFormula.UniversalLPExplosionAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  forall q : FDEValue,
    LP_valid (evalModal m w (ModalFormula.contradiction phi)) q

/-- The two law tests at one node. -/
def ModalFormula.ClassicalLawPairAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  ModalFormula.TolerantLEMAt m w phi /\
  ModalFormula.UniversalLPExplosionAt m w phi

theorem modalTolerantLEMAt_iff_gapFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.TolerantLEMAt m w phi <->
      GapFreeValue (evalModal m w phi) := by
  rw [ModalFormula.TolerantLEMAt, evalModal_excludedMiddle]
  exact excludedMiddle_designated_iff_gapFree (evalModal m w phi)

theorem modalUniversalLPExplosionAt_iff_glutFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.UniversalLPExplosionAt m w phi <->
      GlutFreeValue (evalModal m w phi) := by
  rw [ModalFormula.UniversalLPExplosionAt, evalModal_contradiction]
  exact universal_LP_explosion_iff_glutFree (evalModal m w phi)

/-- At one node, tolerant LEM and universal EFQ jointly say exactly that the
four-valued result is classical. -/
theorem modalClassicalLawPairAt_iff_classical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.ClassicalLawPairAt m w phi <->
      IsClassicalValue (evalModal m w phi) := by
  rw [ModalFormula.ClassicalLawPairAt,
    modalTolerantLEMAt_iff_gapFree,
    modalUniversalLPExplosionAt_iff_glutFree]
  exact evidentiallyRegularValue_iff_classical (evalModal m w phi)

/-- LEM and EFQ at the current node and at every subformula node reached by
the same recursion used by compositional recovery. -/
def ModalFormula.RecursiveClassicalLawProfileAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W -> ModalFormula Atom Ag -> Prop
  | w, phi@(.prop _) => ModalFormula.ClassicalLawPairAt m w phi
  | w, phi@(.not sub) =>
      ModalFormula.ClassicalLawPairAt m w phi /\
      ModalFormula.RecursiveClassicalLawProfileAt m w sub
  | w, phi@(.and left right) =>
      ModalFormula.ClassicalLawPairAt m w phi /\
      ModalFormula.RecursiveClassicalLawProfileAt m w left /\
      ModalFormula.RecursiveClassicalLawProfileAt m w right
  | w, phi@(.bel i sub) =>
      ModalFormula.ClassicalLawPairAt m w phi /\
      (forall u, u ∈ m.R i w ->
        ModalFormula.RecursiveClassicalLawProfileAt m u sub)
  | w, phi@(.know i sub) =>
      ModalFormula.ClassicalLawPairAt m w phi /\
      (forall u, u ∈ m.R i w ->
        ModalFormula.RecursiveClassicalLawProfileAt m u sub)
  | w, phi@(.poss i sub) =>
      ModalFormula.ClassicalLawPairAt m w phi /\
      (forall u, u ∈ m.R i w ->
        ModalFormula.RecursiveClassicalLawProfileAt m u sub)

/-- Gate-14 local result: recursive LEM+EFQ is exactly recursive semantic
classicality. -/
theorem recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    forall w,
      ModalFormula.RecursiveClassicalLawProfileAt m w phi <->
        ModalFormula.CompositionallyClassicalAt m w phi := by
  induction phi with
  | prop p =>
      intro w
      exact modalClassicalLawPairAt_iff_classical m w (.prop p)
  | not phi ih =>
      intro w
      constructor
      · intro h
        exact (ih w).1 h.2
      · intro h
        exact ⟨
          (modalClassicalLawPairAt_iff_classical m w (.not phi)).2
            (evalModal_isClassical_of_compositionallyClassicalAt
              m (.not phi) w h),
          (ih w).2 h⟩
  | and phi psi ihPhi ihPsi =>
      intro w
      constructor
      · intro h
        exact ⟨(ihPhi w).1 h.2.1, (ihPsi w).1 h.2.2⟩
      · intro h
        exact ⟨
          (modalClassicalLawPairAt_iff_classical m w (.and phi psi)).2
            (evalModal_isClassical_of_compositionallyClassicalAt
              m (.and phi psi) w h),
          (ihPhi w).2 h.1,
          (ihPsi w).2 h.2⟩
  | bel i phi ih =>
      intro w
      constructor
      · intro h
        exact ⟨
          fun u hu => (ih u).1 (h.2 u hu),
          (modalClassicalLawPairAt_iff_classical m w (.bel i phi)).1 h.1⟩
      · intro h
        exact ⟨
          (modalClassicalLawPairAt_iff_classical m w (.bel i phi)).2 h.2,
          fun u hu => (ih u).2 (h.1 u hu)⟩
  | know i phi ih =>
      intro w
      constructor
      · intro h u hu
        exact (ih u).1 (h.2 u hu)
      · intro h
        exact ⟨
          (modalClassicalLawPairAt_iff_classical m w (.know i phi)).2
            (evalModal_isClassical_of_compositionallyClassicalAt
              m (.know i phi) w h),
          fun u hu => (ih u).2 (h u hu)⟩
  | poss i phi ih =>
      intro w
      constructor
      · intro h u hu
        exact (ih u).1 (h.2 u hu)
      · intro h
        exact ⟨
          (modalClassicalLawPairAt_iff_classical m w (.poss i phi)).2
            (evalModal_isClassical_of_compositionallyClassicalAt
              m (.poss i phi) w h),
          fun u hu => (ih u).2 (h u hu)⟩

def ModalFormula.RecursiveClassicalLawProfile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : ModalFormula Atom Ag) : Prop :=
  forall w, ModalFormula.RecursiveClassicalLawProfileAt m w phi

theorem recursiveClassicalLawProfile_iff_compositionallyClassical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : ModalFormula Atom Ag) :
    ModalFormula.RecursiveClassicalLawProfile m phi <->
      ModalFormula.CompositionallyClassical m phi := by
  constructor <;> intro h w
  · exact (recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt
      m phi w).1 (h w)
  · exact (recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt
      m phi w).2 (h w)

/-- With probability integrity, the recursive law profile is also exactly the
Gate-10 recovery certificate. -/
theorem recursiveClassicalLawProfile_iff_compositionalRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.RecursiveClassicalLawProfile m phi <->
      ModalFormula.CompositionalRecovery m phi := by
  rw [recursiveClassicalLawProfile_iff_compositionallyClassical,
    compositionalRecovery_iff_compositionallyClassical m hIntegrity phi]

end PEL4
