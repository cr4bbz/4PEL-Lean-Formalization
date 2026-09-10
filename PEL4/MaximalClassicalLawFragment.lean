import PEL4.RecursiveClassicalLawProfile

namespace PEL4

/-!
# Gate 15: maximality and necessity of the recursive classical fragment

The word "maximal" needs a declared comparison class. Here a candidate
fragment is any predicate on world/formula nodes whose members satisfy the
Gate-14 recursive LEM/EFQ profile. This captures closure under the subformula
and accessibility recursion without claiming maximality among unrelated proof
systems or languages.
-/

/-- A candidate fragment is law-closed when every admitted node carries LEM
and EFQ throughout the complete Gate-14 recursion. -/
def ModalFormula.IsRecursiveClassicalLawFragment
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (fragment : W -> ModalFormula Atom Ag -> Prop) : Prop :=
  forall w phi,
    fragment w phi ->
      ModalFormula.RecursiveClassicalLawProfileAt m w phi

/-- Recursive semantic classicality itself is a law-closed fragment. -/
theorem compositionallyClassicalAt_isRecursiveClassicalLawFragment
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) :
    ModalFormula.IsRecursiveClassicalLawFragment m
      (ModalFormula.CompositionallyClassicalAt m) := by
  intro w phi h
  exact (recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt
    m phi w).2 h

/-- Gate-15 maximality theorem. Every recursively law-closed candidate is
contained in the compositionally classical sector. -/
theorem recursiveClassicalLawFragment_le_compositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (fragment : W -> ModalFormula Atom Ag -> Prop)
    (hFragment :
      ModalFormula.IsRecursiveClassicalLawFragment m fragment) :
    forall w phi,
      fragment w phi ->
        ModalFormula.CompositionallyClassicalAt m w phi := by
  intro w phi hMember
  exact (recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt
    m phi w).1 (hFragment w phi hMember)

/-- Exact membership form: the maximal law fragment and Gate-13 recursive
classicality have the same elements. -/
theorem maximalRecursiveClassicalLawFragment_membership
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : ModalFormula Atom Ag) :
    ModalFormula.RecursiveClassicalLawProfileAt m w phi <->
      ModalFormula.CompositionallyClassicalAt m w phi :=
  recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt m phi w

/-! ## Necessity and independence boundaries -/

/-- One-world model exposing a gap atom, a glut atom, and a classical false
atom. The probability component is immaterial to the propositional witnesses. -/
def gate15LawBoundaryModel : Model Unit Unit (Fin 3) where
  worlds := [()]
  R := fun _ _ => [()]
  mu := fun _ _ S => if S = [] then 0 else 1
  val := fun _ p =>
    if p = 0 then FDEValue.N
    else if p = 1 then FDEValue.B
    else FDEValue.F
  c := fun _ => 3 / 4
  mu_total := by intro _ _; decide +kernel
  mu_empty := by intro _ _; decide +kernel
  c_gt_half := by intro _; decide +kernel
  c_le_one := by intro _; decide +kernel

def gate15GapAtom : ModalFormula (Fin 3) Unit := .prop 0
def gate15GlutAtom : ModalFormula (Fin 3) Unit := .prop 1
def gate15FalseAtom : ModalFormula (Fin 3) Unit := .prop 2

/-- A gap validates universal EFQ but fails tolerant LEM. -/
theorem gate15_gap_separates_LEM_from_EFQ :
    (¬ ModalFormula.TolerantLEMAt
        gate15LawBoundaryModel () gate15GapAtom) /\
      ModalFormula.UniversalLPExplosionAt
        gate15LawBoundaryModel () gate15GapAtom := by
  constructor
  · rw [modalTolerantLEMAt_iff_gapFree]
    simp [gate15LawBoundaryModel, gate15GapAtom, evalModal,
      GapFreeValue, isGap]
    all_goals decide +kernel
  · rw [modalUniversalLPExplosionAt_iff_glutFree]
    simp [gate15LawBoundaryModel, gate15GapAtom, evalModal,
      GlutFreeValue, isGlut]
    all_goals decide +kernel

/-- A glut validates tolerant LEM but fails universal EFQ. -/
theorem gate15_glut_separates_EFQ_from_LEM :
      ModalFormula.TolerantLEMAt
        gate15LawBoundaryModel () gate15GlutAtom /\
      (¬ ModalFormula.UniversalLPExplosionAt
        gate15LawBoundaryModel () gate15GlutAtom) := by
  constructor
  · rw [modalTolerantLEMAt_iff_gapFree]
    simp [gate15LawBoundaryModel, gate15GlutAtom, evalModal,
      GapFreeValue, isGap]
    all_goals decide +kernel
  · rw [modalUniversalLPExplosionAt_iff_glutFree]
    simp [gate15LawBoundaryModel, gate15GlutAtom, evalModal,
      GlutFreeValue, isGlut]
    all_goals decide +kernel

/-- Root-level classical laws are not enough: conjunction with a classical
false atom can hide a gappy subformula and make the root value `F`. -/
def gate15RootMasksGap : ModalFormula (Fin 3) Unit :=
  ModalFormula.and gate15GapAtom gate15FalseAtom

theorem gate15_root_laws_do_not_imply_recursive_laws :
    ModalFormula.ClassicalLawPairAt
        gate15LawBoundaryModel () gate15RootMasksGap /\
      (¬ ModalFormula.RecursiveClassicalLawProfileAt
        gate15LawBoundaryModel () gate15RootMasksGap) := by
  constructor
  · rw [modalClassicalLawPairAt_iff_classical]
    simp [gate15RootMasksGap, gate15GapAtom, gate15FalseAtom,
      gate15LawBoundaryModel, evalModal, IsClassicalValue,
      FDEValue.and, FDEValue.N, FDEValue.F]
  · rw [recursiveClassicalLawProfileAt_iff_compositionallyClassicalAt]
    intro h
    have hGap := h.1
    change IsClassicalValue FDEValue.N at hGap
    rcases hGap with hGap | hGap <;> cases hGap

/-- Both law components are individually necessary for membership in the
maximal recursive classical fragment. -/
theorem gate15_both_law_axes_are_necessary :
    (¬ ModalFormula.RecursiveClassicalLawProfileAt
        gate15LawBoundaryModel () gate15GapAtom) /\
      (¬ ModalFormula.RecursiveClassicalLawProfileAt
        gate15LawBoundaryModel () gate15GlutAtom) := by
  constructor
  · intro h
    change ModalFormula.ClassicalLawPairAt
      gate15LawBoundaryModel () gate15GapAtom at h
    exact gate15_gap_separates_LEM_from_EFQ.1 h.1
  · intro h
    change ModalFormula.ClassicalLawPairAt
      gate15LawBoundaryModel () gate15GlutAtom at h
    exact gate15_glut_separates_EFQ_from_LEM.2 h.2

end PEL4
