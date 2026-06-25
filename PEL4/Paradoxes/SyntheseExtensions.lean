import PEL4.Syntax
import PEL4.Diagnostics
import PEL4.ProbabilisticEvidence
import PEL4.ReliableEvidence
import PEL4.Revision

namespace PEL4.Paradoxes.SyntheseExtensions

/-!
Executable companion models for the recent Synthese papers discussed in the
manuscript.  The point of this file is deliberately experimental: each block
turns a philosophical pressure point into a small finite 4-PEL model that can
be inspected with `#eval!`.
-/

/- -------------------------------------------------------------------------
Ochoa / Backes: support and justification do not freely aggregate.

Both `p` and `q` reach the Lockean threshold, while their conjunction does not.
This makes the closure principle

    B(p) and B(q) -> B(p and q)

evaluate to strict falsity in the model.
------------------------------------------------------------------------- -/

inductive AggAtom where
  | p | q
deriving DecidableEq, Repr

inductive AggAgent where
  | a
deriving DecidableEq, Repr

inductive AggWorld where
  | w1 | w2 | w3 | w4 | w5
deriving DecidableEq, Repr

def agg_val : AggWorld -> AggAtom -> FDEValue
| AggWorld.w1, AggAtom.p => FDEValue.T
| AggWorld.w2, AggAtom.p => FDEValue.T
| AggWorld.w3, AggAtom.p => FDEValue.T
| AggWorld.w4, AggAtom.p => FDEValue.F
| AggWorld.w5, AggAtom.p => FDEValue.F
| AggWorld.w1, AggAtom.q => FDEValue.F
| AggWorld.w2, AggAtom.q => FDEValue.F
| AggWorld.w3, AggAtom.q => FDEValue.T
| AggWorld.w4, AggAtom.q => FDEValue.T
| AggWorld.w5, AggAtom.q => FDEValue.T

def agg_worlds : FiniteSet AggWorld :=
  [AggWorld.w1, AggWorld.w2, AggWorld.w3, AggWorld.w4, AggWorld.w5]

def agg_mu : FiniteSet AggWorld -> Rat
| S =>
  let p1 := if S.contains AggWorld.w1 then (1 : Rat) / 5 else 0
  let p2 := if S.contains AggWorld.w2 then (1 : Rat) / 5 else 0
  let p3 := if S.contains AggWorld.w3 then (1 : Rat) / 5 else 0
  let p4 := if S.contains AggWorld.w4 then (1 : Rat) / 5 else 0
  let p5 := if S.contains AggWorld.w5 then (1 : Rat) / 5 else 0
  p1 + p2 + p3 + p4 + p5

axiom agg_mu_total : forall (_ : AggAgent) (_ : AggWorld), agg_mu agg_worlds = 1
axiom agg_mu_empty : forall (_ : AggAgent) (_ : AggWorld), agg_mu [] = 0
axiom agg_c_gt_half : forall (_ : AggAgent), (3 : Rat) / 5 > 1 / 2
axiom agg_c_le_one : forall (_ : AggAgent), (3 : Rat) / 5 <= 1

def AggregationModel : Model AggWorld AggAgent AggAtom :=
  { worlds := agg_worlds
  , R := fun _ _ => agg_worlds
  , mu := fun _ _ => agg_mu
  , val := agg_val
  , c := fun _ => (3 : Rat) / 5
  , mu_total := agg_mu_total
  , mu_empty := agg_mu_empty
  , c_gt_half := agg_c_gt_half
  , c_le_one := agg_c_le_one
  }

def agg_p : Formula AggAtom AggAgent := Formula.prop AggAtom.p
def agg_q : Formula AggAtom AggAgent := Formula.prop AggAtom.q
def Bp : Formula AggAtom AggAgent := Formula.bel AggAgent.a agg_p
def Bq : Formula AggAtom AggAgent := Formula.bel AggAgent.a agg_q
def BpAndq : Formula AggAtom AggAgent := Formula.bel AggAgent.a (Formula.and agg_p agg_q)

def aggregationClosure : Formula AggAtom AggAgent :=
  Formula.implies (Formula.and Bp Bq) BpAndq

#eval! eval AggregationModel AggWorld.w1 Bp
#eval! eval AggregationModel AggWorld.w1 Bq
#eval! eval AggregationModel AggWorld.w1 BpAndq
#eval! eval AggregationModel AggWorld.w1 aggregationClosure
#eval! P_pos AggregationModel AggAgent.a AggWorld.w1 agg_p
#eval! P_pos AggregationModel AggAgent.a AggWorld.w1 agg_q
#eval! P_pos AggregationModel AggAgent.a AggWorld.w1 (Formula.and agg_p agg_q)

/- -------------------------------------------------------------------------
d'Agostini: two gaps for one glut.

The current FDE connective keeps `L and notL` gappy when both conjuncts are
gappy.  To model d'Agostini's conjunctive glut directly, we represent the
whole contradiction as a primitive structured item.  The two `#eval!` lines
below mark the exact extension point: FDE conjunction gives N, the primitive
conjunctive-glut item gives B.
------------------------------------------------------------------------- -/

inductive ConjGlutAtom where
  | L | notL | L_and_notL
deriving DecidableEq, Repr

inductive ConjGlutAgent where
  | a
deriving DecidableEq, Repr

inductive ConjGlutWorld where
  | w
deriving DecidableEq, Repr

def conjGlut_val : ConjGlutWorld -> ConjGlutAtom -> FDEValue
| ConjGlutWorld.w, ConjGlutAtom.L => FDEValue.N
| ConjGlutWorld.w, ConjGlutAtom.notL => FDEValue.N
| ConjGlutWorld.w, ConjGlutAtom.L_and_notL => FDEValue.B

def conjGlut_mu : FiniteSet ConjGlutWorld -> Rat
| S => if S.contains ConjGlutWorld.w then 1 else 0

axiom conjGlut_mu_total :
  forall (_ : ConjGlutAgent) (_ : ConjGlutWorld), conjGlut_mu [ConjGlutWorld.w] = 1
axiom conjGlut_mu_empty :
  forall (_ : ConjGlutAgent) (_ : ConjGlutWorld), conjGlut_mu [] = 0
axiom conjGlut_c_gt_half : forall (_ : ConjGlutAgent), (4 : Rat) / 5 > 1 / 2
axiom conjGlut_c_le_one : forall (_ : ConjGlutAgent), (4 : Rat) / 5 <= 1

def ConjunctiveGlutModel : Model ConjGlutWorld ConjGlutAgent ConjGlutAtom :=
  { worlds := [ConjGlutWorld.w]
  , R := fun _ _ => [ConjGlutWorld.w]
  , mu := fun _ _ => conjGlut_mu
  , val := conjGlut_val
  , c := fun _ => (4 : Rat) / 5
  , mu_total := conjGlut_mu_total
  , mu_empty := conjGlut_mu_empty
  , c_gt_half := conjGlut_c_gt_half
  , c_le_one := conjGlut_c_le_one
  }

def L : Formula ConjGlutAtom ConjGlutAgent := Formula.prop ConjGlutAtom.L
def notL_atom : Formula ConjGlutAtom ConjGlutAgent := Formula.prop ConjGlutAtom.notL
def L_and_notL_as_FDE : Formula ConjGlutAtom ConjGlutAgent := Formula.and L notL_atom
def L_and_notL_as_structured_glut : Formula ConjGlutAtom ConjGlutAgent :=
  Formula.prop ConjGlutAtom.L_and_notL

#eval! eval ConjunctiveGlutModel ConjGlutWorld.w L
#eval! eval ConjunctiveGlutModel ConjGlutWorld.w notL_atom
#eval! eval ConjunctiveGlutModel ConjGlutWorld.w L_and_notL_as_FDE
#eval! eval ConjunctiveGlutModel ConjGlutWorld.w L_and_notL_as_structured_glut
#eval! evalDiagnosticFormula ConjunctiveGlutModel ConjGlutWorld.w
  (DiagnosticFormula.check Diagnostic.gap L_and_notL_as_FDE)
#eval! evalDiagnosticFormula ConjunctiveGlutModel ConjGlutWorld.w
  (DiagnosticFormula.check Diagnostic.glut L_and_notL_as_structured_glut)

/- -------------------------------------------------------------------------
Pailos: validity gaps and gluts.

This is a deliberately small executable proxy for four-valued meta-validity.
`valid` and `invalid` are independent bits, just as FDE truth has independent
positive and negative support.  The example `B -> F` is ST-valid at the local
standard while also an LP-counterexample, hence meta-glutty.
------------------------------------------------------------------------- -/

structure MetaValidity where
  valid : Bool
  invalid : Bool
deriving DecidableEq, Repr

def MetaValidity.V : MetaValidity := { valid := true, invalid := false }
def MetaValidity.G : MetaValidity := { valid := true, invalid := true }
def MetaValidity.N : MetaValidity := { valid := false, invalid := false }
def MetaValidity.I : MetaValidity := { valid := false, invalid := true }

def isStrictTrue (v : FDEValue) : Bool :=
  v.pos && !v.neg

def isTolerated (v : FDEValue) : Bool :=
  v.pos

def stValidAt (premise conclusion : FDEValue) : Bool :=
  (!isStrictTrue premise) || isTolerated conclusion

def lpCounterexampleAt (premise conclusion : FDEValue) : Bool :=
  isTolerated premise && !isTolerated conclusion

def metaValidityAt (premise conclusion : FDEValue) : MetaValidity :=
  { valid := stValidAt premise conclusion
  , invalid := lpCounterexampleAt premise conclusion
  }

#eval! metaValidityAt FDEValue.B FDEValue.F
#eval! metaValidityAt FDEValue.N FDEValue.F
#eval! metaValidityAt FDEValue.T FDEValue.N

/- -------------------------------------------------------------------------
LET-style reliability and paraconsistent revision prototypes.

These small evaluations keep the 4-valued base intact while showing two
natural extension layers suggested by recent evidence logics: reliability
filters and entrenchment-sensitive revision of contradictory evidence.
------------------------------------------------------------------------- -/

#eval! reliabilityProjection rawGlutReliableOnOneSide
#eval! hasReliableGlut rawGlutReliableOnBothSides
#eval! reviseByEntrenchment keepBothWhenEquallyEntrenched
#eval! reviseByEntrenchment keepPositiveWhenMoreEntrenched
#eval! reviseByEntrenchment keepNegativeWhenMoreEntrenched

end PEL4.Paradoxes.SyntheseExtensions
