import PEL4.ModalDynamicsAffineCrossing

namespace PEL4

/-!
# Temporal order of two affine threshold crossings

Affine Threshold Crossing gives a literal rational hit parameter whenever one
support coordinate changes threshold side.  A two-wall FDE transition therefore
has one hit on the positive support coordinate and one on the negative support
coordinate.

This module asks whether those two hits are simultaneous or sequential.

The key preliminary fact is uniqueness: a nonconstant affine rational path can
hit a fixed threshold at at most one parameter.  Since threshold straddling
forces distinct endpoints, every straddling affine segment therefore has one
intrinsic crossing time.
-/

/-- Threshold-straddling endpoints are necessarily distinct. -/
theorem thresholdStraddles_endpoints_ne
    (c x y : Rat)
    (hStraddle : ThresholdStraddles c x y) :
    x ≠ y := by
  intro hxy
  subst y
  rcases hStraddle with h | h
  · exact h.2 h.1
  · exact h.2 h.1

/-- A nonconstant affine rational path has at most one parameter at which it
hits a fixed threshold. -/
theorem affineRatPath_threshold_hit_unique
    (c x y t s : Rat)
    (hxy : x ≠ y)
    (ht : affineRatPath x y t = c)
    (hs : affineRatPath x y s = c) :
    t = s := by
  have hden : y - x ≠ 0 := by
    intro hzero
    have hyx : y = x := by
      have h := congrArg (fun z : Rat => z + x) hzero
      rw [Rat.sub_add_cancel, Rat.zero_add] at h
      exact h
    exact hxy hyx.symm
  have hsame : affineRatPath x y t = affineRatPath x y s :=
    ht.trans hs.symm
  unfold affineRatPath at hsame
  have hmul : t * (y - x) = s * (y - x) :=
    Rat.add_left_cancel x hsame
  have hdiv := congrArg (fun z : Rat => z / (y - x)) hmul
  rw [Rat.mul_div_cancel hden, Rat.mul_div_cancel hden] at hdiv
  exact hdiv

/-- Straddling therefore yields not merely a hit but a unique affine hit in the
rational unit interval. -/
theorem thresholdStraddles_has_unique_affine_unit_crossing
    (c x y : Rat)
    (hStraddle : ThresholdStraddles c x y) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧
      affineRatPath x y t = c ∧
      ∀ s : Rat, affineRatPath x y s = c → s = t := by
  rcases thresholdStraddles_has_affine_unit_crossing c x y hStraddle with
    ⟨t, ht0, ht1, hhit⟩
  have hxy := thresholdStraddles_endpoints_ne c x y hStraddle
  refine ⟨t, ht0, ht1, hhit, ?_⟩
  intro s hs
  exact affineRatPath_threshold_hit_unique c x y s t hxy hs hhit

/-- Data carried by the two support coordinates of a two-wall affine crossing. -/
structure AffineThresholdCrossingPair
    (c p0 p1 n0 n1 : Rat) where
  tp : Rat
  tn : Rat
  tp_nonneg : 0 ≤ tp
  tp_le_one : tp ≤ 1
  tn_nonneg : 0 ≤ tn
  tn_le_one : tn ≤ 1
  positive_hit : affineRatPath p0 p1 tp = c
  negative_hit : affineRatPath n0 n1 tn = c
  positive_unique : ∀ s : Rat, affineRatPath p0 p1 s = c → s = tp
  negative_unique : ∀ s : Rat, affineRatPath n0 n1 s = c → s = tn

/-- Two intrinsic affine crossing times have exactly one of three temporal
relations: positive first, simultaneous, or negative first. -/
theorem affineCrossingPair_order_trichotomy
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1) :
    pair.tp < pair.tn ∨ pair.tp = pair.tn ∨ pair.tn < pair.tp := by
  have htotal : pair.tp ≤ pair.tn ∨ pair.tn ≤ pair.tp := Rat.le_total
  rcases htotal with h | h
  · rcases (Rat.le_iff_lt_or_eq).1 h with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr (Or.inl heq)
  · rcases (Rat.le_iff_lt_or_eq).1 h with hlt | heq
    · exact Or.inr (Or.inr hlt)
    · exact Or.inr (Or.inl heq.symm)

/-- Simultaneous crossing is exactly intersection with the crossing point
`(c,c)` of the two threshold walls. -/
theorem affineCrossingPair_simultaneous_iff_common_hit
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1) :
    pair.tp = pair.tn ↔
      ∃ t : Rat,
        affineRatPath p0 p1 t = c ∧
        affineRatPath n0 n1 t = c := by
  constructor
  · intro hsim
    refine ⟨pair.tp, pair.positive_hit, ?_⟩
    simpa [hsim] using pair.negative_hit
  · rintro ⟨t, hpos, hneg⟩
    have htp : t = pair.tp := pair.positive_unique t hpos
    have htn : t = pair.tn := pair.negative_unique t hneg
    exact htp.symm.trans htn

/-- If the two crossings are not simultaneous, one and only one coordinate is
strictly earlier than the other. -/
theorem affineCrossingPair_sequential_order
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1)
    (hNotSim : pair.tp ≠ pair.tn) :
    pair.tp < pair.tn ∨ pair.tn < pair.tp := by
  rcases affineCrossingPair_order_trichotomy pair with hlt | heq | hgt
  · exact Or.inl hlt
  · exact False.elim (hNotSim heq)
  · exact Or.inr hgt

/-- Every two-wall conditionalized belief transition admits an intrinsic pair
of affine crossing times, and that pair has exactly one temporal order.

This is stated propositionally rather than as a data-valued `def`: the unique
crossing witnesses come from existential theorems, and Lean's constructive
`Exists` eliminator is intentionally restricted to propositions. -/
theorem conditionalization_belief_two_walls_crossing_order
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hTwo :
      thresholdWallCount
        (evalModal m w (ModalFormula.bel i phi))
        (evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi)) = 2) :
    ∃ pair : AffineThresholdCrossingPair
        (m.c i)
        (modalPositiveBeliefMass m i w phi)
        (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
        (modalNegativeBeliefMass m i w phi)
        (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi),
      pair.tp < pair.tn ∨ pair.tp = pair.tn ∨ pair.tn < pair.tp := by
  have hBoth :=
    (conditionalization_belief_two_walls_iff_both_supports_straddle
      m E hAdm i w phi).1 hTwo
  have hPos := hBoth.1
  have hNeg := hBoth.2
  unfold ConditionalizedPositiveStraddles at hPos
  unfold ConditionalizedNegativeStraddles at hNeg
  rcases thresholdStraddles_has_unique_affine_unit_crossing
      (m.c i)
      (modalPositiveBeliefMass m i w phi)
      (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
      hPos with ⟨tp, htp0, htp1, hpHit, hpUnique⟩
  rcases thresholdStraddles_has_unique_affine_unit_crossing
      (m.c i)
      (modalNegativeBeliefMass m i w phi)
      (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
      hNeg with ⟨tn, htn0, htn1, hnHit, hnUnique⟩
  let pair : AffineThresholdCrossingPair
      (m.c i)
      (modalPositiveBeliefMass m i w phi)
      (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
      (modalNegativeBeliefMass m i w phi)
      (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi) :=
    { tp := tp
    , tn := tn
    , tp_nonneg := htp0
    , tp_le_one := htp1
    , tn_nonneg := htn0
    , tn_le_one := htn1
    , positive_hit := hpHit
    , negative_hit := hnHit
    , positive_unique := hpUnique
    , negative_unique := hnUnique
    }
  exact ⟨pair, affineCrossingPair_order_trichotomy pair⟩

/-!
## Interpretation

For a two-wall transition the affine support path does not merely cross both
threshold walls.  Each wall has a unique intrinsic crossing time.

```text
  tp < tn  : positive threshold wall first
  tp = tn  : simultaneous crossing at (c,c)
  tn < tp  : negative threshold wall first
```

Thus diagonal motion in the FDE threshold square acquires temporal structure.
The simultaneous case is geometrically distinguished by the two-dimensional
support path passing through the intersection of the two threshold walls.

A natural next theorem is the **intermediate-vertex classification**: for
nonsimultaneous diagonal transitions, the order of the two crossings should
determine which adjacent FDE vertex occupies the interval between them.

Working name: **Affine Crossing-Order Geometry**.
-/

end PEL4
