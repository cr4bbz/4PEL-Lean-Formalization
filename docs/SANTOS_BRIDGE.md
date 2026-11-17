# Santos bridge — Lockean belief as a neighbourhood modality

Branch: `research/santos-bridge` (based on `paper/epistemic-dynamics-v0.4.0-gate116`).
No gate number has been assigned yet.

## Research question

Santos, *A Four-Valued Dynamic Epistemic Logic* (JoLLI 29, 2020), gives a relational
Belnap–Dunn epistemic logic of evidence with public announcements and leaves belief as
future work. Can 4-PEL threshold belief be placed on the same models as a conservative
belief extension, and which of the static and dynamic laws survive the threshold?

## Reading of the belief operator

With `N_c(w) = { X | μ_w(X) ≥ c }` the operator `belief` is a two-channel
Scott–Montague neighbourhood modality: the positive bit says `‖φ‖⁺ ∈ N_c(w)`, the
negative bit says `‖φ‖⁻ ∈ N_c(w)`.

## Verified results

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

| Module | Theorem | Statement | Status |
|---|---|---|---|
| `NeighbourhoodBelief` | `belief_pos_iff_neighbourhood`, `belief_neg_iff_neighbourhood` | two-channel reading | PROVED |
| | `neighbourhood_N`, `neighbourhood_P` | `R(w) ∈ N_c(w)`, `∅ ∉ N_c(w)` (legacy `Model`) | PROVED |
| | `neighbourhood_M` | upward closure (integrity) | PROVED |
| | `neighbourhood_D` | disjoint events are not both neighbourhoods (integrity, `c > 1/2`) | PROVED |
| | `belief_thresholdConsistent_of_no_glut` | no accessible glut ⇒ belief is never `B` | PROVED |
| | `neighbourhood_not_C` | `{0,1}`, `{1,2}` ∈ `N_{2/3}`, `{1}` ∉ | FINITE-WITNESS |
| `SantosBridge` | `santosBox_pos_implies_belief_pos`, `belief_neg_implies_santosBox_neg` | sandwich `□φ ≤_t Bφ` (legacy `Model`) | PROVED |
| | `belief_pos_eq_santosBox_pos_of_certainty` | support channels coincide at `c = 1` (integrity, regular measure) | PROVED |
| | `belief_pos_and_of_certainty` | aggregation (C) returns for support at `c = 1` | PROVED |
| | `belief_T_but_santosBox_F` | `Bφ = T`, `□φ = F` at `c = 2/3` | FINITE-WITNESS |
| `SantosDynamics` | `belief_conditionalize_pos_iff`, `belief_conditionalize_neg_iff` | belief after conditionalisation on `E` ⇔ `μ(X ∩ E⁺) ≥ c·μ(E⁺)` before | PROVED |
| | `belief_neg_iff_all_neg_of_certainty` | at `c = 1` refutation of belief is universal (`□¬`), not existential (`◇¬`) | PROVED |
| `SantosReduction` | `eval_conditionalize_of_beliefFree`, `eval_announce_of_beliefFree` | S1: belief-free formulas are invariant under both updates | PROVED |
| | `eval_bel_conditionalize_pos_iff`, `eval_bel_conditionalize_neg_iff` | S1: formula-level reduction for `B φ`, `φ` belief-free | PROVED |
| | `bel_not_invariant` | S1: `B p` changes from `F` to `T` under conditionalisation on `p` | FINITE-WITNESS |
| | `announce` | Santos-style update is a `Model` given nonzero evidence mass | PROVED |
| | `belief_announce_eq_conditionalize` | both updates give the same belief, both channels | PROVED |
| | `box_announce_ne_conditionalize` | the relational box differs between the updates | FINITE-WITNESS |
| `ConditionalBelief` | `evalC_condOn_eq_red` | full reduction for arbitrary modal depth in the language with `B(φ | ψ)` and `□`: `eval (M↑E) φ = eval M (red E φ)` | PROVED |
| `SantosConservativity` | `Model.reduct_serial`, `evalC_toC_eq_evalR` | 4-PEL models are serial; box formulas ignore the measure | PROVED |
| | `RelModel.expand`, `evalC_expand_eq_evalR` | every serial relational model expands (uniform measure) with the same box values | PROVED |
| | `box_validity_conservative` | box validity over 4-PEL models ⇔ over serial relational models, for any property of values | PROVED |
| `GradedAggregation` | `mass_intersection_lower_bound`, `neighbourhood_graded_C`, `neighbourhood_intersection_pos` | `μ(A∩B) ≥ μ(A)+μ(B)−1`, hence `≥ 2c−1 > 0` for neighbourhoods | PROVED |

## Interpretive caveats

* INTERPRETIVE: the clauses of `santosBox` (support at all accessible states, refutation
  at some) are the standard Belnap–Dunn modal clauses; they match the paper's stated
  clauses for `◇`, `¬◇` and `¬□φ ≡ ◇¬φ`. The paper's own display of the `□` clause
  should be checked against the PDF before it is cited by number.
* Completeness of the Lockean threshold is *not* a valuation condition: a classically
  valued 50/50 state already yields the gap value. Only consistency is governed by the
  valuation (no glut). The static picture is therefore asymmetric.
* Santos' announcement restricts the state space; 4-PEL conditionalisation keeps `R`
  and changes only `μ`. The two updates agree on supported belief but not on the box.

## Open questions (next step)

* **S1 – formula-level reduction (settled for depth one, open for nesting).** The reduction theorems hold for a fixed semantic
  value. For a formula `φ` the value after the update is `eval (conditionalize m E) φ`.
  For which fragment is `eval` invariant under conditionalisation? Conjecture: exactly
  the belief-free formulas; for nested belief the reduction needs the conditional
  operator at every depth.
* **S2 – conditional belief as primitive.** `ConditionalNeighbourhood` is the natural
  static counterpart of the dynamic operator. Does adding `B(φ | E)` to the syntax give
  a full set of reduction axioms in Santos' style (atoms, ¬, ∧, B)?
* **S3 – frame laws under update.** Which of N, P, M, D hold for `N_c^E`? N and P should
  hold when `μ(E⁺) > 0`; D should hold for events disjoint *inside* `E⁺`.
* **S4 – the refutation channel.** Is `¬B¬` needed as a second primitive to express
  Santos' `◇`, given that the refutation channels differ even at `c = 1`?
* **S5 – threshold crossing.** Characterise when `Bφ` and `[E]Bφ` differ, in terms of
  `μ(‖φ‖⁺ ∩ E⁺) / μ(E⁺)` versus `μ(‖φ‖⁺)`; connect to `ModalDynamicsBeliefInstability`
  and `ModalDynamicsBeliefRestoration`.

A short paper with the verified results, the transfer analysis and the open questions
is in `paper/santos-bridge/santos_bridge.pdf`.

## Status of the open questions after the second round

* S1/S2: settled for conditionalisation at arbitrary depth (`evalC_condOn_eq_red`).
  Still open: the same law for the state-deleting update (relativised box), and whether
  conditional belief is definable from plain belief.
* Conservativity: proved over serial relational models with finite ranges. Transfer to
  Santos' own system still depends on his box clause, seriality and the finite model
  property (INTERPRETIVE).
* Axiomatisation: graded aggregation is a further sound principle. Completeness for a
  fixed `c ∈ (1/2, 1)` remains open; van Eijck–Renne treat `c = 1/2` and need a
  Scott-type scheme and a certainty operator.
