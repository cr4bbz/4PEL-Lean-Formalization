# Conflict Nerve Research Notes

## 1. Core construction

For each claim `i`, let `B_i` be the part of the latent conflict carrier on which claim `i` is object-level glutty. The support Conflict Nerve is the abstract simplicial complex

```text
N = { A != empty : intersection_{i in A} B_i is nonempty }.
```

In the finite weighted incidence model this is equivalent to

```text
A is a simplex  <=>  J_A > 0,
```

where `J_A` is the cumulative co-conflict mass.

More generally, for a raw mass threshold `t`,

```text
N_t = { A : J_A >= t }.
```

Because the co-conflict hierarchy is antitone under inclusion,

```text
A subset B  =>  J_B <= J_A,
```

each `N_t` is downward closed and therefore an abstract simplicial complex.

## 2. Persistence-compatible filtration

Define

```text
f(A) = d - J_A,
```

where `d` is total carrier mass. Then

```text
A subset B  =>  f(A) <= f(B).
```

This is exactly the face/coface monotonicity required of a simplicial filtration. The full weighted filtration is information-equivalent to the full co-conflict hierarchy because

```text
J_A = d - f(A).
```

Combined with the formal Möbius reconstruction theorem, this gives the information chain

```text
exact incidence x_A
    <-> full co-conflict hierarchy J_A
    <-> exact Conflict-Nerve filtration f(A).
```

Support, individual thresholds, Betti numbers, Euler characteristic, and persistence barcodes are progressively coarser summaries.

## 3. Three-claim topological underdetermination

Inside the already formalized symmetric fiber

```text
d = 6
b1 = b2 = b3 = 3
S = 9
p = 3
q = r = 1/4
```

there are at least three different support-nerve signatures.

### fiberA

```text
j12 > 0
j13 = j23 = j123 = 0
```

Support complex: one edge plus an isolated vertex.
Euler count: `chi = 2`.

### fiberCycle

```text
x12 = x13 = x23 = 1
x123 = 0
j12, j13, j23 > 0
j123 = 0
```

Support complex: the boundary of a triangle without the 2-simplex.
Euler count: `chi = 0`.

### fiberB

```text
j12, j13, j23, j123 > 0
```

Support complex: the filled triangle.
Euler count: `chi = 1`.

Thus identical carrier mass, local marginals, total multiplicity, peak, and Conflict-Triangle coordinates can hide distinct support-nerve topology. The Lean development currently certifies the complete finite signatures and their Euler counts. A formal homology layer is future work.

Working name: **Topological Conflict Underdetermination**.

## 4. Relation to classical nerve constructions

The construction is not a new use of the word `nerve`. Classically, the nerve of a family of sets has one vertex for each set and a simplex for each finite subfamily with nonempty common intersection. Our claim-indexed support nerve is exactly of this form for the family `{B_i}`.

Reference:

- Encyclopedia of Mathematics, "Covering (of a set)": https://encyclopediaofmath.org/wiki/Covering_%28of_a_set%29

Important caution: the classical Nerve Theorem relates a nerve to the homotopy type of an underlying topological union only under additional hypotheses on the cover, typically contractibility/good-cover style assumptions. In the current 4PEL model the carrier cells are finite combinatorial objects with no intrinsic topology. Therefore the Conflict Nerve should initially be treated as an intrinsic combinatorial topology of intersection patterns, not as automatically homotopy equivalent to an independently given evidence space.

Useful modern discussion:

- Daniel A. Ramras, "Variations on the nerve theorem" (2023): https://arxiv.org/abs/2305.04794
- Nicholas J. Cavanna and Donald R. Sheehy, "The Generalized Persistent Nerve Theorem" (2018): https://arxiv.org/abs/1807.07920

## 5. Dowker interpretation

Let `C` be the set of positive-mass conflict cells and let `I` be the set of claim indices. Define a binary relation

```text
i R c  <=>  claim i is active in conflict cell c.
```

The claim-side Dowker complex consists of claim subsets that share at least one related cell. This is exactly the support Conflict Nerve.

The transpose relation gives a dual cell-side complex: a collection of conflict cells forms a simplex when the cells share at least one conflicted claim.

Classical Dowker duality says that the two complexes associated with a binary relation are homotopy equivalent. This suggests a duality between

```text
claim-centric conflict topology
and
cell/world-centric conflict topology.
```

References:

- Morten Brun and Lars M. Salbu, "The Rectangle Complex of a Relation" (2022): https://arxiv.org/abs/2207.02018
- Morten Brun and Darij Grinberg, "The Dowker theorem via discrete Morse theory" (2024): https://arxiv.org/abs/2407.15454
- Morten Brun, Marius G. Fosse, Lars M. Salbu, "Dowker Duality for Relations of Categories" (2023): https://arxiv.org/abs/2303.16032

This connection is established mathematics and should be cited rather than presented as a novel theorem of 4PEL. The research opportunity is the epistemic interpretation and interaction with the signed conflict hierarchy.

## 6. Persistent homology direction

The filtration `f(A)=d-J_A` is directly compatible with ordinary filtered-simplicial-complex software. GUDHI defines a filtration value so that faces appear no later than cofaces, exactly the property formally proved for `f`.

References:

- GUDHI persistent cohomology documentation: https://gudhi.inria.fr/python/latest/persistent_cohomology_user.html
- GUDHI simplex tree documentation: https://gudhi.inria.fr/python/latest/simplex_tree_ref.html

A separate literature also studies weighted persistent homology:

- Shiquan Ren, Chengyuan Wu, Jie Wu, "Weighted Persistent Homology" (2017): https://arxiv.org/abs/1708.06722

For the immediate project, ordinary persistent homology of the exact filtration is the cleaner first step. The filtration values already encode the weights.

## 7. Research questions

1. **Betti underdetermination.** Which Betti vectors can occur inside one fixed-marginal fiber?
2. **Persistence underdetermination.** Can two profiles have identical `(d,b_i,q,r)` but arbitrarily different persistence barcodes?
3. **Sharp-conflict restrictions.** Which support nerves are compatible with the Sharp Conflict Spine?
4. **Redundancy versus topology.** What bounds, if any, connect `r` or `S-d` to simplex dimension, Euler characteristic, or Betti numbers?
5. **Möbius versus topology.** Which interaction orders are necessary to determine a given topological invariant?
6. **Dual Dowker interpretation.** What epistemic meaning belongs to the cell-side Dowker complex?
7. **Stability.** How stable are Conflict-Nerve barcodes under small perturbations of signed evidence masses?
8. **Higher-order relations.** Can signed positive/negative/glut/gap information be represented by multiway relations and higher-order Dowker constructions?

## 8. Immediate formalization roadmap

- [x] threshold Conflict Nerve membership
- [x] downward closure
- [x] nested threshold complexes
- [x] filtration `f(A)=d-J_A`
- [x] face/coface filtration monotonicity
- [x] recovery `J_A=d-f(A)`
- [x] three-claim disconnected/cycle/filled signatures
- [x] three-claim Euler counts
- [x] generic support-existence theorem connecting `J_A>0` to a positive-mass incidence cell containing `A`
- [ ] explicit claim/cell Dowker relation
- [ ] homology implementation or external verified computation bridge
- [ ] persistent-homology export format for GUDHI
