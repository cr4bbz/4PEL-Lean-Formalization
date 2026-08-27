# Preface research summary

This note summarizes the Preface case-study developed on
`research/preface-case-study`.

## 1. Starting point: aggregation rather than object-level inconsistency

The classical Preface model has individually accepted claims together with
accepted fallibility.  In the finite symmetric family with `n` claims there is
one all-correct world and `n` one-error worlds.  At threshold `c`, the Preface
region is

\[
\frac12 < c \le \frac{n}{n+1}.
\]

The same upper boundary survives asymmetric one-error allocations.  In simplex
coordinates

\[
(a,e_1,\ldots,e_n)\in\Delta^n,
\]

the region is cut out by

\[
a,e_i\le 1-c.
\]

The general packing/union-bound argument gives the same necessary condition

\[
c\le \frac{n}{n+1}.
\]

At the maximal threshold the symmetric barycentric allocation is forced.

## 2. Signed four-valued Preface models

Belief is represented by independent positive and negative threshold crossings:

\[
B_c(\varphi)=([P^+(\varphi)\ge c],[P^-(\varphi)\ge c]).
\]

With the same local threshold-belief profile `(T,T,T)`, three explicit models
realize three distinct conjunction states:

- `F`: rejection fracture,
- `N`: determination gap,
- `B`: conflict saturation.

Thus local acceptance does not determine the global four-valued aggregation
state.

## 3. Latent Conflict Carrier Theorem

If a finite conjunction is object-level `B` at a world, at least one conjunct
is object-level `B` at that world.  Combining this FDE fact with positive and
negative threshold overlap yields, for arbitrary finite arity,

\[
P(\exists i:p_i=B)\ge 2c-1.
\]

In finite counts, if the model has mass `m` and threshold count `k`,

\[
2k\le m+L,
\]

where `L` is the local conflict-carrier mass.

The bound is independent of the number of conjuncts.  Global epistemic
conflict can therefore be locally invisible at the threshold-belief level, but
it cannot be locally evidentially ungrounded.

## 4. Sharpness and the Sharp Conflict Spine

At conjunction level let `t,b,n,f` be the four FDE cell masses.  Equality in the
carrier bound admits the exact accounting decomposition

\[
L=(2c-1)+\delta_+ + \delta_- + P_N + W,
\]

where `delta_+`, `delta_-` are positive/negative threshold overshoots and `W`
is unused local carrier mass beyond conjunction-`B` mass.

Sharpness therefore requires all inefficiency terms to vanish.  The unique
normalized sharp conjunction macrostate is

\[
(P_T,P_B,P_N,P_F)=(1-c,2c-1,0,1-c).
\]

As `c` varies from `1/2` to `1`, these states form the **Sharp Conflict Spine**.

## 5. Conflict topology: concentration and redundancy

Let

- `d` be local conflict-carrier mass,
- `b_i` the local glut marginals,
- `S=\sum_i b_i`,
- `p=\max_i b_i`.

For arbitrary finite arity `n`,

\[
d\le S\le np\le nd.
\]

After normalization this yields an arity-independent triangle

\[
0\le r\le q\le1,
\]

where `q` measures concentration and `r` redundancy.

The three vertices represent distributed nonredundant conflict, concentrated
nonredundant conflict, and maximally redundant conflict.

## 6. Conflict Incidence Simplex

The coarse topology suppresses the actual membership pattern of local gluts.
For every nonempty subset `A` of the `n` conjuncts, let `x_A` be the carrier
mass on which exactly the conjuncts in `A` are glutty.  Normalized incidence
profiles live in

\[
\Delta^{2^n-2}.
\]

The local marginals are projections

\[
\frac{b_i}{d}=\sum_{A\ni i}x_A.
\]

Redundancy has the exact interpretation

\[
\rho=\frac{S}{d}=E(|A|\mid L),
\]

and hence

\[
r=\frac{E(|A|\mid L)-1}{n-1}.
\]

For `n=3`, explicit profiles show that identical carrier, local marginals,
`S`, `p`, `q`, and `r` can coexist with different higher-order incidence.
This is **Incidence Underdetermination**.

## 7. Fixed-marginal fibers

For the symmetric three-claim fiber

\[
b_1=b_2=b_3=m,\qquad d=2m,
\]

the overlap coordinates satisfy

\[
x_{12}+x_{13}+x_{23}+2x_{123}=m,
\]

with singleton coordinates forced by the opposite-pair masses and triple mass.
After weighting the triple coordinate by two and normalizing, the continuous
fiber is a tetrahedron

\[
\Delta^3.
\]

More generally, fixing normalization and all `n` first-order marginals leaves
a generic affine dimension

\[
2^n-n-2,
\]

subject to boundary degeneracies.  This dimension formula is currently a
research target rather than a completed generic Lean theorem.

## 8. Co-conflict / zeta hierarchy

For a query subset `Q`, define the cumulative co-conflict mass

\[
J_Q=\sum_{A\supseteq Q}x_A.
\]

This is the zeta transform of the exact incidence coordinates on the Boolean
lattice.  The arbitrary-arity Lean development proves antitonicity:

\[
Q\subseteq R\quad\Rightarrow\quad J_R\le J_Q.
\]

Thus first-order local contradiction probabilities are only the bottom layer
of a complete hierarchy of simultaneous conflict interactions.

For `n=3`, the familiar pair/triple formulas are the corresponding Möbius
relations, e.g.

\[
x_{12}+J_{123}=J_{12}.
\]

## 9. Current inversion target

The natural inverse statement is Boolean Möbius inversion:

\[
x_A=\sum_{B\supseteq A}(-1)^{|B|-|A|}J_B.
\]

The Lean implementation now begins with the equivalent iterated finite-
difference operator.  A `false` coordinate applies

\[
F(\ldots,0,\ldots)-F(\ldots,1,\ldots),
\]

while a `true` coordinate is retained.  Applied through every coordinate, this
should cancel all strict supersets and recover exactly `x_A`.

The intended philosophical conclusion is:

> Truncated co-conflict descriptions are underdetermining, but the complete
> hierarchy of all interaction orders is information-complete for incidence
> structure.

## Verification status

The Preface development through the arbitrary-arity co-conflict hierarchy,
including `PrefaceConflictMobiusInverseN.lean`, has been successfully built
with Lean 4.31.0 through the repository root import.  In particular,
`full_coconflict_hierarchy_reconstructs_exact_mass` is machine-verified on the
active research history.
