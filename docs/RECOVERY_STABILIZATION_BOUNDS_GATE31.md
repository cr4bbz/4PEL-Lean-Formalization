# Gate 31: Progress and Stabilization Bounds

## Question

Gate 26 bounds the number of Recovery-status changes by a natural-valued descent potential. Gate 27 upgrades this to eventual Recovery-status stability. Neither result gives a deadline: arbitrarily long status-preserving stuttering can occur between the finitely many genuine flips.

Gate 31 asks what extra dynamic assumption turns eventual stabilization into a quantitative stabilization bound.

## Bounded progress

For a recovery descent system `sys`, trajectory `trajectory`, and horizon `B`, define `BoundedRecoveryProgress sys trajectory B` as follows:

> whenever the current Recovery status will differ at some later time, an adjacent Recovery-status-changing edge must occur within the next `B` update edges.

Formally, for every time `n`,

```text
if ∃ m > n with status(m) ≠ status(n),
then ∃ k < B with status(n+k) ≠ status(n+k+1).
```

This is a bounded-liveness assumption. It is deliberately stronger than ordinary eventual progress and is not derived from 4PEL or Conditionalization alone.

## Quantitative theorem

`RecoveryStabilizesBy sys trajectory N` means that the Recovery status is permanently constant from time `N` onward.

The main theorem is:

```text
recoveryTrajectory_stabilizesBy
```

If a trajectory follows a `RecoveryDescentSystem` and satisfies bounded Recovery progress with horizon `B`, then there is some `N` such that

```text
N ≤ B * sys.potential (trajectory 0)
```

and Recovery is permanently stable from `N` onward.

Mathematically,

\[
T_{\mathrm{stab}} \le B\,\Phi(s_0).
\]

The proof is by induction on the initial natural-valued potential. If no future status change exists, stabilization is immediate. Otherwise bounded progress supplies a flip within `B` edges. Gate 26 makes that flip strictly decrease the potential, and the induction hypothesis applies to the suffix after the flip.

Thus the bound decomposes cleanly into

\[
\text{maximum number of flips}
\times
\text{maximum waiting time per next flip}.
\]

## Sharpness

Gate 31 also contains a concrete sharpness witness with

```text
B = 3
initial potential = 2.
```

Its Recovery status profile is

```text
T T T | F F F | T T T ...
0 1 2   3 4 5   6 7 8
```

The status-changing edges are `2 -> 3` and `5 -> 6`. The trajectory is not stable from time `5`, but it is stable from time `6`. Hence

\[
T_{\mathrm{stab}} = 6 = 3 \cdot 2 = B\,\Phi(s_0).
\]

So the generic Gate-31 deadline cannot be improved without strengthening the hypotheses.

## What Gate 31 does not establish

Gate 31 does **not** prove that bounded progress follows from arbitrary 4PEL learning dynamics. It is an additional dynamic contract.

It also does not privilege the Recovery endpoint. The final stable status can still be Recovery or Non-Recovery, in accordance with Gate 28 and the path-dependence result of Gate 29.

The result therefore says:

```text
finite descent + bounded liveness => bounded-time phase stabilization
```

not:

```text
learning => bounded-time convergence to Recovery.
```

The latter is the stronger attractor question reserved for Gate 32.

## Research position

The Recovery dynamics now separate three quantitative questions:

1. **How many phase changes can occur?** Gate 26.
2. **Must phase changes eventually cease?** Gate 27.
3. **Under a progress contract, how soon must they cease?** Gate 31.

This turns the earlier qualitative phase picture into a small temporal resource theory: potential limits the number of costly phase changes, while the progress horizon limits how long the system may postpone the next one.
