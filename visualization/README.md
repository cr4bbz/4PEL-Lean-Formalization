# Conflict Geometry Visualizations

These scripts visualize formulas and finite examples that are formalized in the Lean development. They are exploratory and explanatory tools, not replacements for the proofs.

## Setup

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install -r visualization/requirements.txt
```

## Latent-Conflict Triangle

```powershell
python visualization/conflict_triangle.py
```

Add formalized or experimental points with repeated `--point q r label` arguments:

```powershell
python visualization/conflict_triangle.py --point 0.25 0.25 preface-fiber
```

The admissible region is

```text
0 <= r <= q <= 1.
```

## Symmetric fixed-marginal tetrahedron

```powershell
python visualization/fiber_tetrahedron.py --m 6
```

The script plots the continuous tetrahedron together with the integer lattice points satisfying

```text
x12 + x13 + x23 + 2*x123 = m.
```

The normalized barycentric coordinates are

```text
u12   = x12 / m
u13   = x13 / m
u23   = x23 / m
u123  = 2*x123 / m
```

and sum to one.

## Hidden-dimension growth

```powershell
python visualization/dimension_growth.py --max-n 12
```

This compares

```text
visible constraints       n + 1
full incidence coordinates 2^n - 1
hidden affine freedom       2^n - n - 2
```

for `n >= 2`.

## Conflict Nerve

```powershell
python visualization/conflict_nerve.py
```

The default view compares three profiles with the same carrier and first-order marginals:

- `fiberA`: one support edge plus an isolated vertex,
- `fiberCycle`: all three support edges and no filled triangle,
- `fiberB`: the filled triangle.

All three have `d = 6` and `b1 = b2 = b3 = 3`, hence the same coarse triangle projection, while their support nerves differ.

Inspect a single profile or change the co-conflict threshold:

```powershell
python visualization/conflict_nerve.py --preset fiberCycle --threshold 1
python visualization/conflict_nerve.py --preset fiberB --threshold 2
```

The support nerve is threshold `1` for the natural-valued finite masses used by the Lean model.

## Saving figures

Each script supports `--save`:

```powershell
python visualization/conflict_nerve.py --save visualization/out/conflict-nerve.png
```

Generated figures are intentionally not required by the Lean build.
