# JevBridge Gates J1-J2

Branch: `research/jev-bridge-j1-j2`

## Gate J1 — semantic contract

J1 accepts a Jev-style four-cell distribution only under the simplex contract

```
pT,pF,pB,pN >= 0
pT + pF + pB + pN = 1
```

and derives

```
P+ = pT + pB
P- = pF + pB
PB = pB
PN = pN
```

Lean proves the balance identity

```
P+ + P- + PN = 1 + PB
```

and constructs a canonical four-world finite 4PEL model whose world weights
preserve the four masses.

**Boundary:** representability does not imply that Jev's internal uncertainty is
already a 4PEL world measure.

## Gate J2 — falsification panel

The formal panel contains controlled T/F/B/N distributions at threshold 3/4,
a scalar-collapse counterexample where B and N both map to 1/2, and the
intervention path

```
N -> T -> B -> F
```

The Python harness consumes pre-labelled Jev outputs in JSONL form.

Required fields:

```json
{"id":"case-001","expected":"B","t":0.1,"f":0.1,"b":0.7,"n":0.1}
```

Optional `chain` and `step` fields test intervention sequences.

### Empirical acceptance criteria

Real-data mode defaults to:

- at least 25 pre-labelled cases in each of T/F/B/N;
- overall projected accuracy >= 0.90;
- B/N accuracy >= 0.90;
- false classical certainty (T/F on true B/N cases) <= 0.05;
- every supplied intervention chain projects exactly to its pre-labelled path.

The 2D B/N centroid distance and the scalar-balance B/N distance are diagnostic
outputs, not hard pass criteria.

Fixture mode is deliberately incapable of claiming empirical success.

## Local build

PowerShell:

```powershell
git fetch origin
git switch research/jev-bridge-j1-j2
git pull --ff-only

lake build

python scripts/jev_bridge_gate_j2.py data/jev_bridge_gate_j2_fixture.jsonl --mode fixture
```

Expected Python terminator:

```
JEV_GATE_J2_HARNESS_OK
```

For real Jev outputs:

```powershell
python scripts/jev_bridge_gate_j2.py .\data\my_jev_results.jsonl --mode real
```

A real empirical pass prints:

```
JEV_GATE_J2_EMPIRICAL_PASS
```

A failure exits with status 2 and prints:

```
JEV_GATE_J2_EMPIRICAL_FAIL
```
