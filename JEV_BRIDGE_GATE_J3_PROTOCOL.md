# Gate J3: Blind Empirical Jev Discrimination

Branch: research/jev-bridge-j3

## Research question

Can Jev's four-way Choice output carry a stable T/F/B/N evidence structure
that the scalar yes/no Noul output does not preserve?

J3 is the first gate allowed to count as empirical evidence about Jev. J1 and
J2 remain mathematical and synthetic controls.

## Frozen benchmark

data/jev_bridge_j3_frozen.jsonl contains 100 states:

- 25 expected T
- 25 expected F
- 25 expected B
- 25 expected N

There are 20 semantic base cases, five per FDE class. Each base case has five
semantically equivalent renderings, producing order, formatting, and wording
variants. The expected label is stored only for later evaluation and is never
included in the TypeSafe API request.

## One state, two Jev primitives

Every state is sent once to POST /v1/systemone with two questions:

1. fde_status: Choice over T/F/B/N.
2. claim_true: Noul yes/no truth probability.

The Choice probabilities are mapped through the J1 bridge:

P+ = pT + pB
P- = pF + pB

and thresholded at c = 0.75. The Noul value is the scalar baseline.

## Preregistered acceptance contract

J3 passes only if all of the following hold:

- complete benchmark coverage and at least 25 cases per T/F/B/N class;
- overall bridged accuracy >= 0.90;
- B/N bridged accuracy >= 0.90;
- false classical certainty on true B/N cases <= 0.05;
- mean within-base paraphrase stability >= 0.90;
- minimum within-base paraphrase stability >= 0.80;
- normalized B/N centroid separation in (P+, P-) is strictly greater than
  the B/N mean separation of the scalar Noul baseline.

These thresholds are frozen in PEL4/JevBridgeEmpiricalContract.lean.

## Blindness rule

The runner constructs each API payload from state only. It does not serialize
expected, base_id, or variant metadata into the request. Raw result JSONL also
omits expected labels. Evaluation joins results back to the frozen benchmark by
id only after collection.

## Local commands

Validate the benchmark:

    python scripts\jev_bridge_gate_j3.py validate data\jev_bridge_j3_frozen.jsonl

Inspect one blinded payload:

    python scripts\jev_bridge_gate_j3.py dry-run data\jev_bridge_j3_frozen.jsonl --case B01-v1

List Jev models available to the account:

    $env:TYPESAFE_API_KEY="..."
    python scripts\jev_bridge_gate_j3.py models

Run all 100 cases:

    python scripts\jev_bridge_gate_j3.py run data\jev_bridge_j3_frozen.jsonl data\jev_bridge_j3_results.jsonl --model jev-latest

The run is resumable. Existing case ids in the result file are skipped.

Evaluate only after collection is complete:

    python scripts\jev_bridge_gate_j3.py evaluate data\jev_bridge_j3_frozen.jsonl data\jev_bridge_j3_results.jsonl --summary data\jev_bridge_j3_summary.json

A passing preregistered result prints JEV_GATE_J3_EMPIRICAL_PASS. A failing
result prints JEV_GATE_J3_EMPIRICAL_FAIL and exits with status 2.

## Interpretation boundary

A pass supports the claim that Jev plus JevBridge preserves a practically
useful four-valued evidence distinction on this benchmark. It does not show
that Jev probabilities are literally identical to 4PEL world measures, and it
does not establish performance outside the tested evidence regimes.
