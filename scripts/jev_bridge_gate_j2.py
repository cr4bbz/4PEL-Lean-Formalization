#!/usr/bin/env python3
"""Gate J2 empirical falsification harness for Jev -> 4PEL.

Input: JSON Lines with at least
  id, expected, t, f, b, n

Optional:
  chain, step

The harness never renormalizes malformed Jev outputs. Invalid simplex rows fail
the contract instead of being silently repaired.

Fixture mode checks the harness only.
Real mode applies the predeclared acceptance criteria.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path

LABELS = ("T", "F", "B", "N")


def validate_row(row: dict, tol: float) -> None:
    missing = [k for k in ("id", "expected", "t", "f", "b", "n") if k not in row]
    if missing:
        raise ValueError(f"{row.get('id', '<unknown>')}: missing {missing}")
    if row["expected"] not in LABELS:
        raise ValueError(f"{row['id']}: expected must be one of {LABELS}")
    xs = [float(row[k]) for k in ("t", "f", "b", "n")]
    if any((not math.isfinite(x)) or x < -tol for x in xs):
        raise ValueError(f"{row['id']}: non-finite or negative cell mass")
    if abs(sum(xs) - 1.0) > tol:
        raise ValueError(
            f"{row['id']}: simplex total {sum(xs):.12f} differs from 1 by "
            f"{abs(sum(xs)-1.0):.3g}"
        )


def support(row: dict) -> tuple[float, float]:
    return float(row["t"]) + float(row["b"]), float(row["f"]) + float(row["b"])


def project(row: dict, threshold: float) -> str:
    pos, neg = support(row)
    if pos >= threshold and neg >= threshold:
        return "B"
    if pos >= threshold and neg < threshold:
        return "T"
    if pos < threshold and neg >= threshold:
        return "F"
    return "N"


def scalar_balance(row: dict) -> float:
    pos, neg = support(row)
    denom = pos + neg
    return 0.5 if denom == 0.0 else pos / denom


def centroid(rows: list[dict], label: str) -> tuple[float, float] | None:
    xs = [support(r) for r in rows if r["expected"] == label]
    if not xs:
        return None
    return statistics.fmean(x[0] for x in xs), statistics.fmean(x[1] for x in xs)


def scalar_mean(rows: list[dict], label: str) -> float | None:
    xs = [scalar_balance(r) for r in rows if r["expected"] == label]
    return None if not xs else statistics.fmean(xs)


def chain_metrics(rows: list[dict], threshold: float) -> tuple[int, int]:
    chains: dict[str, list[dict]] = defaultdict(list)
    for r in rows:
        if "chain" in r and "step" in r:
            chains[str(r["chain"])].append(r)

    checked = passed = 0
    for _, seq in chains.items():
        seq.sort(key=lambda r: int(r["step"]))
        expected = [r["expected"] for r in seq]
        predicted = [project(r, threshold) for r in seq]
        checked += 1
        passed += int(expected == predicted)
    return checked, passed


def load_jsonl(path: Path) -> list[dict]:
    rows = []
    with path.open("r", encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{lineno}: {exc}") from exc
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("data", type=Path)
    ap.add_argument("--mode", choices=("fixture", "real"), default="fixture")
    ap.add_argument("--threshold", type=float, default=0.75)
    ap.add_argument("--simplex-tol", type=float, default=1e-9)
    ap.add_argument("--min-per-class", type=int, default=25)
    ap.add_argument("--min-overall-accuracy", type=float, default=0.90)
    ap.add_argument("--min-bn-accuracy", type=float, default=0.90)
    ap.add_argument("--max-bn-false-certainty", type=float, default=0.05)
    args = ap.parse_args()

    rows = load_jsonl(args.data)
    if not rows:
        raise SystemExit("No data rows.")

    for row in rows:
        validate_row(row, args.simplex_tol)
        row["predicted"] = project(row, args.threshold)

    counts = Counter(r["expected"] for r in rows)
    correct = sum(r["predicted"] == r["expected"] for r in rows)
    overall = correct / len(rows)

    bn = [r for r in rows if r["expected"] in ("B", "N")]
    bn_accuracy = (
        sum(r["predicted"] == r["expected"] for r in bn) / len(bn)
        if bn else float("nan")
    )
    bn_false_certainty = (
        sum(r["predicted"] in ("T", "F") for r in bn) / len(bn)
        if bn else float("nan")
    )

    b_cent = centroid(rows, "B")
    n_cent = centroid(rows, "N")
    if b_cent and n_cent:
        bn_distance_2d = math.dist(b_cent, n_cent)
        b_scalar = scalar_mean(rows, "B")
        n_scalar = scalar_mean(rows, "N")
        bn_distance_scalar = abs(b_scalar - n_scalar)
    else:
        bn_distance_2d = float("nan")
        bn_distance_scalar = float("nan")

    chains_checked, chains_passed = chain_metrics(rows, args.threshold)
    chain_rate = chains_passed / chains_checked if chains_checked else float("nan")

    report = {
        "mode": args.mode,
        "n": len(rows),
        "class_counts": dict(counts),
        "threshold": args.threshold,
        "overall_accuracy": overall,
        "bn_accuracy": bn_accuracy,
        "bn_false_certainty_rate": bn_false_certainty,
        "bn_centroid_distance_2d": bn_distance_2d,
        "bn_scalar_mean_distance": bn_distance_scalar,
        "chains_checked": chains_checked,
        "chain_pass_rate": chain_rate,
    }
    print(json.dumps(report, indent=2, sort_keys=True))

    if args.mode == "fixture":
        print("JEV_GATE_J2_HARNESS_OK")
        print("Fixture mode is a harness self-test, not empirical evidence.")
        return 0

    enough = all(counts[label] >= args.min_per_class for label in LABELS)
    chains_ok = chains_checked == 0 or chain_rate == 1.0
    accepted = (
        enough
        and overall >= args.min_overall_accuracy
        and bn_accuracy >= args.min_bn_accuracy
        and bn_false_certainty <= args.max_bn_false_certainty
        and chains_ok
    )

    if accepted:
        print("JEV_GATE_J2_EMPIRICAL_PASS")
        return 0

    print("JEV_GATE_J2_EMPIRICAL_FAIL")
    if not enough:
        print(
            "Reason: insufficient pre-labelled cases; need at least "
            f"{args.min_per_class} per T/F/B/N class."
        )
    return 2


if __name__ == "__main__":
    sys.exit(main())
