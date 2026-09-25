#!/usr/bin/env python3
"""Gate J3: blind empirical Jev -> 4PEL benchmark.

Uses only the Python standard library.

The benchmark contains expected labels, but API requests contain only each
case's state. Raw results omit expected labels. Evaluation joins by id later.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import statistics
import sys
import time
import urllib.error
import urllib.request
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

LABELS = ("T", "F", "B", "N")
DEFAULT_BASE_URL = "https://api.typesafe.ai"
DEFAULT_MODEL = "jev-latest"

FDE_CRITERIA = {
    "T": (
        "There is substantial credible evidence for the claim and no "
        "substantial credible evidence against it."
    ),
    "F": (
        "There is substantial credible evidence against the claim and no "
        "substantial credible evidence for it."
    ),
    "B": (
        "There is substantial credible evidence both for and against the claim, "
        "even if the evidence conflicts."
    ),
    "N": (
        "There is not substantial credible evidence either for or against the claim."
    ),
}

QUESTIONS = {
    "fde_status": {
        "type": "choice",
        "instructions": (
            "Classify the epistemic status of the claim using only the evidence "
            "in the state. Distinguish contradictory evidence from missing evidence."
        ),
        "criteria": FDE_CRITERIA,
    },
    "claim_true": {
        "type": "noul",
        "instructions": "Using only the supplied state, is the claim true?",
        "criteria": {
            "true": "The claim is true.",
            "false": "The claim is false.",
        },
    },
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{lineno}: {exc}") from exc
    return rows


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def validate_benchmark(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ids: set[str] = set()
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    counts: Counter[str] = Counter()

    for row in rows:
        missing = [
            key
            for key in ("id", "base_id", "variant", "expected", "state")
            if key not in row
        ]
        if missing:
            raise ValueError(f"benchmark row missing fields: {missing}")
        if row["id"] in ids:
            raise ValueError(f"duplicate benchmark id: {row['id']}")
        ids.add(row["id"])
        if row["expected"] not in LABELS:
            raise ValueError(f"{row['id']}: expected must be one of {LABELS}")
        if not isinstance(row["state"], str) or not row["state"].strip():
            raise ValueError(f"{row['id']}: state must be non-empty text")

        counts[row["expected"]] += 1
        groups[str(row["base_id"])].append(row)

    if len(rows) != 100:
        raise ValueError(f"expected exactly 100 frozen cases, found {len(rows)}")
    if any(counts[label] != 25 for label in LABELS):
        raise ValueError(f"expected 25 cases per class, got {dict(counts)}")
    if len(groups) != 20:
        raise ValueError(f"expected 20 base groups, found {len(groups)}")

    for base_id, items in groups.items():
        if len(items) != 5:
            raise ValueError(f"{base_id}: expected 5 variants, found {len(items)}")
        labels = {item["expected"] for item in items}
        if len(labels) != 1:
            raise ValueError(
                f"{base_id}: variants disagree on frozen label: {labels}"
            )
        variants = sorted(int(item["variant"]) for item in items)
        if variants != [1, 2, 3, 4, 5]:
            raise ValueError(
                f"{base_id}: variants must be 1..5, got {variants}"
            )

    return {
        "n": len(rows),
        "class_counts": dict(sorted(counts.items())),
        "base_groups": len(groups),
    }


def payload_for(row: dict[str, Any], model: str) -> dict[str, Any]:
    # Deliberately no expected label, base id, or variant metadata.
    return {
        "model": model,
        "state": row["state"],
        "questions": QUESTIONS,
    }


def api_request(
    method: str,
    path: str,
    *,
    api_key: str,
    base_url: str,
    payload: dict[str, Any] | None = None,
    timeout: float = 60.0,
) -> dict[str, Any]:
    url = base_url.rstrip("/") + path
    body = None if payload is None else json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        method=method,
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "4PEL-JevBridge-J3/1.0",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(
            f"TypeSafe API HTTP {exc.code}: {detail}"
        ) from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(
            f"TypeSafe API connection error: {exc}"
        ) from exc


def api_key_or_die() -> str:
    key = os.environ.get("TYPESAFE_API_KEY", "").strip()
    if not key:
        raise SystemExit(
            "TYPESAFE_API_KEY is not set. In PowerShell: "
            '$env:TYPESAFE_API_KEY="..."'
        )
    return key


def parse_result(
    case_id: str,
    response: dict[str, Any],
    benchmark_hash: str,
) -> dict[str, Any]:
    answers = response.get("answers", {})
    choice = answers.get("fde_status", {})
    noul = answers.get("claim_true", {})

    if choice.get("type") != "choice":
        raise ValueError(f"{case_id}: missing Choice answer")
    if noul.get("type") != "noul":
        raise ValueError(f"{case_id}: missing Noul answer")

    probs = choice.get("probabilities")
    if not isinstance(probs, dict) or any(label not in probs for label in LABELS):
        raise ValueError(
            f"{case_id}: Choice probabilities must contain T/F/B/N"
        )

    p = {label: float(probs[label]) for label in LABELS}
    if any(
        (not math.isfinite(value)) or value < 0.0 or value > 1.0
        for value in p.values()
    ):
        raise ValueError(f"{case_id}: invalid Choice probability: {p}")

    total = sum(p.values())
    if abs(total - 1.0) > 1e-3:
        raise ValueError(
            f"{case_id}: Choice probability total {total:.12f} is not near 1"
        )

    scalar = float(noul.get("noul"))
    if not math.isfinite(scalar) or not (0.0 <= scalar <= 1.0):
        raise ValueError(f"{case_id}: invalid Noul probability: {scalar}")

    usage = response.get("usage", {})
    return {
        "id": case_id,
        "benchmark_sha256": benchmark_hash,
        "model": response.get("model"),
        "choice": choice.get("choice"),
        "choice_confidence": choice.get("confidence"),
        "probabilities": p,
        "probability_total": total,
        "noul_true": scalar,
        "usage": {
            "input_tokens": usage.get("input_tokens"),
            "output_tokens": usage.get("output_tokens"),
        },
    }


def bridge_projection(
    result: dict[str, Any],
    threshold: float,
) -> tuple[str, float, float]:
    p = result["probabilities"]
    pos = float(p["T"]) + float(p["B"])
    neg = float(p["F"]) + float(p["B"])

    if pos >= threshold and neg >= threshold:
        label = "B"
    elif pos >= threshold:
        label = "T"
    elif neg >= threshold:
        label = "F"
    else:
        label = "N"

    return label, pos, neg


def centroid(points: list[tuple[float, float]]) -> tuple[float, float]:
    return (
        statistics.fmean(x for x, _ in points),
        statistics.fmean(y for _, y in points),
    )


def evaluate(
    benchmark: list[dict[str, Any]],
    results: list[dict[str, Any]],
    threshold: float,
) -> tuple[dict[str, Any], bool]:
    expected_by_id = {row["id"]: row for row in benchmark}
    result_by_id: dict[str, dict[str, Any]] = {}

    for result in results:
        rid = result.get("id")
        if rid in result_by_id:
            raise ValueError(f"duplicate result id: {rid}")
        result_by_id[rid] = result

    missing = sorted(set(expected_by_id) - set(result_by_id))
    extra = sorted(set(result_by_id) - set(expected_by_id))
    complete = (
        not missing
        and not extra
        and len(results) == len(benchmark)
    )

    joined = []
    for rid, row in expected_by_id.items():
        if rid not in result_by_id:
            continue

        result = result_by_id[rid]
        projected, pos, neg = bridge_projection(result, threshold)
        joined.append({
            "id": rid,
            "base_id": row["base_id"],
            "expected": row["expected"],
            "projected": projected,
            "pos": pos,
            "neg": neg,
            "noul_true": float(result["noul_true"]),
            "choice": result.get("choice"),
        })

    counts = Counter(item["expected"] for item in joined)

    overall = (
        sum(
            item["projected"] == item["expected"]
            for item in joined
        ) / len(joined)
        if joined
        else float("nan")
    )

    bn = [
        item
        for item in joined
        if item["expected"] in ("B", "N")
    ]
    bn_accuracy = (
        sum(
            item["projected"] == item["expected"]
            for item in bn
        ) / len(bn)
        if bn
        else float("nan")
    )
    bn_false_certainty = (
        sum(
            item["projected"] in ("T", "F")
            for item in bn
        ) / len(bn)
        if bn
        else float("nan")
    )

    by_base: dict[str, list[str]] = defaultdict(list)
    for item in joined:
        by_base[str(item["base_id"])].append(
            str(item["projected"])
        )

    stability_by_base: dict[str, float] = {}
    for base_id, labels in sorted(by_base.items()):
        most_common = Counter(labels).most_common(1)[0][1]
        stability_by_base[base_id] = most_common / len(labels)

    stability_mean = (
        statistics.fmean(stability_by_base.values())
        if stability_by_base
        else float("nan")
    )
    stability_min = (
        min(stability_by_base.values())
        if stability_by_base
        else float("nan")
    )

    b_points = [
        (item["pos"], item["neg"])
        for item in joined
        if item["expected"] == "B"
    ]
    n_points = [
        (item["pos"], item["neg"])
        for item in joined
        if item["expected"] == "N"
    ]

    if b_points and n_points:
        b_cent = centroid(b_points)
        n_cent = centroid(n_points)

        # Normalize Euclidean distance by the diagonal of [0,1]^2.
        sep4 = math.dist(b_cent, n_cent) / math.sqrt(2.0)

        b_scalar = statistics.fmean(
            item["noul_true"]
            for item in joined
            if item["expected"] == "B"
        )
        n_scalar = statistics.fmean(
            item["noul_true"]
            for item in joined
            if item["expected"] == "N"
        )
        sep_scalar = abs(b_scalar - n_scalar)
    else:
        b_cent = (float("nan"), float("nan"))
        n_cent = (float("nan"), float("nan"))
        sep4 = float("nan")
        sep_scalar = float("nan")
        b_scalar = float("nan")
        n_scalar = float("nan")

    direct_choice_accuracy = (
        sum(
            item["choice"] == item["expected"]
            for item in joined
        ) / len(joined)
        if joined
        else float("nan")
    )

    preregistered = {
        "required_per_class": 25,
        "min_overall_accuracy": 0.90,
        "min_bn_accuracy": 0.90,
        "max_bn_false_certainty": 0.05,
        "min_paraphrase_stability_mean": 0.90,
        "min_paraphrase_stability_min": 0.80,
        "require_bn_separation4_gt_scalar": True,
    }

    accepted = (
        complete
        and all(counts[label] >= 25 for label in LABELS)
        and overall >= 0.90
        and bn_accuracy >= 0.90
        and bn_false_certainty <= 0.05
        and stability_mean >= 0.90
        and stability_min >= 0.80
        and sep4 > sep_scalar
    )

    report = {
        "accepted": accepted,
        "complete": complete,
        "missing_ids": missing,
        "extra_ids": extra,
        "n_joined": len(joined),
        "class_counts": dict(sorted(counts.items())),
        "threshold": threshold,
        "overall_accuracy": overall,
        "direct_choice_accuracy": direct_choice_accuracy,
        "bn_accuracy": bn_accuracy,
        "bn_false_certainty_rate": bn_false_certainty,
        "paraphrase_stability_mean": stability_mean,
        "paraphrase_stability_min": stability_min,
        "paraphrase_stability_by_base": stability_by_base,
        "bn_centroid_B": b_cent,
        "bn_centroid_N": n_cent,
        "bn_separation4_normalized": sep4,
        "bn_noul_mean_B": b_scalar,
        "bn_noul_mean_N": n_scalar,
        "bn_separation_scalar": sep_scalar,
        "bn_separation_advantage": sep4 - sep_scalar,
        "preregistered_acceptance": preregistered,
    }
    return report, accepted


def command_validate(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.benchmark)
    summary = validate_benchmark(rows)
    summary["sha256"] = sha256_file(args.benchmark)
    print(json.dumps(summary, indent=2, sort_keys=True))
    print("JEV_GATE_J3_BENCHMARK_OK")
    return 0


def command_dry_run(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.benchmark)
    validate_benchmark(rows)

    selected = next(
        (row for row in rows if row["id"] == args.case),
        None,
    )
    if selected is None:
        raise SystemExit(f"Unknown case id: {args.case}")

    payload = payload_for(selected, args.model)
    print(json.dumps(payload, indent=2, sort_keys=True))
    print("JEV_GATE_J3_BLIND_PAYLOAD_OK")
    return 0


def command_models(args: argparse.Namespace) -> int:
    key = api_key_or_die()
    response = api_request(
        "GET",
        "/v1/models",
        api_key=key,
        base_url=args.base_url,
    )
    print(json.dumps(response, indent=2, sort_keys=True))
    return 0


def command_run(args: argparse.Namespace) -> int:
    key = api_key_or_die()
    rows = read_jsonl(args.benchmark)
    validate_benchmark(rows)
    benchmark_hash = sha256_file(args.benchmark)

    args.results.parent.mkdir(parents=True, exist_ok=True)

    existing: dict[str, dict[str, Any]] = {}
    if args.results.exists():
        for row in read_jsonl(args.results):
            if row.get("benchmark_sha256") != benchmark_hash:
                raise SystemExit(
                    "Existing result file was produced from "
                    "a different benchmark hash."
                )
            existing[str(row["id"])] = row

    pending = [
        row
        for row in rows
        if row["id"] not in existing
    ]
    if args.limit is not None:
        pending = pending[: args.limit]

    print(
        f"benchmark_sha256={benchmark_hash} "
        f"existing={len(existing)} "
        f"pending={len(pending)} "
        f"model={args.model}"
    )

    with args.results.open("a", encoding="utf-8") as out:
        for index, row in enumerate(pending, 1):
            payload = payload_for(row, args.model)
            response = api_request(
                "POST",
                "/v1/systemone",
                api_key=key,
                base_url=args.base_url,
                payload=payload,
                timeout=args.timeout,
            )
            parsed = parse_result(
                row["id"],
                response,
                benchmark_hash,
            )
            out.write(
                json.dumps(parsed, sort_keys=True) + "\n"
            )
            out.flush()

            print(
                f"[{index}/{len(pending)}] "
                f"{row['id']} "
                f"choice={parsed['choice']} "
                f"noul={parsed['noul_true']:.4f}"
            )

            if args.sleep > 0:
                time.sleep(args.sleep)

    print("JEV_GATE_J3_RUN_COMPLETE")
    return 0


def command_evaluate(args: argparse.Namespace) -> int:
    benchmark = read_jsonl(args.benchmark)
    validate_benchmark(benchmark)
    results = read_jsonl(args.results)

    benchmark_hash = sha256_file(args.benchmark)
    bad_hashes = sorted({
        str(row.get("benchmark_sha256"))
        for row in results
        if row.get("benchmark_sha256") != benchmark_hash
    })
    if bad_hashes:
        raise SystemExit(
            f"Result benchmark hash mismatch. "
            f"Expected {benchmark_hash}; got {bad_hashes}"
        )

    report, accepted = evaluate(
        benchmark,
        results,
        args.threshold,
    )
    report["benchmark_sha256"] = benchmark_hash

    print(json.dumps(report, indent=2, sort_keys=True))

    if args.summary is not None:
        write_json(args.summary, report)
        print(f"summary={args.summary}")

    if accepted:
        print("JEV_GATE_J3_EMPIRICAL_PASS")
        return 0

    print("JEV_GATE_J3_EMPIRICAL_FAIL")
    return 2


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(
        dest="command",
        required=True,
    )

    p = sub.add_parser(
        "validate",
        help="validate the frozen benchmark",
    )
    p.add_argument("benchmark", type=Path)
    p.set_defaults(func=command_validate)

    p = sub.add_parser(
        "dry-run",
        help="print one blinded API payload",
    )
    p.add_argument("benchmark", type=Path)
    p.add_argument("--case", default="B01-v1")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.set_defaults(func=command_dry_run)

    p = sub.add_parser(
        "models",
        help="list models available to the API key",
    )
    p.add_argument(
        "--base-url",
        default=DEFAULT_BASE_URL,
    )
    p.set_defaults(func=command_models)

    p = sub.add_parser(
        "run",
        help="run blinded Jev requests",
    )
    p.add_argument("benchmark", type=Path)
    p.add_argument("results", type=Path)
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument(
        "--base-url",
        default=DEFAULT_BASE_URL,
    )
    p.add_argument(
        "--timeout",
        type=float,
        default=60.0,
    )
    p.add_argument(
        "--sleep",
        type=float,
        default=0.0,
    )
    p.add_argument(
        "--limit",
        type=int,
        default=None,
    )
    p.set_defaults(func=command_run)

    p = sub.add_parser(
        "evaluate",
        help="join frozen labels and evaluate the run",
    )
    p.add_argument("benchmark", type=Path)
    p.add_argument("results", type=Path)
    p.add_argument(
        "--threshold",
        type=float,
        default=0.75,
    )
    p.add_argument(
        "--summary",
        type=Path,
        default=None,
    )
    p.set_defaults(func=command_evaluate)

    return ap


def main() -> int:
    args = parser().parse_args()
    try:
        return int(args.func(args))
    except (ValueError, RuntimeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
