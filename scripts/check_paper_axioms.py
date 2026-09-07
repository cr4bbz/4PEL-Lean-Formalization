"""Reject nonstandard axioms in the explicit manuscript claim inventory.

This complements the strict MPFG audit. Native-decision axioms are forbidden,
including transitive dependencies through legacy helper lemmas.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "PEL4/PaperAxiomAudit.lean"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PATTERN = re.compile(
    r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]*)\])"
)


def audit_output(output: str, expected: list[str]) -> list[dict]:
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("Empty or duplicate audit inventory")
    found = {}
    for name, no_axioms, deps in PATTERN.findall(output):
        if name not in expected:
            continue
        if name in found:
            raise ValueError(f"Duplicate output for {name}")
        actual = set() if no_axioms else {d.strip() for d in deps.split(",") if d.strip()}
        unexpected = actual - STANDARD
        if unexpected:
            raise ValueError(f"Unexpected assumptions for {name}: {sorted(unexpected)}")
        found[name] = {
            "declaration": name,
            "axioms": sorted(actual),
            "trust": "standard-lean",
        }
    missing = set(expected) - found.keys()
    if missing:
        raise ValueError(f"Incomplete audit: {sorted(missing)}")
    return [found[name] for name in expected]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    expected = re.findall(r"^#print axioms (\S+)$", AUDIT.read_text(), re.MULTILINE)
    run = subprocess.run(["lake", "env", "lean", str(AUDIT)], cwd=ROOT,
                         capture_output=True, text=True, check=False)
    output = run.stdout + run.stderr
    print(output, end="")
    if run.returncode:
        return run.returncode
    try:
        rows = audit_output(output, expected)
    except ValueError as exc:
        print(f"PAPER_AXIOMS_FAILED {exc}")
        return 1
    native = sum(row["trust"] == "native-evaluation" for row in rows)
    print(f"PAPER_AXIOMS_OK declarations={len(rows)} standard={len(rows)-native} native={native}")
    if args.report:
        report = {
            "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "declarations": rows,
        }
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
