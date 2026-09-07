"""Audit the explicit manuscript claim inventory, exposing native evaluation.

Native dependencies are recognized by Lean 4.31's generated name marker, not
silently equated with standard logical axioms. This inventory is complementary
to (and does not relax) the strict MPFG checker. It is not an independent check
of the compiler's native computation.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "PEL4/PaperAxiomAudit.lean"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
LEGACY_NATIVE = {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
PATTERN = re.compile(
    r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]*)\])"
)


def native_dependency(name: str) -> bool:
    return name in LEGACY_NATIVE or bool(
        re.search(r"(?:^|\.)_native\.native_decide\.ax(?:_\d+)?$", name)
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
        native = {d for d in actual if native_dependency(d)}
        unexpected = actual - STANDARD - native
        if unexpected:
            raise ValueError(f"Unexpected assumptions for {name}: {sorted(unexpected)}")
        if name.startswith("PEL4.PaperReview.") and native:
            raise ValueError(f"Native evaluation forbidden for review lemmas: {name}")
        found[name] = {
            "declaration": name,
            "axioms": sorted(actual),
            "trust": "native-evaluation" if native else "standard-lean",
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
