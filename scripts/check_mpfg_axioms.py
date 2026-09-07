"""Compile MPFG-1's focused audit and reject undeclared proof assumptions."""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "PEL4/ModalProbability/AxiomAudit.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    expected = re.findall(r"^#print axioms (\S+)$", AUDIT.read_text(), re.MULTILINE)
    run = subprocess.run(
        ["lake", "env", "lean", str(AUDIT)], cwd=ROOT,
        capture_output=True, text=True, check=False,
    )
    output = run.stdout + run.stderr
    print(output, end="")
    if run.returncode:
        return run.returncode
    checked = set()
    for name, no_axioms, deps in re.findall(
        r"'([^']+)'\s+(?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]*)\])",
        output,
    ):
        if name not in expected:
            continue
        actual = set() if no_axioms else {s.strip() for s in deps.split(",") if s.strip()}
        if actual - ALLOWED:
            print(f"Unexpected assumptions for {name}: {sorted(actual - ALLOWED)}", file=sys.stderr)
            return 1
        checked.add(name)
    missing = set(expected) - checked
    if not expected or missing:
        print(f"Incomplete audit: missing {sorted(missing)}", file=sys.stderr)
        return 1
    print(f"MPFG_AXIOMS_OK declarations={len(checked)} allowed={sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
