from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "papers" / "epistemic-dynamics"
MAIN = PAPER / "main.tex"

INPUT_RE = re.compile(r"\\input\{([^}]+)\}")


def tex_path(parent: Path, raw: str) -> Path:
    path = Path(raw)
    if path.suffix != ".tex":
        path = path.with_suffix(".tex")
    return (parent / path).resolve()


def collect_inputs(path: Path, seen: set[Path]) -> list[Path]:
    path = path.resolve()
    if path in seen:
        return []
    seen.add(path)
    text = path.read_text(encoding="utf-8")
    found: list[Path] = []
    for raw in INPUT_RE.findall(text):
        child = tex_path(path.parent, raw)
        # main.tex inputs are relative to the paper root; nested section wrappers
        # also use paper-root paths such as sections/02a_recovery_loops.
        if not child.exists():
            child = tex_path(PAPER, raw)
        if not child.exists():
            raise SystemExit(f"missing LaTeX input: {raw} referenced from {path.relative_to(ROOT)}")
        found.append(child)
        found.extend(collect_inputs(child, seen))
    return found


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise SystemExit(f"missing required {label}: {needle}")


def forbid(text: str, needle: str, label: str) -> None:
    if needle in text:
        raise SystemExit(f"stale {label} remains: {needle}")


def main() -> None:
    if not MAIN.exists():
        raise SystemExit(f"paper main file not found: {MAIN}")

    seen: set[Path] = set()
    collect_inputs(MAIN, seen)

    main_text = MAIN.read_text(encoding="utf-8")
    require(main_text, "Research Paper v0.4.0", "paper version")
    require(main_text, "research/noisy-identification-gate116", "Gate-116 formalization base")
    require(main_text, "875ed5d3850271927fdffe983ca4eca48af9cfed", "Gate-116 source commit")
    require(main_text, "sections/08_noisy_epistemic_control", "Gate-116 paper section")
    require(main_text, "appendix/formal_result_map_and_verification", "formal-result appendix")
    forbid(main_text, "Research Paper v0.3.0", "paper version")
    forbid(main_text, "research/epistemic-self-trust-integration-gate104", "Gate-104 snapshot")

    section05 = (PAPER / "sections" / "05_model_criticism_and_self_trust.tex").read_text(encoding="utf-8")
    for stale in ("\\frac9{17}", "\\frac8{17}", "actFragile", "expandModelClass"):
        forbid(section05, stale, "pre-audit Gate-95/104 wording")
    require(section05, "\\frac13", "Gate-95 corrected posterior")
    require(section05, "\\frac23", "Gate-95 corrected posterior")
    require(section05, "\\mathsf{reconcileModel}", "Gate-104 action")

    audit = PAPER / "editorial" / "GATES_095_116_SOURCE_AUDIT.md"
    matrix = PAPER / "editorial" / "CLAIM_THEOREM_MATRIX_v0.4.0.md"
    for required in (audit, matrix):
        if not required.exists():
            raise SystemExit(f"missing editorial contract: {required.relative_to(ROOT)}")

    print(f"EPIS_DYNAMICS_PAPER_OK tex_files={len(seen)} version=v0.4.0 gate=116")


if __name__ == "__main__":
    main()
