"""Verify the complete inventory of project-specific Lean axiom declarations."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

PROTOTYPE = {
    ("PEL4/ProductUpdate.lean", "product_mu_total"),
    ("PEL4/ProductUpdate.lean", "product_mu_empty"),
    ("PEL4/ProductTheorems.lean", "product_transitive_preservation"),
    ("PEL4/ProductTheorems.lean", "product_euclidean_preservation"),
}

CONVENIENCE = {
    ("PEL4/Paradoxes/Preface.lean", "preface_mu_total"),
    ("PEL4/Paradoxes/Preface.lean", "preface_mu_empty"),
    ("PEL4/Paradoxes/Preface.lean", "preface_c_gt_half"),
    ("PEL4/Paradoxes/Preface.lean", "preface_c_le_one"),
    ("PEL4/Paradoxes/PrefaceSigned.lean", "signedPrefaceMuTotal"),
    ("PEL4/Paradoxes/PrefaceSigned.lean", "signedPrefaceMuEmpty"),
    ("PEL4/Paradoxes/PrefaceSigned.lean", "signedPrefaceThresholdGtHalf"),
    ("PEL4/Paradoxes/PrefaceSigned.lean", "signedPrefaceThresholdLeOne"),
    ("PEL4/Paradoxes/SurpriseExamination.lean", "surprise_mu_total"),
    ("PEL4/Paradoxes/SurpriseExamination.lean", "surprise_mu_empty"),
    ("PEL4/Paradoxes/SurpriseExamination.lean", "surprise_c_gt_half"),
    ("PEL4/Paradoxes/SurpriseExamination.lean", "surprise_c_le_one"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "agg_mu_total"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "agg_mu_empty"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "agg_c_gt_half"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "agg_c_le_one"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "conjGlut_mu_total"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "conjGlut_mu_empty"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "conjGlut_c_gt_half"),
    ("PEL4/Paradoxes/SyntheseExtensions.lean", "conjGlut_c_le_one"),
}

DECLARATION = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)


def source_inventory() -> set[tuple[str, str]]:
    found = set()
    for path in ROOT.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        relative = path.relative_to(ROOT).as_posix()
        for name in DECLARATION.findall(path.read_text(encoding="utf-8")):
            found.add((relative, name))
    return found


def main() -> int:
    expected = PROTOTYPE | CONVENIENCE
    actual = source_inventory()
    missing = sorted(expected - actual)
    unexpected = sorted(actual - expected)
    if missing or unexpected:
        details = []
        if missing:
            details.append(f"missing={missing}")
        if unexpected:
            details.append(f"unexpected={unexpected}")
        raise SystemExit("PROJECT_AXIOMS_FAILED " + " ".join(details))
    print(
        "PROJECT_AXIOMS_OK "
        f"declarations={len(actual)} prototype={len(PROTOTYPE)} "
        f"convenience={len(CONVENIENCE)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
