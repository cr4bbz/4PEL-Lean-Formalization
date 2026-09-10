"""Build the manuscript and verify layout, metadata, and committed PDF content.

The committed-PDF comparison uses ordered ASCII word/identifier tokens.  This keeps
the freshness check stable across TeX/Poppler versions whose math-glyph extraction,
hyphenation, and page breaks differ, while still detecting stale prose or declaration
names.  It does not replace visual inspection. Use --check-committed in CI after
committing the new render.
"""

import argparse
from pathlib import Path
import re
import subprocess
import unicodedata

ROOT = Path(__file__).resolve().parents[1]


def manuscript_version() -> str:
    tex = (ROOT / "paper/main.tex").read_text(encoding="utf-8")
    readme = (ROOT / "paper/README.md").read_text(encoding="utf-8")
    tex_match = re.search(r"\\date\{Working manuscript, version ([^,}]+),", tex)
    readme_match = re.search(r"Current manuscript version: \*\*([^*]+)\*\*", readme)
    if tex_match is None or readme_match is None:
        raise ValueError("cannot read manuscript version metadata")
    tex_version = tex_match.group(1).strip()
    readme_version = readme_match.group(1).strip()
    if tex_version != readme_version:
        raise ValueError(
            f"manuscript version mismatch: main.tex={tex_version}, README={readme_version}"
        )
    return tex_version


def declared_page_count() -> int:
    readme = (ROOT / "paper/README.md").read_text(encoding="utf-8")
    match = re.search(
        r"Current manuscript version: \*\*[^*]+\*\*[^\n]*?,\s*(\d+) pages\.",
        readme,
    )
    if match is None:
        raise ValueError("cannot read manuscript page count from paper/README.md")
    return int(match.group(1))


def rendered_page_count(pdf: Path) -> int:
    output = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
    match = re.search(r"^Pages:\s+(\d+)\s*$", output, re.MULTILINE)
    if match is None:
        raise ValueError("cannot read rendered PDF page count")
    return int(match.group(1))


def pdf_text(pdf: bytes) -> str:
    text = subprocess.check_output(
        ["pdftotext", "-nopgbrk", "-enc", "UTF-8", "-", "-"], input=pdf
    ).decode("utf-8")
    normalized = unicodedata.normalize("NFKC", text)
    return " ".join(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", normalized)).casefold()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    committed = None
    if args.check_committed:
        committed = subprocess.check_output(["git", "show", "HEAD:paper/main.pdf"], cwd=ROOT)
    subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
        cwd=ROOT / "paper", check=True,
    )
    log = (ROOT / "paper/main.log").read_text(encoding="utf-8", errors="replace")
    errors = re.findall(
        r"^.*(?:Overfull \\[hv]box|LaTeX Warning:.*undefined|LaTeX Font Warning:|There were undefined references).*$",
        log, re.MULTILINE,
    )
    if errors:
        raise SystemExit("PAPER_FAILED\n" + "\n".join(errors))
    pdf_path = ROOT / "paper/main.pdf"
    generated = pdf_path.read_bytes()
    if committed is not None and pdf_text(committed) != pdf_text(generated):
        raise SystemExit("PAPER_FAILED committed PDF text differs from fresh render")
    try:
        version = manuscript_version()
        declared_pages = declared_page_count()
        rendered_pages = rendered_page_count(pdf_path)
    except ValueError as exc:
        raise SystemExit(f"PAPER_FAILED {exc}") from exc
    if declared_pages != rendered_pages:
        raise SystemExit(
            "PAPER_FAILED page count mismatch: "
            f"README={declared_pages}, rendered={rendered_pages}"
        )
    print(
        f"PAPER_RENDER_OK bytes={len(generated)} version={version} "
        f"pages={rendered_pages} committed_text_checked={committed is not None}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
