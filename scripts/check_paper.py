"""Build the manuscript, reject layout/reference errors, and detect stale PDF text.

Text comparison ignores PDF timestamps and whitespace, but does not replace
visual inspection. Use --check-committed in CI after committing the new render.
"""

import argparse
from pathlib import Path
import re
import subprocess
import unicodedata

ROOT = Path(__file__).resolve().parents[1]


def pdf_text(pdf: bytes) -> str:
    text = subprocess.check_output(
        ["pdftotext", "-nopgbrk", "-enc", "UTF-8", "-", "-"], input=pdf
    ).decode("utf-8")
    return " ".join(unicodedata.normalize("NFKC", text).split())


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
    log = (ROOT / "paper/main.log").read_text()
    errors = re.findall(
        r"^.*(?:Overfull \\[hv]box|LaTeX Warning:.*undefined|LaTeX Font Warning:|There were undefined references).*$",
        log, re.MULTILINE,
    )
    if errors:
        raise SystemExit("PAPER_FAILED\n" + "\n".join(errors))
    generated = (ROOT / "paper/main.pdf").read_bytes()
    if committed is not None and pdf_text(committed) != pdf_text(generated):
        raise SystemExit("PAPER_FAILED committed PDF text differs from fresh render")
    print(f"PAPER_RENDER_OK bytes={len(generated)} committed_text_checked={committed is not None}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
