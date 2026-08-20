from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt


def hidden_freedom(n: int) -> int:
    return 2**n - n - 2


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Plot visible constraints against full and hidden conflict structure."
    )
    parser.add_argument("--max-n", type=int, default=12, help="largest arity to display")
    parser.add_argument("--save", type=Path, help="save the figure instead of only showing it")
    args = parser.parse_args()

    if args.max_n < 2:
        raise SystemExit("--max-n must be at least 2")

    ns = list(range(2, args.max_n + 1))
    visible = [n + 1 for n in ns]
    full = [2**n - 1 for n in ns]
    hidden = [hidden_freedom(n) for n in ns]

    fig, ax = plt.subplots(figsize=(9, 6))
    ax.plot(ns, visible, marker="o", label="carrier + marginals  n+1")
    ax.plot(ns, full, marker="o", label="nonempty incidence coordinates  2^n-1")
    ax.plot(ns, hidden, marker="o", label="hidden fiber freedom  2^n-n-2")

    for n, value in zip(ns, hidden):
        if n <= 6 or n == args.max_n:
            ax.annotate(str(value), (n, value), xytext=(5, 5), textcoords="offset points")

    ax.set_xlabel("number of claims n")
    ax.set_ylabel("count")
    ax.set_title("Growth of hidden conflict interaction freedom")
    ax.grid(alpha=0.2)
    ax.legend()

    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.save, bbox_inches="tight", dpi=180)
    else:
        plt.show()


if __name__ == "__main__":
    main()
