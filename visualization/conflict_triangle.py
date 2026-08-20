from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import Polygon


def parse_point(raw: list[str]) -> tuple[float, float, str]:
    q = float(raw[0])
    r = float(raw[1])
    label = raw[2]
    if not (0.0 <= r <= q <= 1.0):
        raise argparse.ArgumentTypeError("points must satisfy 0 <= r <= q <= 1")
    return q, r, label


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Visualize the latent-conflict triangle 0 <= r <= q <= 1."
    )
    parser.add_argument(
        "--point",
        action="append",
        nargs=3,
        metavar=("Q", "R", "LABEL"),
        default=[],
        help="add a labeled point satisfying 0 <= r <= q <= 1",
    )
    parser.add_argument("--save", type=Path, help="save the figure instead of only showing it")
    args = parser.parse_args()

    fig, ax = plt.subplots(figsize=(7, 7))

    vertices = [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0)]
    ax.add_patch(Polygon(vertices, closed=True, alpha=0.18))
    xs = [v[0] for v in vertices] + [vertices[0][0]]
    ys = [v[1] for v in vertices] + [vertices[0][1]]
    ax.plot(xs, ys, linewidth=2)

    labels = {
        (0.0, 0.0): "distributed-exclusive\n(0, 0)",
        (1.0, 0.0): "concentrated-exclusive\n(1, 0)",
        (1.0, 1.0): "fully redundant\n(1, 1)",
    }
    for (x, y), label in labels.items():
        ax.scatter([x], [y], s=55)
        ax.annotate(label, (x, y), xytext=(8, 8), textcoords="offset points")

    for raw in args.point:
        q, r, label = parse_point(raw)
        ax.scatter([q], [r], s=70)
        ax.annotate(label, (q, r), xytext=(7, -15), textcoords="offset points")

    ax.set_xlim(-0.05, 1.08)
    ax.set_ylim(-0.05, 1.08)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel("q  (conflict concentration)")
    ax.set_ylabel("r  (conflict redundancy)")
    ax.set_title("Latent-Conflict Triangle")
    ax.grid(alpha=0.2)

    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.save, bbox_inches="tight", dpi=180)
    else:
        plt.show()


if __name__ == "__main__":
    main()
