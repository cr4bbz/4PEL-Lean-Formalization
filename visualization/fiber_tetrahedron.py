from __future__ import annotations

import argparse
import math
from pathlib import Path

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection


VERTICES = [
    (0.0, 0.0, 0.0),
    (1.0, 0.0, 0.0),
    (0.5, math.sqrt(3) / 2.0, 0.0),
    (0.5, math.sqrt(3) / 6.0, math.sqrt(2.0 / 3.0)),
]
LABELS = ["u12", "u13", "u23", "u123"]


def barycentric_to_xyz(weights: tuple[float, float, float, float]) -> tuple[float, float, float]:
    return tuple(
        sum(weights[i] * VERTICES[i][axis] for i in range(4))
        for axis in range(3)
    )


def lattice_points(m: int) -> list[tuple[float, float, float]]:
    if m <= 0:
        return []
    points: list[tuple[float, float, float]] = []
    for x123 in range(m // 2 + 1):
        remaining = m - 2 * x123
        for x12 in range(remaining + 1):
            for x13 in range(remaining - x12 + 1):
                x23 = remaining - x12 - x13
                weights = (
                    x12 / m,
                    x13 / m,
                    x23 / m,
                    (2 * x123) / m,
                )
                points.append(barycentric_to_xyz(weights))
    return points


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Visualize the symmetric n=3 fixed-marginal fiber as a tetrahedron."
    )
    parser.add_argument("--m", type=int, default=6, help="integer scale of the fiber equation")
    parser.add_argument("--save", type=Path, help="save the figure instead of only showing it")
    args = parser.parse_args()

    if args.m <= 0:
        raise SystemExit("--m must be positive")

    fig = plt.figure(figsize=(8, 7))
    ax = fig.add_subplot(111, projection="3d")

    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for i, j in edges:
        ax.plot(
            [VERTICES[i][0], VERTICES[j][0]],
            [VERTICES[i][1], VERTICES[j][1]],
            [VERTICES[i][2], VERTICES[j][2]],
            linewidth=1.5,
        )

    faces = [
        [VERTICES[0], VERTICES[1], VERTICES[2]],
        [VERTICES[0], VERTICES[1], VERTICES[3]],
        [VERTICES[0], VERTICES[2], VERTICES[3]],
        [VERTICES[1], VERTICES[2], VERTICES[3]],
    ]
    ax.add_collection3d(Poly3DCollection(faces, alpha=0.08))

    points = lattice_points(args.m)
    if points:
        xs, ys, zs = zip(*points)
        ax.scatter(xs, ys, zs, s=22, alpha=0.8)

    for label, vertex in zip(LABELS, VERTICES):
        ax.text(vertex[0], vertex[1], vertex[2], f"  {label}")

    ax.set_title(
        "Symmetric fixed-marginal fiber\n"
        "u12 + u13 + u23 + u123 = 1"
    )
    ax.set_axis_off()

    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.save, bbox_inches="tight", dpi=180)
    else:
        plt.show()


if __name__ == "__main__":
    main()
