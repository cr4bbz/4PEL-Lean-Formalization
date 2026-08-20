from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import Polygon


PRESETS = {
    "fiberA": {
        "j1": 3, "j2": 3, "j3": 3,
        "j12": 3, "j13": 0, "j23": 0, "j123": 0,
    },
    "fiberCycle": {
        "j1": 3, "j2": 3, "j3": 3,
        "j12": 1, "j13": 1, "j23": 1, "j123": 0,
    },
    "fiberB": {
        "j1": 3, "j2": 3, "j3": 3,
        "j12": 2, "j13": 1, "j23": 1, "j123": 1,
    },
}

POSITIONS = {
    1: (0.0, 0.0),
    2: (1.0, 0.0),
    3: (0.5, 0.86),
}


def validate(data: dict[str, int]) -> None:
    inequalities = [
        ("j12", "j1"), ("j12", "j2"),
        ("j13", "j1"), ("j13", "j3"),
        ("j23", "j2"), ("j23", "j3"),
        ("j123", "j12"), ("j123", "j13"), ("j123", "j23"),
    ]
    for smaller_mass, larger_mass in inequalities:
        if data[smaller_mass] > data[larger_mass]:
            raise ValueError(
                f"invalid co-conflict hierarchy: {smaller_mass}={data[smaller_mass]} "
                f"must not exceed {larger_mass}={data[larger_mass]}"
            )


def euler_at_threshold(data: dict[str, int], threshold: int) -> int:
    vertices = sum(data[f"j{i}"] >= threshold for i in (1, 2, 3))
    edges = sum(data[key] >= threshold for key in ("j12", "j13", "j23"))
    face = int(data["j123"] >= threshold)
    return vertices - edges + face


def draw_nerve(ax, name: str, data: dict[str, int], threshold: int) -> None:
    validate(data)

    if data["j123"] >= threshold:
        ax.add_patch(
            Polygon([POSITIONS[1], POSITIONS[2], POSITIONS[3]], closed=True, alpha=0.16)
        )

    edge_data = [
        (1, 2, "j12"),
        (1, 3, "j13"),
        (2, 3, "j23"),
    ]
    for i, j, key in edge_data:
        if data[key] >= threshold:
            xi, yi = POSITIONS[i]
            xj, yj = POSITIONS[j]
            ax.plot([xi, xj], [yi, yj], linewidth=2.5)
            ax.text(
                (xi + xj) / 2,
                (yi + yj) / 2,
                f"{key}={data[key]}",
                ha="center",
                va="center",
            )

    for i in (1, 2, 3):
        key = f"j{i}"
        if data[key] >= threshold:
            x, y = POSITIONS[i]
            ax.scatter([x], [y], s=110, zorder=3)
            ax.text(x, y + 0.07, f"{i}: J={data[key]}", ha="center")

    if data["j123"] >= threshold:
        ax.text(0.5, 0.28, f"j123={data['j123']}", ha="center")

    chi = euler_at_threshold(data, threshold)
    ax.set_title(f"{name}   threshold={threshold}   chi={chi}")
    ax.set_xlim(-0.15, 1.15)
    ax.set_ylim(-0.15, 1.05)
    ax.set_aspect("equal", adjustable="box")
    ax.set_axis_off()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Visualize three-claim weighted conflict nerves from co-conflict masses."
    )
    parser.add_argument(
        "--preset",
        choices=["all", *PRESETS.keys()],
        default="all",
        help="which formalized profile to display",
    )
    parser.add_argument(
        "--threshold",
        type=int,
        default=1,
        help="raw co-conflict mass threshold; 1 gives the support nerve",
    )
    parser.add_argument("--save", type=Path, help="save the figure instead of only showing it")
    args = parser.parse_args()

    if args.threshold < 0:
        raise SystemExit("--threshold must be nonnegative")

    names = list(PRESETS) if args.preset == "all" else [args.preset]
    fig, axes = plt.subplots(1, len(names), figsize=(5 * len(names), 4.8), squeeze=False)

    for ax, name in zip(axes[0], names):
        draw_nerve(ax, name, PRESETS[name], args.threshold)

    fig.suptitle(
        "Conflict Nerve: identical first-order marginals, different higher-order support"
    )
    fig.tight_layout()

    if args.save:
        args.save.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(args.save, bbox_inches="tight", dpi=180)
    else:
        plt.show()


if __name__ == "__main__":
    main()
