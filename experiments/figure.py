"""Figure for experiments/probe.py: reconstruction error by rule and regime.

Panel (a) absolute RMSE; panel (b) excess over the per-position oracle.  Both
are read from probe_results.json, so the figure and the reported table cannot
drift apart.
"""
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

RULES = ["frozen scalar", "frozen table", "amortized net",
         "SURE scalar (Mode A)", "oracle profile (floor)"]
LABELS = ["frozen\nscalar", "frozen\ntable", "amortized\nnet",
          "SURE scalar\n(Mode A)", "oracle\nprofile"]
SHADES = ["0.35", "0.55", "0.72", "0.15", "0.90"]
HATCH = ["", "//", "\\\\", "", ".."]
REGIME_LABELS = {"id": "training\ndistribution", "ood_loc": "open set:\nunseen location",
                 "ood_width": "open set:\nunseen width", "ood_noise": "open set:\nunseen noise"}


def plot(results, outdir):
    os.makedirs(outdir, exist_ok=True)
    regimes = list(results["regimes"].keys())
    x = np.arange(len(regimes))
    width = 0.16

    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.9))
    handles = []
    for panel, (ax, key, title) in enumerate(
            zip(axes, ("rmse", "excess"),
                ("(a) reconstruction error", "(b) excess over the per-instance ideal"))):
        for j, (rule, lab, col, hat) in enumerate(zip(RULES, LABELS, SHADES, HATCH)):
            vals = [results["regimes"][r][rule][key] for r in regimes]
            b = ax.bar(x + (j - 2) * width, vals, width, label=lab.replace("\n", " "),
                       color=col, edgecolor="black", linewidth=0.4, hatch=hat)
            if panel == 0:
                handles.append(b)
        ax.set_xticks(x)
        ax.set_xticklabels([REGIME_LABELS[r] for r in regimes], fontsize=6)
        ax.set_title(title, fontsize=7)
        ax.tick_params(labelsize=6)
        ax.grid(axis="y", linewidth=0.3, alpha=0.4)
        ax.set_axisbelow(True)
        ax.set_ylim(0, ax.get_ylim()[1] * 1.02)
        ax.set_ylabel("RMSE" if key == "rmse" else "excess RMSE", fontsize=7)
    fig.legend(handles, [lab.replace("\n", " ") for lab in LABELS], fontsize=6,
               frameon=False, ncol=5, loc="lower center", bbox_to_anchor=(0.5, 0.0))
    fig.tight_layout(pad=0.4, rect=(0, 0.13, 1, 1))
    path = os.path.join(outdir, "probe.pdf")
    fig.savefig(path, metadata={"CreationDate": None})
    plt.close(fig)
    return path
