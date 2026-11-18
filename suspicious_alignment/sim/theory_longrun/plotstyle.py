"""Matplotlib style shared by make_figures.py (same convention as sim/exact/plotstyle.py):
optimizer family -> hue (SGD: ink, Muon: blue, HTMuon: orange, Echelon: aqua), family member -> dash
pattern / marker (never colour alone).  The three hues are the reference categorical slots 1-3
(validated all-pairs for CVD and normal vision on the light surface with dataviz/validate_palette.js;
aqua is below 3:1 contrast, so every figure has a legend and every plotted number is in a table of the
note).  Ordinal series (the gap m) use a single-hue light -> dark ramp."""
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURFACE, INK, INK2, MUTED, GRID, AXIS = "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7"
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
BLUE_RAMP = ["#86b6ef", "#5598e7", "#2a78d6", "#1c5cab", "#104281", "#0d366b"]


def setup():
    plt.rcParams.update({
        "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
        "font.family": "sans-serif", "font.size": 9.5, "axes.titlesize": 10.5, "axes.labelsize": 9.5,
        "axes.edgecolor": AXIS, "axes.labelcolor": INK2, "axes.titlecolor": INK, "text.color": INK,
        "xtick.color": MUTED, "ytick.color": MUTED, "xtick.labelcolor": INK2, "ytick.labelcolor": INK2,
        "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8, "grid.linestyle": "-",
        "axes.spines.top": False, "axes.spines.right": False, "axes.axisbelow": True,
        "lines.linewidth": 2.0, "lines.solid_capstyle": "round", "lines.markersize": 6.5,
        "legend.frameon": False, "legend.fontsize": 8.5, "figure.dpi": 130, "savefig.dpi": 130,
        "savefig.bbox": "tight",
    })
    return plt


def mk(color, marker):
    """marker kwargs with a surface ring (overlapping marks stay separable)."""
    return dict(color=color, marker=marker, mec=SURFACE, mew=1.0, ls="none")
