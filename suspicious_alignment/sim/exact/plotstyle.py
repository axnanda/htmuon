"""Shared matplotlib style: optimizer family -> hue, family member -> dash pattern (never colour alone).

Palette: reference categorical slots 1-3 (blue, orange, aqua; validated all-pairs for CVD / normal vision on
the light surface) + primary ink for the SGD baseline.  The aqua slot is below 3:1 contrast on the surface,
so every figure carries a legend and every plotted number is also in a table of the note.
"""
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURFACE, INK, INK2, MUTED, GRID, AXIS = "#fcfcfb", "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7"
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"
BLUE_RAMP = ["#86b6ef", "#5598e7", "#2a78d6", "#1c5cab", "#104281", "#0d366b"]      # ordinal (light -> dark)

OPT_STYLE = {
    "sgd": dict(color=INK, ls="-", label="SGD (f = s)"),
    "muon": dict(color=BLUE, ls="-", label="Muon (f = 1)"),
    "ht0.125": dict(color=ORANGE, ls="-", label="HTMuon p = 0.125"),
    "ht0.25": dict(color=ORANGE, ls="--", label="HTMuon p = 0.25"),
    "ht0.5": dict(color=ORANGE, ls=":", label="HTMuon p = 0.5"),
    "ech1": dict(color=AQUA, ls=":", label="Echelon r = 1"),
    "ech10": dict(color=AQUA, ls="-.", label="Echelon r = k/2"),
    "ech20": dict(color=AQUA, ls="-", label="Echelon r = k"),
    "ech40": dict(color=AQUA, ls="--", label="Echelon r = 2k"),
}
OPT_MARK = {"sgd": "o", "muon": "s", "ht0.125": "^", "ht0.25": "v", "ht0.5": "D", "ech1": "P", "ech10": "X",
            "ech20": "h", "ech40": "*"}


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


def line(ax, x, y, opt, **kw):
    st = OPT_STYLE[opt]
    kw.setdefault("label", st["label"])
    return ax.plot(x, y, color=st["color"], ls=st["ls"], **kw)


def pts(ax, x, y, opt, yerr=None, **kw):
    st = OPT_STYLE[opt]
    kw.setdefault("label", st["label"])
    return ax.errorbar(x, y, yerr=yerr, color=st["color"], ls=st["ls"], marker=OPT_MARK[opt], mec=SURFACE, mew=1.0,
                       capsize=2, elinewidth=1, **kw)


def legend_below(fig, ax, ncol=5, y=-0.02):
    h, l = ax.get_legend_handles_labels()
    fig.legend(h, l, loc="upper center", bbox_to_anchor=(0.5, y), ncol=ncol, handlelength=3.2)
