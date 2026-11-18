"""Shared matplotlib style: fixed-order categorical palette (validated default palette of the
dataviz guideline, light surface), recessive grid and axes, thin marks.  Reference curves
(exact filters) are drawn in primary ink (black); at most 8 coloured series per panel."""
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from cycler import cycler

PALETTE = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#008300', '#6250d6', '#e34948']
INK = '#0b0b0b'
INK2 = '#52514e'
MUTED = '#898781'
GRID = '#e1e0d9'
AXIS = '#c3c2b7'
SURFACE = '#fcfcfb'


def apply():
    plt.rcParams.update({
        'axes.prop_cycle': cycler(color=PALETTE),
        'figure.facecolor': SURFACE, 'axes.facecolor': SURFACE, 'savefig.facecolor': SURFACE,
        'axes.edgecolor': AXIS, 'axes.linewidth': 0.8,
        'axes.grid': True, 'grid.color': GRID, 'grid.linewidth': 0.6,
        'axes.spines.top': False, 'axes.spines.right': False,
        'xtick.color': MUTED, 'ytick.color': MUTED, 'xtick.labelcolor': INK2, 'ytick.labelcolor': INK2,
        'axes.labelcolor': INK2, 'axes.titlecolor': INK, 'text.color': INK,
        'axes.titlesize': 10, 'axes.labelsize': 9, 'xtick.labelsize': 8, 'ytick.labelsize': 8,
        'legend.fontsize': 7, 'legend.frameon': False,
        'lines.linewidth': 1.6, 'lines.markersize': 4,
        'font.size': 9, 'savefig.dpi': 130,
    })
