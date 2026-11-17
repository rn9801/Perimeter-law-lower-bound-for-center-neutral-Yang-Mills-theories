"""Generate the paper's four vector figures: python figures/generate_figures.py.

Requires NumPy and Matplotlib. Coordinates below are lattice coordinates;
the reflection maps act before the fixed oblique projection to the page.
"""
from pathlib import Path
import os
os.environ.setdefault("MPLCONFIGDIR", "/tmp/gluelump-matplotlib")
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
plt.rcParams.update({"font.family": "serif", "mathtext.fontset": "cm",
                     "font.size": 12, "pdf.fonttype": 42})
RED, BLUE, PALE, GRAY = "#b73535", "#246898", "#df9292", "#777777"
E = np.eye(3)
O = np.zeros(3)
N, M = 4, 4
X, Y = N * E[0], N * E[1]
PROJ = np.array([[1., -.78, 0.], [-.38, -.48, .85]])


def project(v):
    return np.asarray(v) @ PROJ.T


def line(ax, pts, color, lw=1.7, style="-", arrows=False):
    pts = project(pts)
    ax.plot(*pts.T, color=color, lw=lw, ls=style, solid_capstyle="round")
    if arrows:
        for a, b in zip(pts[:-1], pts[1:]):
            d = b-a
            ax.annotate("", xy=a+.62*d, xytext=a+.38*d,
                        arrowprops=dict(arrowstyle="->", color=color, lw=lw,
                                        shrinkA=0, shrinkB=0, mutation_scale=11))


def label(ax, p, s, offset=(0, 0), **kw):
    q = project(p)
    ax.annotate(s, q, xytext=offset, textcoords="offset points", **kw)


def dot(ax, p, s=None, offset=(0, -15)):
    q = project(p)
    ax.plot(*q, "o", color="#222222", ms=3)
    if s:
        label(ax, p, s, offset, ha="center")


def comb_edges(base, short):
    """Union of the m loops: two rails and m+1 unit rungs."""
    return ([(base, base+M*E[2]), (base+short, base+short+M*E[2])]
            + [(base+t*E[2], base+short+t*E[2]) for t in range(M+1)])


def comb(ax, base, short, transform=lambda v: v):
    for a, b in comb_edges(base, short):
        line(ax, [transform(a), transform(b)], BLUE)


def frame(ax, anti=False):
    if anti:
        a, b = X+.45*(E[0]-E[1]), Y+.45*(E[1]-E[0])
    else:
        a, b = -.35*(E[0]+E[1]), 2.15*(E[0]+E[1])
    line(ax, [a, b, b+4.6*E[2], a+4.6*E[2], a], GRAY, 1, "--")


def axes_key(ax, base):
    for e, s in zip(E, (r"$e_1$", r"$e_2$", r"$e_3$")):
        line(ax, [base, base+.65*e], GRAY, 1, arrows=True)
        label(ax, base+.80*e, s, ha="center", va="center", fontsize=10)


def setup(ax, title, xlim=(-4.2, 4.8), ylim=(-3.8, 4.8)):
    ax.set_aspect("equal")
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.axis("off")
    ax.set_title(title, fontsize=13, pad=8)


def save(fig, name):
    if name.startswith("reflection_"):
        # Multi-panel figures are reduced to manuscript text width.
        for text in fig.findobj(matplotlib.text.Text):
            text.set_fontsize(text.get_fontsize() * 1.35)
    fig.savefig(OUT/f"{name}_audited.pdf", bbox_inches="tight", pad_inches=.10)
    fig.savefig(OUT/f"{name}_audited.png", dpi=160, bbox_inches="tight", pad_inches=.10)
    plt.close(fig)


# 1. Each panel uses exactly the same strip; pale edges are context only.
fig, axs = plt.subplots(4, 1, figsize=(8, 6.2))
for k, ax in enumerate(axs, 1):
    for t in (0, 1):
        ax.plot([0, 4], [t, t], color="#dddddd", lw=1)
    for t in range(5):
        ax.plot([t, t], [0, 1], color="#dddddd", lw=1)
    pts = np.array([[0, 0], [k, 0], [k, 1], [0, 1], [0, 0]])
    ax.plot(*pts.T, color=BLUE, lw=1.8)
    ax.plot([k, k], [0, 1], color=RED, lw=2.3)
    for a, b in zip(pts[:-1], pts[1:]):
        ax.annotate("", xy=a+.64*(b-a), xytext=a+.36*(b-a),
                    arrowprops=dict(arrowstyle="->", color=RED if a[0]==b[0]==k else BLUE,
                                    lw=1.6, mutation_scale=12))
    ax.plot(0, 0, "ko", ms=3)
    ax.text(-.15, -.07, "$x$", ha="right", va="top")
    ax.text(-.6, .5, rf"$\ell_{k}$", va="center", fontsize=16)
    ax.text(k+.1, .5, rf"$b_{k}$", color=RED, va="center")
    ax.set(xlim=(-.9, 5.6), ylim=(-.35, 1.4), aspect="equal")
    ax.axis("off")
axs[0].annotate("", xy=(5.25,.95), xytext=(4.65,.95),
                arrowprops=dict(arrowstyle="->", color=GRAY))
axs[0].text(4.95, 1.1, "$e_i$", ha="center")
axs[0].annotate("", xy=(4.65,.95), xytext=(4.65,.35),
                arrowprops=dict(arrowstyle="->", color=GRAY))
axs[0].text(4.82, .48, "$e_j$")
fig.subplots_adjust(hspace=.10)
save(fig, "comb")

# 2. Transverse endpoint combs, both with long +e3 and short +e2.
fig, ax = plt.subplots(figsize=(7, 4.6))
setup(ax, "", xlim=(-1.9, 5.1), ylim=(-3., 4.2))
comb(ax, O, E[1]); comb(ax, X, E[1])
line(ax, [O, X], RED, 2.3, arrows=True)
dot(ax, O, "$0$"); dot(ax, X, "$ne_1$")
label(ax, 2*E[2], r"$\Phi_0^{32}$", (-48, 0), ha="right", color=BLUE)
label(ax, X+2*E[2], r"$\Phi_{ne_1}^{32}$", (10, 0), color=BLUE)
label(ax, X/2, r"$\gamma$", (0, -18), color=RED)
axes_key(ax, np.array([.1, -1.1, 3.0]))
save(fig, "wilson_line")

# 3. Swap coordinates 1 and 2; the entire endpoint comb is reflected.
fig, axs = plt.subplots(1, 2, figsize=(12, 5.5))
for ax in axs:
    setup(ax, "")
    frame(ax)
axs[0].set_title(r"Half-space data: $z_1\geq z_2$")
comb(axs[0], X, E[1]); comb(axs[0], O, E[0])
line(axs[0], [O, X], RED, 2.2, arrows=True)
dot(axs[0], O, "$0$"); dot(axs[0], X, "$x=ne_1$")
label(axs[0], X+3*E[2], r"$\Phi_x^{32}$", (10, 0), color=BLUE)
label(axs[0], 3*E[2], r"$\Phi_0^{31}$", (-10, 0), ha="right", color=BLUE)
axs[1].set_title(r"Gluing $B_P(f,f)$")
comb(axs[1], X, E[1]); comb(axs[1], Y, E[0])
line(axs[1], [X, O, Y], RED, 2.2, arrows=True)
for p, s in [(O, "$0$"), (X, "$x$"), (Y, "$y=ne_2$")]:
    dot(axs[1], p, s)
label(axs[1], X+3*E[2], r"$\Phi_x^{32}$", (10, 0), color=BLUE)
label(axs[1], Y+3*E[2], r"$\Phi_y^{31}$", (-10, 0), ha="right", color=BLUE)
for ax in axs:
    ax.text(.5, .04, r"$P:\ z_1=z_2$", transform=ax.transAxes, ha="center", color=GRAY)
axes_key(axs[0], np.array([2.3, -1., 4.6]))
fig.subplots_adjust(wspace=.14)
save(fig, "reflection_L")

# 4. Anti-diagonal map fixes x,y and sends 0 to (n,n,0).
anti = lambda v: np.array([N-v[1], N-v[0], v[2]])
fig, axs = plt.subplots(1, 3, figsize=(14, 5))
for ax, title in zip(axs, ["Reflected endpoint combs", "Closing the square", "Rectangle comparison"]):
    setup(ax, title, ylim=(-5.5, 4.4))
for ax in axs[:2]:
    frame(ax, anti=True)
    ax.text(.5, .03, r"$P:\ z_1+z_2=n$", transform=ax.transAxes, ha="center", color=GRAY)
comb(axs[0], X, E[1], anti); comb(axs[0], Y, E[0], anti)
line(axs[0], [X, O, Y], RED, 2.2, arrows=True)
for p, s in [(O, "$0$"), (X, "$x$"), (Y, "$y$")]:
    dot(axs[0], p, s)
label(axs[0], X+3*E[2], r"$-e_1$", (12, 0), color=BLUE)
label(axs[0], Y+3*E[2], r"$-e_2$", (-28, 0), ha="right", color=BLUE)
line(axs[1], [Y, O, X], RED, 2.2, arrows=True)
line(axs[1], [X, anti(O), Y], PALE, 2.2, arrows=True)
for p, s in [(O, "$0$"), (X, "$x$"), (Y, "$y$"), (anti(O), "$n(e_1+e_2)$")]:
    dot(axs[1], p, s)
axs[1].text(.5, .85, r"$\lambda_n^{-1}$ (red), $\Theta_P\lambda_n$ (pale)",
            transform=axs[1].transAxes, ha="center", fontsize=11)
# n=max(r,s): choose r=n=4, s=2, so one rectangle side equals n.
line(axs[2], [O, X, X+Y, Y, O], BLUE, 4.)
S = 2*E[1]
line(axs[2], [O, X, X+S, S, O], RED, 1.9, arrows=True)
dot(axs[2], O, "$0$")
label(axs[2], X/2, "$r=n$", (0, -18), color=RED)
label(axs[2], S/2, "$s$", (-14, 2), color=RED)
label(axs[2], Y/2, "$n$", (-15, 0), color=BLUE)
axs[2].text(.5, .83, r"$n=\max\{r,s\}$", transform=axs[2].transAxes, ha="center")
axs[2].text(.5, .08, r"$w_{r,s}\geq w_{n,n}$", transform=axs[2].transAxes, ha="center")
fig.subplots_adjust(wspace=.15)
save(fig, "reflection_square")

# Geometric checks guard the support conditions illustrated in the paper.
for b, short in [(X, E[1]), (O, E[0])]:
    assert all(v[0] >= v[1] for edge in comb_edges(b, short) for v in edge)
for b, short in [(X, E[1]), (Y, E[0])]:
    assert all(v[0]+v[1] >= N for edge in comb_edges(b, short) for v in edge)
    assert all(anti(v)[0]+anti(v)[1] <= N for edge in comb_edges(b, short) for v in edge)
assert np.allclose(anti(X), X) and np.allclose(anti(Y), Y)
print("Wrote four PDF figures and PNG previews; lattice support checks passed.")
